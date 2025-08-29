use std::io::{self, Write};

use crate::{
    compress::{
        bitstream::{self, Symbol},
        matchfinder::MatchFinder,
        BitWriter, Flush,
    },
    tables::{DIST_SYM_TO_DIST_EXTRA, LENGTH_TO_SYMBOL, LEN_SYM_TO_LEN_EXTRA},
};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct Slot {
    length: u16,
    distance: u16,
    cost: u32,
}
impl Default for Slot {
    fn default() -> Self {
        Self {
            length: 0,
            distance: 0,
            cost: u32::MAX / 2,
        }
    }
}

pub(crate) struct DynamicProgrammingParser<M> {
    match_finder: M,
    skip_ahead_shift: u8,

    // symbols: Vec<Symbol>,

    // ip: usize,
    // last_match: usize,
    // m: Match,
    last_index: u32,

    costs: [u8; 286],
    dist_costs: [u8; 30],
    slots: Vec<Slot>,
}

impl<M: MatchFinder> DynamicProgrammingParser<M> {
    pub fn new(skip_ahead_shift: u8, match_finder: M) -> Self {
        Self {
            match_finder,
            skip_ahead_shift,
            // symbols: Vec::new(),
            // ip: 0,
            // last_match: 0,
            // m: Match::empty(),
            last_index: 0,

            costs: [0; 286],
            dist_costs: [0; 30],
            slots: Vec::new(),
        }
    }

    pub fn reset_indices(&mut self, old_base_index: u32) {
        self.last_index -= old_base_index;
        self.match_finder.reset_indices(old_base_index);
    }

    fn store_literal_cost(&mut self, block_start: usize, index: usize, byte: u8) {
        let index = index - block_start;

        let cost = u32::from(self.costs[byte as usize]) + self.slots[index].cost;
        if self.slots[index + 1].cost > cost {
            self.slots[index + 1].cost = cost;
            self.slots[index + 1].length = 1;
            self.slots[index + 1].distance = 0;
        }
    }

    fn store_match_cost(&mut self, block_start: usize, index: usize, length: u16, distance: u16) {
        let index = index - block_start;

        assert!(self.slots[index].cost < u32::MAX / 2);

        let dist_cost =
            u32::from(self.dist_costs[bitstream::distance_to_dist_sym(distance) as usize]);
        let len_cost = u32::from(self.costs[LENGTH_TO_SYMBOL[length as usize - 3] as usize]);
        let cost = dist_cost + len_cost + self.slots[index].cost;
        if self.slots[index + length as usize].cost > cost {
            self.slots[index + length as usize].cost = cost;
            self.slots[index + length as usize].length = length;
            self.slots[index + length as usize].distance = distance;
        }
    }

    /// Compress the data using a greedy algorithm.
    pub fn compress<W: Write>(
        &mut self,
        writer: &mut BitWriter<W>,
        data: &[u8],
        base_index: u32,
        _start: usize,
        flush: Flush,
    ) -> io::Result<usize> {
        assert!(base_index as u64 + data.len() as u64 <= u32::MAX as u64);

        if flush == Flush::None {
            return Ok(0);
        }

        let mut symbols = Vec::new();

        // Measure the literal distribution in the first 4KB.
        let lookahead = data.len().min(4096);
        let mut lit_freqs = [[0u16; 256]; 4];
        for chunk in data[..lookahead].chunks_exact(4) {
            lit_freqs[0][chunk[0] as usize] += 1;
            lit_freqs[1][chunk[1] as usize] += 1;
            lit_freqs[2][chunk[2] as usize] += 1;
            lit_freqs[3][chunk[3] as usize] += 1;
        }
        for i in 0..256 {
            lit_freqs[0][i] += lit_freqs[1][i] + lit_freqs[2][i] + lit_freqs[3][i];
        }

        // Initialize costs based on measured literal frequencies and constant backref costs.
        self.costs = [15; 286];
        self.dist_costs = [10; 30];
        for (i, f) in lit_freqs[0].iter().enumerate() {
            if *f > 0 {
                self.costs[i] = (((*f) as f32 / lookahead as f32).log2() * -1.0)
                    .round()
                    .clamp(1.0, 15.0) as u8;
            }
        }
        for i in 257..286 {
            self.costs[i] = 6 + LEN_SYM_TO_LEN_EXTRA[i - 257];
        }
        self.costs[257] = 15;
        for i in 0..30 {
            self.dist_costs[i] = 5 + DIST_SYM_TO_DIST_EXTRA[i];
        }

        let mut first_block = true;

        const OPT_WINDOW: usize = 4096;

        // self.slots = vec![Slot::default(); OPT_WINDOW + 1];

        let mut i = 0;
        while i < data.len().saturating_sub(8) {
            self.slots = vec![Slot::default(); OPT_WINDOW + 1];
            self.slots[0].cost = 0;

            let block_start = i;
            let block_end = (i + OPT_WINDOW).min(data.len().saturating_sub(8));

            let mut high_water_mark = block_start + 1;
            while i < block_end
            /*&& i < high_water_mark*/
            {
                self.store_literal_cost(block_start, i, data[i]);

                let current = u64::from_le_bytes(data[i..][..8].try_into().unwrap());

                if i == 0 {
                    self.match_finder
                        .insert(data, base_index, current, i as u32);
                    i += 1;
                    continue;
                }

                if current as u32 == (current >> 8) as u32 {
                    if i + 4 >= block_end {
                        i += 1;
                        continue;
                    }

                    if i == 0 || data[i - 1] != data[i] {
                        i += 1;
                        self.store_literal_cost(block_start, i, data[i]);
                    }

                    // Find the match length.
                    let mut length = 3;
                    while i + length < block_end && data[i + length] == data[i] {
                        length += 1;
                    }

                    // Store the match cost.
                    self.store_match_cost(block_start, i, length.min(258) as u16, 1);

                    // Also store the costs of matches starting at future positions in the run.
                    for j in 1..=(length - 3) {
                        self.store_literal_cost(block_start, i + j, data[i + j]);
                        self.store_match_cost(block_start, i + j, (length - j).min(258) as u16, 1);
                    }

                    high_water_mark = high_water_mark.max(i + length);
                    i += length - 2;
                    continue;
                }

                let ms = self
                    .match_finder
                    .get_all_and_insert(data, base_index, i, i, current);

                if ms.is_empty() {
                    let skip_ahead = (i.saturating_sub(high_water_mark)) >> self.skip_ahead_shift;
                    if skip_ahead == 0 || i + skip_ahead >= block_end {
                        i += 1;
                        continue;
                    }

                    for j in 1..=skip_ahead {
                        self.store_literal_cost(block_start, i + j, data[i + j]);
                    }
                    i += 1 + skip_ahead;
                    continue;
                }

                let mut max_len = 3;
                for m in &ms {
                    while max_len <= m.length as usize && max_len <= 258 && i + max_len <= block_end
                    {
                        self.store_match_cost(block_start, i, max_len as u16, m.distance);
                        max_len += 1;
                    }
                }
                high_water_mark = high_water_mark
                    .max(i + ms.last().unwrap().length as usize)
                    .min(data.len());
                // if max_len > 128 {
                //     i += max_len - 32;
                // } else {
                i += 1;
                // }
                // }
            }

            // // Block may have ended early if we reached the high water mark.
            // let block_end = block_end.min(high_water_mark);

            let mut prev_index = block_end - block_start;
            let mut prev = self.slots[prev_index];
            loop {
                assert!(prev.cost < u32::MAX / 2);

                let new_prev_index = prev_index - prev.length as usize;
                let new_prev = self.slots[new_prev_index];

                self.slots[new_prev_index] = prev;
                prev_index = new_prev_index;
                prev = new_prev;

                if prev_index == 0 {
                    break;
                }
            }

            // And convert to symbols in the forward direction.
            let mut j = 0;
            let mut symbol_run = 0;
            while j + symbol_run < block_end - block_start {
                let m = &self.slots[j + symbol_run];
                assert!(m.length != 0);
                if m.length == 1 {
                    symbol_run += 1;
                } else {
                    assert!(m.distance > 0);
                    if symbol_run > 0 {
                        symbols.push(Symbol::LiteralRun {
                            start: (block_start + j) as u32,
                            end: (block_start + j + symbol_run) as u32,
                        });
                        j += symbol_run;
                        symbol_run = 0;
                    }
                    symbols.push(Symbol::Backref {
                        length: m.length,
                        distance: m.distance,
                        dist_sym: bitstream::distance_to_dist_sym(m.distance),
                    });
                    j += m.length as usize;

                    assert!(j as usize <= block_end);
                    if symbols.len() >= 16384 || (first_block && symbols.len() >= 1024) {
                        first_block = false;

                        let last_block = flush == Flush::Finish && j as usize == data.len();

                        let codes = bitstream::compute_block_codes(data, base_index, &symbols);

                        for i in 0..286 {
                            self.costs[i] = if codes.lengths[i] > 0 {
                                codes.lengths[i]
                            } else {
                                15
                            };
                            if i >= 257 {
                                self.costs[i] += LEN_SYM_TO_LEN_EXTRA[i - 257];
                            }
                        }
                        for i in 0..30 {
                            self.dist_costs[i] = if codes.dist_lengths[i] > 0 {
                                codes.dist_lengths[i]
                            } else {
                                15
                            };
                            self.dist_costs[i] += DIST_SYM_TO_DIST_EXTRA[i];
                        }

                        bitstream::write_block(writer, data, base_index, &symbols, last_block)?;
                        symbols.clear();
                    }
                }
            }
            if symbol_run > 0 {
                symbols.push(Symbol::LiteralRun {
                    start: (block_start + j) as u32,
                    end: (block_start + j + symbol_run) as u32,
                });
                j += symbol_run;
            }
            assert_eq!(block_start + j as usize, block_end);

            // self.slots[..=(high_water_mark - block_start).min(OPT_WINDOW)].fill(Slot::default());

            // for k in 0..OPT_WINDOW {
            //     assert_eq!(
            //         self.slots[k],
            //         Slot::default(),
            //         "k={k} start={} end={OPT_WINDOW}",
            //         high_water_mark - block_start,
            //     );
            // }

            // while symbols.len() > 16384 {
            //     let codes = bitstream::compute_block_codes(data, base_index, &symbols[..16384]);

            //     for i in 0..286 {
            //         self.costs[i] = if codes.lengths[i] > 0 {
            //             codes.lengths[i]
            //         } else {
            //             15
            //         };
            //         if i >= 257 {
            //             self.costs[i] += LEN_SYM_TO_LEN_EXTRA[i - 257];
            //         }
            //     }
            //     for i in 0..30 {
            //         self.dist_costs[i] = if codes.dist_lengths[i] > 0 {
            //             codes.dist_lengths[i]
            //         } else {
            //             15
            //         };
            //         self.dist_costs[i] += DIST_SYM_TO_DIST_EXTRA[i];
            //     }

            //     bitstream::write_block(writer, data, base_index, &symbols[..16384], false)?;
            //     symbols.drain(..16384);
            // }
        }

        if i < data.len() {
            symbols.push(Symbol::LiteralRun {
                start: i as u32,
                end: data.len() as u32,
            });
        }

        if !symbols.is_empty() {
            bitstream::write_block(writer, data, base_index, &symbols, true)?;
        }

        Ok(data.len())
    }
}
