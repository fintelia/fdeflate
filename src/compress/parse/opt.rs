use std::io::{self, Write};

use crate::{
    compress::{
        bitstream::{self, Symbol},
        matchfinder::{HashChainMatchFinder, MatchFinder},
        BitWriter, Flush,
    },
    tables::{DIST_SYM_TO_DIST_EXTRA, LENGTH_TO_SYMBOL, LEN_SYM_TO_LEN_EXTRA},
};

#[derive(Debug, Clone, Copy)]
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

    costs: [u32; 286],
    dist_costs: [u32; 30],
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

    fn store_literal_cost(&mut self, index: usize, byte: u8) {
        let cost = self.costs[byte as usize] + self.slots[index].cost;
        if self.slots[index + 1].cost > cost {
            self.slots[index + 1].cost = cost;
            self.slots[index + 1].length = 1;
            self.slots[index + 1].distance = 0;
        }
    }

    fn store_match_cost(&mut self, index: usize, length: u16, distance: u16) {
        assert!(self.slots[index].cost < u32::MAX / 2);

        let dist_cost = self.dist_costs[bitstream::distance_to_dist_sym(distance) as usize];
        let len_cost = self.costs[LENGTH_TO_SYMBOL[length as usize - 3] as usize];
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

        // let delta = base_index - self.last_index;
        // self.ip -= delta as usize;
        // self.last_match -= delta as usize;
        // if !self.m.is_empty() {
        //     self.m.start -= delta as usize;
        // }
        // self.last_index = base_index;

        // let mut last_block_end = start;

        // let max_ip = if flush == Flush::None {
        //     data.len().saturating_sub(258 + 8)
        // } else {
        //     data.len().saturating_sub(7)
        // };

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
                self.costs[i] = 1 + (((*f) as f32 / lookahead as f32).log2() * -1.0)
                    .round()
                    .clamp(0.0, 14.0) as u32;
            }
        }
        for i in 257..286 {
            self.costs[i] = 6 + LEN_SYM_TO_LEN_EXTRA[i - 257] as u32;
        }
        for i in 0..30 {
            self.dist_costs[i] = 5 + DIST_SYM_TO_DIST_EXTRA[i] as u32;
        }

        const OPT_WINDOW: usize = 4096;

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
                self.store_literal_cost(i - block_start, data[i]);

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
                        self.store_literal_cost(i - block_start, data[i]);
                    }

                    // Find the match length.
                    let mut length = 3;
                    while i + length < block_end && data[i + length] == data[i] {
                        length += 1;
                    }

                    // Store the match cost.
                    self.store_match_cost(i - block_start, length.min(258) as u16, 1);

                    // Also store the costs of matches starting at future positions in the run.
                    for j in 1..=(length - 3) {
                        self.store_literal_cost(i - block_start + j, data[i + j]);
                        self.store_match_cost(i - block_start + j, (length - j).min(258) as u16, 1);
                    }

                    high_water_mark = high_water_mark.max(i + length);
                    i += length - 2;
                    continue;
                }

                let ms = self
                    .match_finder
                    .get_all_and_insert(data, base_index, i, i, current);

                // let m = self
                //     .match_finder
                //     .get_and_insert(data, base_index, i, i, current);
                // let ms = if m.is_empty() { Vec::new() } else { vec![m] };

                if ms.is_empty() {
                    let skip_ahead = (i.saturating_sub(high_water_mark)) >> self.skip_ahead_shift;
                    if skip_ahead == 0 || i + skip_ahead >= block_end {
                        i += 1;
                        continue;
                    }

                    for j in 1..=skip_ahead {
                        self.store_literal_cost(i - block_start + j, data[i + j]);
                    }
                    i += 1 + skip_ahead;
                    continue;
                }

                let mut max_len = 3;
                for m in &ms {
                    while max_len <= m.length as usize && max_len <= 258 && i + max_len <= block_end
                    {
                        self.store_match_cost(i - block_start, max_len as u16, m.distance);
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

            // println!("block {}..{}:", block_start, high_water_mark);
            // println!("matches: {:#?}", &matches[..16]);

            // Backtrack to record the optimal path.
            // let mut j = high_water_mark - block_start;
            let mut prev_index = /*high_water_mark*/block_end - block_start;
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
            while j + symbol_run < /*high_water_mark*/block_end - block_start {
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
                    if symbols.len() >= 16384 {
                        let last_block = flush == Flush::Finish && j as usize == data.len();
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
            assert_eq!(
                block_start + j as usize,
                block_end /*.min(high_water_mark)*/
            );
        }

        if i < data.len() {
            symbols.push(Symbol::LiteralRun {
                start: i as u32,
                end: data.len() as u32,
            });
        }

        // let mut total_symbols = 0;
        // let mut total_backrefs = 0;
        // let mut frequencies = [0; 286];
        // let mut dist_frequencies = [0; 30];

        // frequencies[256] = 1; // EOF symbol

        // // Do a greedy pass to estimate the frequencies of symbols.
        // let mut i = 0;
        // while i < data.len() {
        //     if matches[i].length > 0 {
        //         frequencies[LENGTH_TO_SYMBOL[matches[i].length as usize - 3] as usize] += 1;
        //         dist_frequencies[bitstream::distance_to_dist_sym(matches[i].distance) as usize] +=
        //             1;
        //         i += matches[i].length as usize;
        //         total_backrefs += 1;
        //     } else {
        //         frequencies[data[i] as usize] += 1;
        //         i += 1;
        //     }
        //     total_symbols += 1;
        // }

        // for passes_left in (0..1).rev() {
        //     let mut costs = [15; 286];
        //     let mut dist_costs = [10; 30];
        //     for (i, f) in frequencies.iter().enumerate() {
        //         if *f > 0 {
        //             costs[i] = (((*f) as f32 / total_symbols as f32).log2() * -1.0)
        //                 .round()
        //                 .clamp(1.0, 15.0) as u32;
        //             if i >= 257 {
        //                 costs[i] += LEN_SYM_TO_LEN_EXTRA[i - 257] as u32;
        //             }
        //         }
        //     }
        //     for (i, f) in dist_frequencies.iter().enumerate() {
        //         if *f > 0 {
        //             dist_costs[i] = (((*f) as f32 / total_backrefs as f32).log2() * -1.0)
        //                 .round()
        //                 .clamp(1.0, 15.0) as u32
        //                 + DIST_SYM_TO_DIST_EXTRA[i] as u32;
        //         }
        //     }

        //     matches[data.len() - 1].cost = costs[data[data.len() - 1] as usize];
        //     for i in (0..matches.len() - 1).rev() {
        //         let lit_cost = costs[data[i] as usize] + matches[i + 1].cost;

        //         if matches[i].length == 0 {
        //             matches[i].cost = lit_cost;
        //             matches[i].chosen_length = 0;
        //         } else {
        //             let mut best_length = 0;
        //             let mut best_cost = lit_cost;
        //             let dist_cost =
        //                 dist_costs[bitstream::distance_to_dist_sym(matches[i].distance) as usize];

        //             for j in 3..=matches[i].length as usize {
        //                 let cost = dist_cost
        //                     + costs[LENGTH_TO_SYMBOL[j - 3] as usize]
        //                     + matches[i + j].cost;
        //                 if cost < best_cost {
        //                     best_length = j as u16;
        //                     best_cost = cost
        //                 }
        //             }

        //             matches[i].cost = best_cost;
        //             matches[i].chosen_length = best_length;
        //         }
        //     }

        //     if passes_left != 0 {
        //         total_symbols = 0;
        //         total_backrefs = 0;
        //         frequencies = [0; 286];
        //         dist_frequencies = [0; 30];

        //         frequencies[256] = 1; // EOF symbol

        //         let mut i = 0;
        //         while i < data.len() {
        //             let m = &matches[i];
        //             if m.chosen_length > 0 {
        //                 frequencies[LENGTH_TO_SYMBOL[m.chosen_length as usize - 3] as usize] += 1;
        //                 dist_frequencies[bitstream::distance_to_dist_sym(m.distance) as usize] += 1;
        //                 i += m.chosen_length as usize;
        //                 total_backrefs += 1;
        //             } else {
        //                 frequencies[data[i] as usize] += 1;
        //                 i += 1;
        //             }
        //             total_symbols += 1;
        //         }
        //     }
        // }

        // let mut i = 0;
        // let mut symbols = Vec::new();
        // let mut symbol_run = 0;
        // while i + symbol_run < data.len() {
        //     let m = &matches[i + symbol_run];
        //     if m.chosen_length == 0 {
        //         symbol_run += 1;
        //     } else {
        //         if symbol_run > 0 {
        //             symbols.push(Symbol::LiteralRun {
        //                 start: i as u32,
        //                 end: (i + symbol_run) as u32,
        //             });
        //             i += symbol_run;
        //             symbol_run = 0;
        //         }
        //         symbols.push(Symbol::Backref {
        //             length: m.chosen_length,
        //             distance: m.distance,
        //             dist_sym: bitstream::distance_to_dist_sym(m.distance),
        //         });
        //         i += m.chosen_length as usize;

        //         assert!(i as usize <= data.len());
        //         if symbols.len() >= 16384 {
        //             let last_block = flush == Flush::Finish && i as usize == data.len();
        //             bitstream::write_block(writer, data, base_index, &symbols, last_block)?;
        //             symbols.clear();
        //         }
        //     }
        // }

        // if symbol_run > 0 {
        //     symbols.push(Symbol::LiteralRun {
        //         start: i as u32,
        //         end: (i + symbol_run) as u32,
        //     });
        //     i += symbol_run;
        // }
        // assert_eq!(i as usize, data.len());

        if !symbols.is_empty() {
            bitstream::write_block(writer, data, base_index, &symbols, true)?;
        }

        Ok(data.len())
    }
}
