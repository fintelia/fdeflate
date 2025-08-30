use std::io::{self, Write};

use crate::{
    compress::{
        bitstream::{self, Symbol},
        matchfinder::MatchFinder,
        BitWriter, Flush,
    },
    tables::{DIST_SYM_TO_DIST_EXTRA, LENGTH_TO_SYMBOL, LEN_SYM_TO_LEN_EXTRA},
};

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
struct Slot {
    length: u8,
    distance: u16,

    length2: u8,
    distance2: u16,

    cost: u32,
    chosen_length: u16,
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
    initialized_costs: bool,

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

            costs: [9; 286],
            dist_costs: [6; 30],
            initialized_costs: false,
            slots: Vec::new(),
        }
    }

    pub fn reset_indices(&mut self, old_base_index: u32) {
        self.last_index -= old_base_index;
        self.match_finder.reset_indices(old_base_index);
    }

    // fn store_literal_cost(&mut self, block_start: usize, index: usize, byte: u8) {
    //     let index = index - block_start;

    //     let cost = u32::from(self.costs[byte as usize]) + self.slots[index].cost;
    //     if self.slots[index + 1].cost > cost {
    //         self.slots[index + 1].cost = cost;
    //         self.slots[index + 1].length = 1;
    //         self.slots[index + 1].distance = 0;
    //     }
    // }

    // fn store_match_cost(&mut self, block_start: usize, index: usize, length: u16, distance: u16) {
    //     let index = index - block_start;

    //     assert!(self.slots[index].cost < u32::MAX / 2);

    //     let dist_cost =
    //         u32::from(self.dist_costs[bitstream::distance_to_dist_sym(distance) as usize]);
    //     let len_cost = u32::from(self.costs[LENGTH_TO_SYMBOL[length as usize - 3] as usize]);
    //     let cost = dist_cost + len_cost + self.slots[index].cost;
    //     if self.slots[index + length as usize].cost > cost {
    //         self.slots[index + length as usize].cost = cost;
    //         self.slots[index + length as usize].length = length;
    //         self.slots[index + length as usize].distance = distance;
    //     }
    // }

    fn compute_costs(
        &mut self,
        frequencies: &[u32; 286],
        dist_frequencies: &[u32; 30],
        total_symbols: u32,
        total_backrefs: u32,
    ) {
        self.costs = [15; 286];
        self.dist_costs = [10; 30];
        for (i, f) in frequencies.iter().enumerate() {
            if *f > 0 {
                self.costs[i] = (((*f) as f32 / total_symbols as f32).log2() * -1.0)
                    .round()
                    .clamp(1.0, 15.0) as u8;
                if i >= 257 {
                    self.costs[i] += LEN_SYM_TO_LEN_EXTRA[i - 257];
                }
            }
        }
        for (i, f) in dist_frequencies.iter().enumerate() {
            if *f > 0 {
                self.dist_costs[i] = (((*f) as f32 / total_backrefs as f32).log2() * -1.0)
                    .round()
                    .clamp(1.0, 15.0) as u8
                    + DIST_SYM_TO_DIST_EXTRA[i]
            }
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

        const OPT_WINDOW: usize = 100000;// 65536;

        if data.len() >= 8 {
            let current = u64::from_le_bytes(data[..8].try_into().unwrap());
            self.match_finder.insert(data, base_index, current, 0);
        }

        for block_start in (0..data.len()).step_by(OPT_WINDOW) {
            let block_length = (OPT_WINDOW).min(data.len() - block_start);
            let block_end = block_start + block_length;

            self.slots = vec![Slot::default(); block_length + 1];

            let mut high_water_mark = block_start + 1;

            let max_search_pos = block_end.min(data.len().saturating_sub(8));
            let mut i = block_start.max(1);
            while i < max_search_pos {
                let current = u64::from_le_bytes(data[i..][..8].try_into().unwrap());
                if current as u32 == (current >> 8) as u32 && false {
                    let mut length = 4;
                    if data[i - 1] != data[i] {
                        i += 1;
                        length -= 1;
                    }

                    // Find the match length.
                    while i + length < block_end && data[i + length] == data[i] {
                        length += 1;
                    }

                    // Store the matches.
                    for j in 0..=(length - 3) {
                        let slot = &mut self.slots[i + j - block_start];
                        slot.length = (length - j - 3).min(255) as u8;
                        slot.distance = 1;
                    }

                    high_water_mark = high_water_mark.max(i + length);
                    i += length - 2;
                    continue;
                }

                let ms = self
                    .match_finder
                    .get_all_and_insert(data, base_index, i, i, current);

                if ms.is_empty() {
                    i += 1 + ((i.saturating_sub(high_water_mark)) >> self.skip_ahead_shift);
                    continue;
                }

                let last_match = ms.len() - 1;
                let slot = &mut self.slots[i - block_start];

                assert!(ms[last_match].length >= 3);

                slot.length = (ms[last_match].length - 3) as u8;
                slot.distance = ms[last_match].distance;
                if ms.len() > 1 {
                    slot.length2 = (ms[last_match - 1].length - 3) as u8;
                    slot.distance2 = ms[last_match - 1].distance;
                    assert!(slot.distance2 < slot.distance);
                }

                high_water_mark = high_water_mark.max(i + 3 + slot.length as usize);

                // if slot.length > 150 {
                //     // //     let length = slot.length as usize + 3;
                //     // //     let distance = slot.distance;
                //     // //     for j in 0..(length - 10).min(block_end - i) {
                //     // //         let slot = &mut self.slots[i + j as usize - block_start];
                //     // //         slot.length = (length - j - 3).min(255) as u8;
                //     // //         slot.distance = distance;
                //     // //     }
                //     i += slot.length as usize - 10;
                // } else {
                    i += 1;
                // }
            }

            // If necessary, do a greedy pass to estimate the frequencies of symbols.
            if !self.initialized_costs {
                self.initialized_costs = true;

                let mut total_symbols = 0;
                let mut total_backrefs = 0;
                let mut frequencies = [0; 286];
                let mut dist_frequencies = [0; 30];
                frequencies[256] = 1; // EOF symbol

                let mut i = 0;
                while i < block_length {
                    if self.slots[i].distance > 0 && i + 3 <= self.slots.len() {
                        frequencies[LENGTH_TO_SYMBOL[self.slots[i].length as usize] as usize] += 1;
                        dist_frequencies
                            [bitstream::distance_to_dist_sym(self.slots[i].distance) as usize] += 1;
                        i += self.slots[i].length as usize + 3;
                        total_backrefs += 1;
                    } else {
                        frequencies[data[i] as usize] += 1;
                        i += 1;
                    }
                    total_symbols += 1;
                }

                self.compute_costs(
                    &frequencies,
                    &dist_frequencies,
                    total_symbols,
                    total_backrefs,
                );
            }

            for passes_left in (0..4).rev() {
                self.slots[block_length].cost = 0;
                self.slots[block_length].chosen_length = 1;

                for j in (0..block_length).rev() {
                    let lit_cost = u32::from(self.costs[data[block_start + j] as usize])
                        + self.slots[j + 1].cost;
                    let slot = &self.slots[j];

                    if slot.distance == 0 {
                        self.slots[j].cost = lit_cost;
                        self.slots[j].chosen_length = 1;
                    } else {
                        let mut best_length = 1;
                        let mut best_cost = lit_cost;

                        let dist_sym = bitstream::distance_to_dist_sym(slot.distance);
                        let dist_cost = u32::from(self.dist_costs[dist_sym as usize]);

                        let start = if slot.distance2 != 0 {
                            let dist2_sym = bitstream::distance_to_dist_sym(slot.distance2);
                            let dist2_cost = u32::from(self.dist_costs[dist2_sym as usize]);

                            let length2 = (slot.length2 as usize + 3).min(block_length - j);
                            for k in 3..=length2 {
                                let cost = dist2_cost
                                    + u32::from(self.costs[LENGTH_TO_SYMBOL[k - 3] as usize])
                                    + self.slots[j + k].cost;
                                if cost < best_cost {
                                    best_length = k as u16;
                                    best_cost = cost
                                }
                            }

                            length2 + 1
                        } else {
                            3
                        };

                        let length = (slot.length as usize + 3).min(block_length - j);
                        for k in start..=length {
                            let cost = dist_cost
                                + u32::from(self.costs[LENGTH_TO_SYMBOL[k - 3] as usize])
                                + self.slots[j + k].cost;
                            if cost < best_cost {
                                best_length = k as u16;
                                best_cost = cost
                            }
                        }

                        self.slots[j].cost = best_cost;
                        self.slots[j].chosen_length = best_length;
                        assert!(j + best_length as usize <= block_length);
                    }
                }

                if passes_left != 0 || true {
                    let mut total_symbols = 0;
                    let mut total_backrefs = 0;
                    let mut frequencies = [0; 286];
                    let mut dist_frequencies = [0; 30];

                    frequencies[256] = 1; // EOF symbol

                    let mut i = 0;
                    while i < block_length {
                        let m = &self.slots[i];
                        if m.chosen_length != 1 {
                            frequencies[LENGTH_TO_SYMBOL[m.chosen_length as usize - 3] as usize] +=
                                1;
                            dist_frequencies
                                [bitstream::distance_to_dist_sym(m.distance) as usize] += 1;
                            i += m.chosen_length as usize;
                            total_backrefs += 1;
                        } else {
                            frequencies[data[block_start + i] as usize] += 1;
                            i += 1;
                        }
                        total_symbols += 1;
                    }

                    self.compute_costs(
                        &frequencies,
                        &dist_frequencies,
                        total_symbols,
                        total_backrefs,
                    );
                }
            }

            // And convert to symbols in the forward direction.
            let mut j = 0;
            let mut symbol_run = 0;
            while j < block_length {
                let m = &self.slots[j];
                assert!(j + m.chosen_length as usize <= block_length);
                assert!(m.chosen_length != 0);
                if m.chosen_length == 1 {
                    symbol_run += 1;
                    j += 1;
                    assert!(j as usize <= block_length);
                    continue;
                }

                let distance = if m.distance2 != 0 && m.chosen_length <= u16::from(m.length2) + 3 {
                    m.distance2
                } else {
                    m.distance
                };
                // let distance = m.distance;
                assert!(distance > 0);
                assert!(
                    (distance as usize) <= block_start + j,
                    "distance={} index={}",
                    distance,
                    block_start + j
                );

                if symbol_run > 0 {
                    symbols.push(Symbol::LiteralRun {
                        start: (block_start + j - symbol_run) as u32,
                        end: (block_start + j) as u32,
                    });
                    symbol_run = 0;
                }

                symbols.push(Symbol::Backref {
                    length: m.chosen_length,
                    distance,
                    dist_sym: bitstream::distance_to_dist_sym(distance),
                });
                j += m.chosen_length as usize;

                assert!(
                    j as usize <= block_length,
                    "j={} block_length={} chosen_length={}",
                    j,
                    block_length,
                    m.chosen_length
                );
                if symbols.len() >= 16384 {
                    let last_block = flush == Flush::Finish && block_start + j as usize == data.len();
                    bitstream::write_block(writer, data, base_index, &symbols, last_block)?;
                    symbols.clear();
                }
            }
            assert_eq!(j as usize, block_length);

            if symbol_run > 0 {
                symbols.push(Symbol::LiteralRun {
                    start: (block_end - symbol_run) as u32,
                    end: block_end as u32,
                });
            }
        }

        if !symbols.is_empty() {
            bitstream::write_block(writer, data, base_index, &symbols, true)?;
        }

        Ok(data.len())
    }
}
