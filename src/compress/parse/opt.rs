use std::io::{self, Write};

use crate::{
    compress::{
        bitstream::{self, Symbol},
        matchfinder::{BinaryTreeMatchFinder, PackedMatch},
        BitWriter, Flush,
    },
    tables::{DIST_SYM_TO_DIST_EXTRA, LENGTH_TO_SYMBOL, LEN_SYM_TO_LEN_EXTRA},
};

#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
struct Slot {
    cost: u32,
    chosen_length: u16,
    chosen_distance: u16,
    num_matches: u8,
}

pub(crate) struct NearOptimalParser {
    match_finder: BinaryTreeMatchFinder,
    skip_ahead_shift: u8,

    // symbols: Vec<Symbol>,
    last_index: u32,

    costs: [u8; 286],
    length_costs: [u8; 259],
    dist_costs: [u8; 30],
    initialized_costs: bool,

    distance_to_sym: Vec<u8>,

    found_matches: Vec<PackedMatch>,
    slots: Vec<Slot>,
}

impl NearOptimalParser {
    pub fn new(skip_ahead_shift: u8, match_finder: BinaryTreeMatchFinder) -> Self {
        Self {
            match_finder,
            skip_ahead_shift,
            // symbols: Vec::new(),
            // ip: 0,
            // last_match: 0,
            // m: Match::empty(),
            last_index: 0,

            costs: [9; 286],
            length_costs: [9; 259],
            dist_costs: [6; 30],
            initialized_costs: false,

            distance_to_sym: Vec::new(),
            found_matches: Vec::new(),
            slots: Vec::new(),
        }
    }

    pub fn reset_indices(&mut self, old_base_index: u32) {
        self.last_index -= old_base_index;
        self.match_finder.reset_indices(old_base_index);
    }

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

        for len in 3..=258 {
            self.length_costs[len] = self.costs[LENGTH_TO_SYMBOL[len - 3] as usize];
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

        if self.distance_to_sym.is_empty() {
            self.distance_to_sym.push(0);
        }
        for i in self.distance_to_sym.len()..data.len().min(32769) {
            self.distance_to_sym
                .push(bitstream::distance_to_dist_sym(i as u16));
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

        const OPT_WINDOW: usize = 65536;

        if data.len() >= 8 {
            let current = u64::from_le_bytes(data[..8].try_into().unwrap());
            self.match_finder.insert(data, base_index, current, 0);
        }

        for block_start in (0..data.len()).step_by(OPT_WINDOW) {
            let block_length = (OPT_WINDOW).min(data.len() - block_start);
            let block_end = block_start + block_length;

            self.slots = vec![Slot::default(); block_length + 1];

            self.found_matches.clear();
            self.found_matches.push(PackedMatch {
                length: 0,
                distance: 0,
            });

            let mut high_water_mark = block_start + 1;

            let max_search_pos = block_end.min(data.len().saturating_sub(8));
            let mut i = block_start.max(1);
            while i < max_search_pos {
                let current = u64::from_le_bytes(data[i..][..8].try_into().unwrap());
                if (current >> 8) == (current & 0xff_ffff_ffff_ffff) && false {
                    let mut length = 8;
                    if data[i - 1] != data[i] {
                        assert_eq!(self.slots[i - block_start].num_matches, 0);
                        i += 1;
                        length -= 1;
                        if i == max_search_pos {
                            break;
                        }
                    }
                    // Find the match length.
                    while i + length < block_end && data[i + length] == data[i] {
                        length += 1;
                    }
                    // Store the matches.
                    let n = (length - 6).min(block_end - i);
                    for j in 0..n {
                        self.slots[i + j - block_start].num_matches = 1;
                        self.found_matches.push(PackedMatch {
                            length: (length - j).min(258) as u16,
                            distance: 1,
                        });

                        assert_eq!(data[i + j - 1], data[i + j]);
                    }
                    high_water_mark = high_water_mark.max(i + length);
                    i += n;
                    continue;
                }

                let n = self.match_finder.get_and_insert(
                    &mut self.found_matches,
                    data,
                    base_index,
                    i,
                    current,
                );

                if n == 0 {
                    i += 1 ;//+ ((i.saturating_sub(high_water_mark)) >> self.skip_ahead_shift);
                    continue;
                }

                assert_eq!(self.slots[i - block_start].num_matches, 0);
                self.slots[i - block_start].num_matches = n as u8;
                let max_len = self.found_matches.last().unwrap().length as usize;
                high_water_mark = high_water_mark.max(i + max_len);
                i += 1;

                // if max_len >= 75 {
                //     for _ in 0..max_len {
                //         if i >= max_search_pos {
                //             break;
                //         }
                //         let current = u64::from_le_bytes(data[i..][..8].try_into().unwrap());
                //         self.match_finder
                //             .insert(data, base_index, current, i as u32);
                //         i += 1;
                //     }
                // }
            }

            // // If necessary, do a greedy pass to estimate the frequencies of symbols.
            // if !self.initialized_costs {
            //     self.initialized_costs = true;

            //     let mut total_symbols = 0;
            //     let mut total_backrefs = 0;
            //     let mut frequencies = [0; 286];
            //     let mut dist_frequencies = [0; 30];
            //     frequencies[256] = 1; // EOF symbol

            //     let mut i = 0;
            //     while i < block_length {
            //         if self.slots[i].distance > 0 && i + 3 <= self.slots.len() {
            //             frequencies[LENGTH_TO_SYMBOL[self.slots[i].length as usize] as usize] += 1;
            //             dist_frequencies
            //                 [bitstream::distance_to_dist_sym(self.slots[i].distance) as usize] += 1;
            //             i += self.slots[i].length as usize + 3;
            //             total_backrefs += 1;
            //         } else {
            //             frequencies[data[i] as usize] += 1;
            //             i += 1;
            //         }
            //         total_symbols += 1;
            //     }

            //     self.compute_costs(
            //         &frequencies,
            //         &dist_frequencies,
            //         total_symbols,
            //         total_backrefs,
            //     );
            // }

            for passes_left in (0..2).rev() {
                self.slots[block_length].cost = 0;
                self.slots[block_length].chosen_length = 1;

                let mut match_index = self.found_matches.len() - 1;
                for j in (0..block_length).rev() {
                    let lit_cost = u32::from(self.costs[data[block_start + j] as usize])
                        + self.slots[j + 1].cost;
                    let slot = &self.slots[j];

                    if slot.num_matches == 0 {
                        self.slots[j].cost = lit_cost;
                        self.slots[j].chosen_length = 1;
                    } else if self.found_matches[match_index].distance > 64 {
                        // If we have a long match, just use it.
                        let distance = self.found_matches[match_index].distance as usize;
                        let dist_sym = self.distance_to_sym[distance] as usize;
                        let length =
                            (self.found_matches[match_index].length as usize).min(block_length - j);
                        match_index -= slot.num_matches as usize;

                        let backref_cost = u32::from(self.dist_costs[dist_sym])
                            + u32::from(self.length_costs[length])
                            + self.slots[j + length].cost;

                        let slot = &mut self.slots[j];
                        slot.cost = backref_cost.min(lit_cost);
                        if backref_cost < lit_cost && length >= 3 {
                            slot.chosen_distance = distance as u16;
                            slot.chosen_length = length as u16;
                        } else {
                            slot.chosen_length = 1;
                        }
                    } else {
                        let mut best_length = 1;
                        let mut best_distance = 0;
                        let mut best_cost = lit_cost;

                        let mut length = 3;
                        let mut index = match_index + 1 - slot.num_matches as usize;
                        while index <= match_index {
                            let distance = self.found_matches[index].distance as usize;
                            let dist_sym = self.distance_to_sym[distance] as usize;
                            let dist_cost = u32::from(self.dist_costs[dist_sym]);

                            while length <= self.found_matches[index].length as usize
                                && length <= block_length - j
                            {
                                let cost = dist_cost
                                    + u32::from(self.length_costs[length])
                                    + self.slots[j + length].cost;

                                if cost < best_cost {
                                    best_length = length as u16;
                                    best_distance = distance as u16;
                                    best_cost = cost;
                                }
                                length += 1;
                            }
                            index += 1;
                        }

                        match_index -= slot.num_matches as usize;
                        self.slots[j].cost = best_cost;
                        self.slots[j].chosen_length = best_length;
                        self.slots[j].chosen_distance = best_distance;
                        assert!(j + best_length as usize <= block_length);
                        assert!(best_distance as usize <= block_start + j as usize)
                    }
                }

                if passes_left != 0 {
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
                                [self.distance_to_sym[m.chosen_distance as usize] as usize] += 1;
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

                // let distance = if m.distance2 != 0 && m.chosen_length <= u16::from(m.length2) + 3 {
                //     m.distance2
                // } else {
                //     m.distance
                // };
                let distance = m.chosen_distance;
                assert!(distance > 0);
                assert!((distance as usize) <= block_start + j,);

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
                    dist_sym: self.distance_to_sym[distance as usize],
                });
                j += m.chosen_length as usize;

                assert!(j as usize <= block_length,);
                if symbols.len() >= 16384 {
                    let last_block =
                        flush == Flush::Finish && block_start + j as usize == data.len();
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
