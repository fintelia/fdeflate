#![allow(unused)]

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
    nice_length: usize,
    iters: u8,

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
    pub fn new(skip_ahead_shift: u8, iters: u8, search_depth: u16, nice_length: u16) -> Self {
        Self {
            match_finder: BinaryTreeMatchFinder::new(search_depth, nice_length),
            skip_ahead_shift,
            nice_length: nice_length as usize,
            iters,
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
    ) -> u32 {
        self.costs = [13; 286];
        self.dist_costs = [10; 30];
        for (i, f) in frequencies.iter().enumerate() {
            if *f > 0 {
                self.costs[i] = (((*f) as f32 / total_symbols as f32).log2() * -1.0)
                    .round()
                    .clamp(1.0, 13.0) as u8;
                if i >= 257 {
                    self.costs[i] += LEN_SYM_TO_LEN_EXTRA[i - 257];
                }
            }
        }
        for (i, f) in dist_frequencies.iter().enumerate() {
            if *f > 0 {
                self.dist_costs[i] = (((*f) as f32 / total_backrefs as f32).log2() * -1.0)
                    .round()
                    .clamp(1.0, 10.0) as u8
                    + DIST_SYM_TO_DIST_EXTRA[i]
            }
        }

        for len in 3..=258 {
            self.length_costs[len] = self.costs[LENGTH_TO_SYMBOL[len - 3] as usize];
        }

        let mut total_cost = 0u32;
        for (i, f) in frequencies.iter().enumerate() {
            total_cost += u32::from(self.costs[i]) * f;
        }
        for (i, f) in dist_frequencies.iter().enumerate() {
            total_cost += u32::from(self.dist_costs[i]) * f;
        }
        total_cost
    }

    fn compute_true_costs(
        &mut self,
        frequencies: &[u32; 286],
        dist_frequencies: &[u32; 30],
    ) -> u32 {
        let mut codes = [0u16; 286];
        let mut dist_codes = [0u16; 30];

        self.costs.fill(0);
        bitstream::build_huffman_tree(frequencies, &mut self.costs, &mut codes, 15);
        for (i, c) in self.costs.iter_mut().enumerate() {
            if *c == 0 {
                *c = 13;
            }
            if i >= 257 {
                *c += LEN_SYM_TO_LEN_EXTRA[i - 257];
            }
        }

        self.dist_costs.fill(0);
        bitstream::build_huffman_tree(dist_frequencies, &mut self.dist_costs, &mut dist_codes, 15);
        for (i, c) in self.dist_costs.iter_mut().enumerate() {
            if *c == 0 {
                *c = 10;
            }
            *c += DIST_SYM_TO_DIST_EXTRA[i];
        }

        for len in 3..=258 {
            self.length_costs[len] = self.costs[LENGTH_TO_SYMBOL[len - 3] as usize];
        }

        let mut total_cost = 0u32;
        for (i, f) in frequencies.iter().enumerate() {
            total_cost += u32::from(self.costs[i]) * f;
        }
        for (i, f) in dist_frequencies.iter().enumerate() {
            total_cost += u32::from(self.dist_costs[i]) * f;
        }
        total_cost
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
        self.costs = [12; 286];
        self.dist_costs = [10; 30];
        for (i, f) in lit_freqs[0].iter().enumerate() {
            if *f > 0 {
                self.costs[i] = (((*f) as f32 / lookahead as f32).log2() * -1.0)
                    .round()
                    .clamp(1.0, 12.0) as u8;
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

        if data.len() >= 8 && base_index == 0 {
            let current = u64::from_le_bytes(data[..8].try_into().unwrap());
            self.match_finder.insert(data, base_index, 0, current);
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
                let n = self.match_finder.get_and_insert(
                    &mut self.found_matches,
                    data,
                    base_index,
                    i,
                    current,
                );

                if n == 0 {
                    i += 1 + ((i.saturating_sub(high_water_mark)) >> self.skip_ahead_shift);
                    continue;
                }

                assert_eq!(self.slots[i - block_start].num_matches, 0);
                self.slots[i - block_start].num_matches = n as u8;
                let max_len = self.found_matches.last().unwrap().length as usize;
                high_water_mark = high_water_mark.max(i + max_len);
                i += 1;

                if max_len >= self.nice_length {
                    let end_index = (i + max_len).min(max_search_pos) - 1;
                    while i < end_index {
                        let current = u64::from_le_bytes(data[i..][..8].try_into().unwrap());
                        self.match_finder.insert(data, base_index, i, current);
                        i += 1;
                    }
                }
            }

            let mut best_total_cost = u32::MAX;
            for _ in 0..self.iters {
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

                let mut _total_symbols = 0;
                let mut _total_backrefs = 0;
                let mut frequencies = [0; 286];
                let mut dist_frequencies = [0; 30];

                frequencies[256] = 1; // EOF symbol

                let mut i = 0;
                while i < block_length {
                    let m = &self.slots[i];
                    if m.chosen_length != 1 {
                        frequencies[LENGTH_TO_SYMBOL[m.chosen_length as usize - 3] as usize] += 1;
                        dist_frequencies
                            [self.distance_to_sym[m.chosen_distance as usize] as usize] += 1;
                        i += m.chosen_length as usize;
                        _total_backrefs += 1;
                    } else {
                        frequencies[data[block_start + i] as usize] += 1;
                        i += 1;
                    }
                    _total_symbols += 1;
                }

                // let total_cost = self.compute_costs(
                //     &frequencies,
                //     &dist_frequencies,
                //     total_symbols,
                //     total_backrefs,
                // );
                let total_cost = self.compute_true_costs(&frequencies, &dist_frequencies);
                if total_cost >= best_total_cost {
                    break;
                }
                best_total_cost = total_cost;
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
            }
            assert_eq!(j as usize, block_length);

            if symbol_run > 0 {
                symbols.push(Symbol::LiteralRun {
                    start: (block_end - symbol_run) as u32,
                    end: block_end as u32,
                });
            }

            if !symbols.is_empty() {
                let last_block = flush == Flush::Finish && block_start + j as usize == data.len();
                bitstream::write_block(writer, data, base_index, &symbols, last_block)?;
                symbols.clear();
            }
        }

        if !symbols.is_empty() {
            bitstream::write_block(writer, data, base_index, &symbols, flush == Flush::Finish)?;
        }

        Ok(data.len())
    }
}
