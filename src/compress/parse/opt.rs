use std::io::{self, Write};

use crate::{
    compress::{
        bitstream::{self, Symbol},
        matchfinder::{MatchFinder},
        BitWriter, Flush,
    },
    tables::{DIST_SYM_TO_DIST_EXTRA, LENGTH_TO_SYMBOL, LEN_SYM_TO_LEN_EXTRA},
};

#[derive(Debug, Clone, Copy)]
struct Slot {
    length: u16,
    distance: u16,
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
        }
    }

    pub fn reset_indices(&mut self, old_base_index: u32) {
        self.last_index -= old_base_index;
        self.match_finder.reset_indices(old_base_index);
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

        let mut matches = vec![
            Slot {
                length: 0,
                distance: 0,
                cost: 0,
                chosen_length: 0,
            };
            data.len() + 1
        ];

        let mut i = 1;
        let mut high_water_mark = 1;
        while i < data.len().saturating_sub(8) {
            let current = u64::from_le_bytes(data[i..][..8].try_into().unwrap());
            if current as u32 == (current >> 8) as u32 {
                if data[i - 1] != data[i] {
                    i += 1;
                }

                let mut length = 4;
                while i + length < data.len() && data[i + length] == data[i] {
                    length += 1;
                }

                high_water_mark = high_water_mark.max(i + length);
                while length >= 4 {
                    matches[i].length = length.min(258) as u16;
                    matches[i].distance = 1;
                    i += 1;
                    length -= 1;
                }
            } else {
                let m = self
                    .match_finder
                    .get_and_insert(data, base_index, i, i, current);

                if !m.is_empty() {
                    matches[i].length = m.length;
                    matches[i].distance = m.distance;
                    high_water_mark = high_water_mark.max(i + m.length as usize);
                    i += 1;
                } else {
                    i += 1 + ((i.saturating_sub(high_water_mark)) >> self.skip_ahead_shift);
                }
            }
        }

        let mut total_symbols = 0;
        let mut total_backrefs = 0;
        let mut frequencies = [0; 286];
        let mut dist_frequencies = [0; 30];

        frequencies[256] = 1; // EOF symbol

        // Do a greedy pass to estimate the frequencies of symbols.
        let mut i = 0;
        while i < data.len() {
            if matches[i].length > 0 {
                frequencies[LENGTH_TO_SYMBOL[matches[i].length as usize - 3] as usize] += 1;
                dist_frequencies[bitstream::distance_to_dist_sym(matches[i].distance) as usize] +=
                    1;
                i += matches[i].length as usize;
                total_backrefs += 1;
            } else {
                frequencies[data[i] as usize] += 1;
                i += 1;
            }
            total_symbols += 1;
        }

        for passes_left in (0..1).rev() {
            let mut costs = [15; 286];
            let mut dist_costs = [10; 30];
            for (i, f) in frequencies.iter().enumerate() {
                if *f > 0 {
                    costs[i] = (((*f) as f32 / total_symbols as f32).log2() * -1.0)
                        .round()
                        .clamp(1.0, 15.0) as u32;
                    if i >= 257 {
                        costs[i] += LEN_SYM_TO_LEN_EXTRA[i - 257] as u32;
                    }
                }
            }
            for (i, f) in dist_frequencies.iter().enumerate() {
                if *f > 0 {
                    dist_costs[i] = (((*f) as f32 / total_backrefs as f32).log2() * -1.0)
                        .round()
                        .clamp(1.0, 15.0) as u32
                        + DIST_SYM_TO_DIST_EXTRA[i] as u32;
                }
            }

            matches[data.len() - 1].cost = costs[data[data.len() - 1] as usize];
            for i in (0..matches.len() - 1).rev() {
                let lit_cost = costs[data[i] as usize] + matches[i + 1].cost;

                if matches[i].length == 0 {
                    matches[i].cost = lit_cost;
                    matches[i].chosen_length = 0;
                } else {
                    let mut best_length = 0;
                    let mut best_cost = lit_cost;
                    let dist_cost =
                        dist_costs[bitstream::distance_to_dist_sym(matches[i].distance) as usize];

                    for j in 3..=matches[i].length as usize {
                        let cost = dist_cost
                            + costs[LENGTH_TO_SYMBOL[j - 3] as usize]
                            + matches[i + j].cost;
                        if cost < best_cost {
                            best_length = j as u16;
                            best_cost = cost
                        }
                    }

                    matches[i].cost = best_cost;
                    matches[i].chosen_length = best_length;
                }
            }

            if passes_left != 0 {
                total_symbols = 0;
                total_backrefs = 0;
                frequencies = [0; 286];
                dist_frequencies = [0; 30];

                frequencies[256] = 1; // EOF symbol

                let mut i = 0;
                while i < data.len() {
                    let m = &matches[i];
                    if m.chosen_length > 0 {
                        frequencies[LENGTH_TO_SYMBOL[m.chosen_length as usize - 3] as usize] += 1;
                        dist_frequencies[bitstream::distance_to_dist_sym(m.distance) as usize] += 1;
                        i += m.chosen_length as usize;
                        total_backrefs += 1;
                    } else {
                        frequencies[data[i] as usize] += 1;
                        i += 1;
                    }
                    total_symbols += 1;
                }
            }
        }

        let mut i = 0;
        let mut symbols = Vec::new();
        let mut symbol_run = 0;
        while i + symbol_run < data.len() {
            let m = &matches[i + symbol_run];
            if m.chosen_length == 0 {
                symbol_run += 1;
            } else {
                if symbol_run > 0 {
                    symbols.push(Symbol::LiteralRun {
                        start: i as u32,
                        end: (i + symbol_run) as u32,
                    });
                    i += symbol_run;
                    symbol_run = 0;
                }
                symbols.push(Symbol::Backref {
                    length: m.chosen_length,
                    distance: m.distance,
                    dist_sym: bitstream::distance_to_dist_sym(m.distance),
                });
                i += m.chosen_length as usize;

                assert!(i as usize <= data.len());
                if symbols.len() >= 16384 {
                    let last_block = flush == Flush::Finish && i as usize == data.len();
                    bitstream::write_block(writer, data, base_index, &symbols, last_block)?;
                    symbols.clear();
                }
            }
        }

        if symbol_run > 0 {
            symbols.push(Symbol::LiteralRun {
                start: i as u32,
                end: (i + symbol_run) as u32,
            });
            i += symbol_run;
        }
        assert_eq!(i as usize, data.len());

        if !symbols.is_empty() {
            bitstream::write_block(writer, data, base_index, &symbols, true)?;
        }

        Ok(data.len())
    }
}
