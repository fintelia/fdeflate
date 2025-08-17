use crate::compress::{
    matchfinder::{Match, MatchFinder},
    WINDOW_SIZE,
};

const CACHE_SIZE: usize = 1 << 16;

/// Find the length of the match between the current position and the previous position, searching
/// both forwards and backwards from the starting position.
fn match_length(data: &[u8], ip: usize, prev_index: usize) -> u16 {
    assert!(
        prev_index < ip,
        "Match past current position: {prev_index} {ip}"
    );

    let mut length = 0;
    while length < 258 && ip + length < data.len() && data[ip + length] == data[prev_index + length]
    {
        length += 1;
    }
    length as u16
}

fn left_child(index: u32) -> usize {
    2 * (index as usize % WINDOW_SIZE)
}

fn right_child(index: u32) -> usize {
    2 * (index as usize % WINDOW_SIZE) + 1
}

/// Match finder that uses a binary tree to find matches.
///
/// Based on bt_matchfinder.h from libdeflate.
pub(crate) struct BinaryTreeMatchFinder {
    hash_table: Box<[u32; CACHE_SIZE]>,
    child_links: Box<[u32; WINDOW_SIZE * 2]>,
    search_depth: u16,
    early_return_length: usize,
}
impl BinaryTreeMatchFinder {
    pub(crate) fn new(search_depth: u16) -> Self {
        Self {
            hash_table: vec![0; CACHE_SIZE].into_boxed_slice().try_into().unwrap(),
            child_links: vec![0; WINDOW_SIZE * 2]
                .into_boxed_slice()
                .try_into()
                .unwrap(),
            search_depth,
            early_return_length: 258,
        }
    }

    fn update(
        &mut self,
        data: &[u8],
        base_index: u32,
        ip: usize,
        value: u64,
        record_matches: bool,
    ) -> Match {
        let min_offset = (base_index + (ip as u32).saturating_sub(32768)).max(1);

        let mut best_offset = 0;
        let mut best_length = 3;

        // Lookup current value
        let hash = super::compute_hash(value & 0xff_ffff_ffff);
        let hash_index = (hash as usize) % CACHE_SIZE;
        let mut offset = self.hash_table[hash_index];
        self.hash_table[hash_index] = ip as u32;

        let mut pending_left = left_child(ip as u32 + base_index);
        let mut pending_right = right_child(ip as u32 + base_index);

        if offset < min_offset {
            self.child_links[pending_left] = 0;
            self.child_links[pending_right] = 0;
            return Match::empty();
        }

        let mut best_left_length = 0;
        let mut best_right_length = 0;
        let mut length = 0;

        // Visit previous matches
        let mut depth_remaining = self.search_depth;
        loop {
            if data[ip + length] == data[(offset - base_index) as usize + length] {
                while length < 258
                    && ip + length < data.len()
                    && data[ip + length] == data[(offset - base_index) as usize + length]
                {
                    length += 1;
                }

                if record_matches && length > best_length as usize {
                    best_length = length as u16;
                    best_offset = offset as u32;
                }

                if length >= self.early_return_length || ip + length == data.len() {
                    self.child_links[pending_left] = self.child_links[left_child(offset)];
                    self.child_links[pending_right] = self.child_links[right_child(offset)];
                    break;
                }
            }

            assert!(ip + length < data.len());

            if data[(offset - base_index) as usize + length] < data[ip + length] {
                self.child_links[pending_left] = offset as u32;
                pending_left = right_child(offset);
                offset = self.child_links[pending_left];

                best_left_length = length;
                if best_right_length < length {
                    length = best_right_length;
                }
            } else {
                assert!(
                    data[(offset - base_index) as usize + length] > data[ip + length],
                    "{length} {depth_remaining} {offset} {min_offset}"
                );

                self.child_links[pending_right] = offset as u32;
                pending_right = left_child(offset);
                offset = self.child_links[pending_right];

                best_right_length = length;
                if best_left_length < length {
                    length = best_left_length;
                }
            }

            depth_remaining -= 1;
            if offset <= min_offset || depth_remaining == 0 {
                self.child_links[pending_left] = 0;
                self.child_links[pending_right] = 0;
                break;
            }
        }

        if best_length >= 4 {
            return Match {
                length: best_length,
                distance: (ip - (best_offset - base_index) as usize) as u16,
                start: ip,
            };
        }

        Match::empty()
    }
}
impl MatchFinder for BinaryTreeMatchFinder {
    fn get_and_insert(
        &mut self,
        data: &[u8],
        base_index: u32,
        _anchor: usize,
        ip: usize,
        value: u64,
    ) -> Match {
        self.update(data, base_index, ip, value, true)
    }

    fn insert(&mut self, data: &[u8], base_index: u32, value: u64, offset: u32) {
        self.update(
            data,
            base_index,
            (offset - base_index) as usize,
            value,
            false,
        );
    }

    fn reset_indices(&mut self, old_base_index: u32) {
        for v in &mut *self.hash_table {
            *v = v.saturating_sub(old_base_index);
        }

        for v in &mut *self.child_links {
            *v = v.saturating_sub(old_base_index);
        }
    }
}
