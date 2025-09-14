use crate::compress::{
    matchfinder::{self, PackedMatch},
    WINDOW_SIZE,
};

const CACHE_SIZE: usize = 1 << 16;
const CACHE3_SIZE: usize = 1 << 16;

/// Find the length of the match between the current position and the previous position, searching
/// both forwards and backwards from the starting position.
fn _match_length(data: &[u8], ip: usize, prev_index: usize) -> u16 {
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
    hash3_table: Box<[u32; CACHE3_SIZE]>,
    hash_table: Box<[u32; CACHE_SIZE]>,
    child_links: Box<[u32; WINDOW_SIZE * 2]>,
    search_depth: u16,
    early_return_length: usize,
}
impl BinaryTreeMatchFinder {
    pub(crate) fn new(search_depth: u16, nice_length: u16) -> Self {
        Self {
            hash3_table: vec![0; CACHE3_SIZE].into_boxed_slice().try_into().unwrap(),
            hash_table: vec![0; CACHE_SIZE].into_boxed_slice().try_into().unwrap(),
            child_links: vec![0; WINDOW_SIZE * 2]
                .into_boxed_slice()
                .try_into()
                .unwrap(),
            search_depth,
            early_return_length: nice_length as usize,
        }
    }

    fn update(
        &mut self,
        data: &[u8],
        base_index: u32,
        ip: usize,
        value: u32,
        record_matches: bool,
        found_matches: &mut Vec<PackedMatch>,
    ) -> usize {
        let min_offset = (base_index + (ip as u32).saturating_sub(32768)).max(1);

        let mut num_matches = 0;
        let mut best_length = 3;

        // Lookup current value
        let hash = super::compute_hash(value as u64);
        let hash_index = (hash as usize) % CACHE_SIZE;
        let mut offset = self.hash_table[hash_index];
        self.hash_table[hash_index] = ip as u32 + base_index;

        // Look for 3-byte match
        let hash3 = super::compute_hash((value & 0xff_ffff) as u64);
        let hash3_index = (hash3 as usize) % CACHE3_SIZE;
        let offset3 = self.hash3_table[hash3_index];
        self.hash3_table[hash3_index] = ip as u32 + base_index;

        if record_matches && offset3 >= min_offset && offset3 != offset {
            let prev = u32::from_le_bytes(
                data[(offset3 - base_index) as usize..][..4]
                    .try_into()
                    .unwrap(),
            );
            if ((value as u32) ^ prev) & 0xffffff == 0 {
                num_matches = 1;
                found_matches.push(PackedMatch {
                    length: 3,
                    distance: (ip - (offset3 - base_index) as usize) as u16,
                });
            }
        }

        let mut pending_left = left_child(ip as u32 + base_index);
        let mut pending_right = right_child(ip as u32 + base_index);

        if offset < min_offset {
            self.child_links[pending_left] = 0;
            self.child_links[pending_right] = 0;
            return num_matches;
        }

        let mut best_left_length = 0;
        let mut best_right_length = 0;
        let mut length = 0;

        // let data = &data[..ip + 258.min(data.len() - ip)];

        // let max_length = (data.len() - ip).min(258);

        // Visit previous matches
        let mut depth_remaining = self.search_depth;
        loop {
            if data[ip + length] == data[(offset - base_index) as usize + length] {
                //length += 1;
                length += matchfinder::extend_match(
                    data,
                    ip + length,
                    (offset - base_index) as usize + length,
                ) as usize;

                if record_matches && length > best_length as usize {
                    if num_matches == 255 {
                        found_matches.pop().unwrap();
                        num_matches -= 1;
                    }

                    best_length = length.min(258) as u16;
                    num_matches += 1;
                    found_matches.push(PackedMatch {
                        length: best_length,
                        distance: (ip - (offset - base_index) as usize) as u16,
                    });
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

        num_matches
    }

    pub(crate) fn get_and_insert(
        &mut self,
        found_matches: &mut Vec<PackedMatch>,
        data: &[u8],
        base_index: u32,
        ip: usize,
        value: u32,
    ) -> usize {
        self.update(data, base_index, ip, value, true, found_matches)
    }

    pub(crate) fn insert(&mut self, data: &[u8], base_index: u32, ip: usize, value: u32) {
        self.update(data, base_index, ip, value, false, &mut Vec::new());
    }

    pub(crate) fn reset_indices(&mut self, old_base_index: u32) {
        for v in &mut *self.hash3_table {
            *v = v.saturating_sub(old_base_index);
        }

        for v in &mut *self.hash_table {
            *v = v.saturating_sub(old_base_index);
        }

        for v in &mut *self.child_links {
            *v = v.saturating_sub(old_base_index);
        }
    }
}
