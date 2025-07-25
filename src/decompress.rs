use simd_adler32::Adler32;
use std::num::NonZeroUsize;

use crate::{
    huffman::{self, build_table},
    tables::{
        self, CLCL_ORDER, DIST_SYM_TO_DIST_BASE, DIST_SYM_TO_DIST_EXTRA, FIXED_DIST_TABLE,
        FIXED_LITLEN_TABLE, LEN_SYM_TO_LEN_BASE, LEN_SYM_TO_LEN_EXTRA, LITLEN_TABLE_ENTRIES,
    },
};

/// An error encountered while decompressing a deflate stream.
#[derive(Debug, PartialEq, Clone)]
pub enum DecompressionError {
    /// The zlib header is corrupt.
    BadZlibHeader,
    /// All input was consumed, but the end of the stream hasn't been reached.
    InsufficientInput,
    /// A block header specifies an invalid block type.
    InvalidBlockType,
    /// An uncompressed block's NLEN value is invalid.
    InvalidUncompressedBlockLength,
    /// Too many literals were specified.
    InvalidHlit,
    /// Too many distance codes were specified.
    InvalidHdist,
    /// Attempted to repeat a previous code before reading any codes, or past the end of the code
    /// lengths.
    InvalidCodeLengthRepeat,
    /// The stream doesn't specify a valid huffman tree.
    BadCodeLengthHuffmanTree,
    /// The stream doesn't specify a valid huffman tree.
    BadLiteralLengthHuffmanTree,
    /// The stream doesn't specify a valid huffman tree.
    BadDistanceHuffmanTree,
    /// The stream contains a literal/length code that was not allowed by the header.
    InvalidLiteralLengthCode,
    /// The stream contains a distance code that was not allowed by the header.
    InvalidDistanceCode,
    /// The stream contains contains back-reference as the first symbol.
    InputStartsWithRun,
    /// The stream contains a back-reference that is too far back.
    DistanceTooFarBack,
    /// The deflate stream checksum is incorrect.
    WrongChecksum,
    /// Extra input data.
    ExtraInput,
}

struct BlockHeader {
    hlit: usize,
    hdist: usize,
    hclen: usize,
    num_lengths_read: usize,

    /// Low 3-bits are code length code length, high 5-bits are code length code.
    table: [u32; 128],
    code_lengths: [u8; 320],
}

pub const LITERAL_ENTRY: u32 = 0x8000;
pub const EXCEPTIONAL_ENTRY: u32 = 0x4000;
pub const SECONDARY_TABLE_ENTRY: u32 = 0x2000;

// See https://github.com/image-rs/fdeflate/issues/45 for discussion of the table sizes.
const DEFAULT_LITLEN_TABLE_SIZE: usize = 4096;
const DEFAULT_DIST_TABLE_SIZE: usize = 512;

/// The Decompressor state for a compressed block.
#[derive(Eq, PartialEq, Debug)]
struct CompressedBlock<const LITLEN_TABLE_SIZE: usize, const DIST_TABLE_SIZE: usize> {
    litlen_table: Box<[u32; LITLEN_TABLE_SIZE]>,
    secondary_table: Vec<u16>,

    dist_table: Box<[u32; DIST_TABLE_SIZE]>,
    dist_secondary_table: Vec<u16>,

    eof_code: u16,
    eof_mask: u16,
    eof_bits: u8,
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
enum State {
    ZlibHeader,
    BlockHeader,
    CodeLengthCodes,
    CodeLengths,
    CompressedData,
    UncompressedData,
    Checksum,
    Done,
}

/// Decompressor for arbitrary zlib streams.
pub struct Decompressor {
    /// State for decoding a compressed block.
    compression: CompressedBlock<DEFAULT_LITLEN_TABLE_SIZE, DEFAULT_DIST_TABLE_SIZE>,
    // State for decoding a block header.
    header: BlockHeader,
    // Number of bytes left for uncompressed block.
    uncompressed_bytes_left: u16,

    bits: BitBuffer,

    queued_output: Option<QueuedOutput>,
    last_block: bool,
    fixed_table: bool,

    state: State,
    checksum: Adler32,
    ignore_adler32: bool,
}

impl Default for Decompressor {
    fn default() -> Self {
        Self::new()
    }
}

impl Decompressor {
    /// Create a new decompressor.
    pub fn new() -> Self {
        Self {
            bits: BitBuffer::new(),
            compression: CompressedBlock {
                litlen_table: Box::new([0; DEFAULT_LITLEN_TABLE_SIZE]),
                dist_table: Box::new([0; DEFAULT_DIST_TABLE_SIZE]),
                secondary_table: Vec::new(),
                dist_secondary_table: Vec::new(),
                eof_code: 0,
                eof_mask: 0,
                eof_bits: 0,
            },
            header: BlockHeader {
                hlit: 0,
                hdist: 0,
                hclen: 0,
                table: [0; 128],
                num_lengths_read: 0,
                code_lengths: [0; 320],
            },
            uncompressed_bytes_left: 0,
            queued_output: None,
            checksum: Adler32::new(),
            state: State::ZlibHeader,
            last_block: false,
            ignore_adler32: false,
            fixed_table: false,
        }
    }

    /// Ignore the checksum at the end of the stream.
    pub fn ignore_adler32(&mut self) {
        self.ignore_adler32 = true;
    }

    /// Decompresses a chunk of data.
    ///
    /// Returns the number of bytes read from `input` and the number of bytes written to `output`,
    /// or an error if the deflate stream is not valid. `input` is the compressed data. `output` is
    /// the buffer to write the decompressed data to, starting at index `output_position`.
    /// `end_of_input` indicates whether more data may be available in the future.
    ///
    /// The contents of `output` after `output_position` are ignored. However, this function may
    /// write additional data to `output` past what is indicated by the return value.
    ///
    /// When this function returns `Ok`, at least one of the following is true:
    /// - The input is fully consumed.
    /// - The output is full but there are more bytes to output.
    /// - The deflate stream is complete (and `is_done` will return true).
    ///
    /// # Panics
    ///
    /// This function will panic if `output_position` is out of bounds.
    pub fn read(
        &mut self,
        input: &[u8],
        output: &mut [u8],
        output_position: usize,
        end_of_input: bool,
    ) -> Result<(usize, usize), DecompressionError> {
        if let State::Done = self.state {
            return Ok((0, 0));
        }

        assert!(output_position <= output.len());

        let mut remaining_input = input;
        let mut output_index = output_position;

        if let Some(queued_output) = self.queued_output.take() {
            match queued_output {
                QueuedOutput::Rle { data, length } => {
                    let length: usize = length.into();
                    let n = length.min(output.len() - output_index);
                    output[output_index..][..n].fill(data);
                    output_index += n;
                    if let Ok(length) = NonZeroUsize::try_from(length - n) {
                        self.queued_output = Some(QueuedOutput::Rle { data, length });
                        return Ok((0, n));
                    }
                }
                QueuedOutput::Backref { dist, length } => {
                    let length: usize = length.into();
                    let n = length.min(output.len() - output_index);
                    for i in 0..n {
                        output[output_index + i] = output[output_index + i - dist];
                    }
                    output_index += n;
                    if let Ok(length) = NonZeroUsize::try_from(length - n) {
                        self.queued_output = Some(QueuedOutput::Backref { dist, length });
                        return Ok((0, n));
                    }
                }
            }
        }

        // Main decoding state machine.
        let mut last_state = None;
        while last_state != Some(self.state) {
            last_state = Some(self.state);
            match self.state {
                State::ZlibHeader => {
                    self.bits.fill_buffer(&mut remaining_input);
                    if self.bits.nbits < 16 {
                        break;
                    }

                    let input0 = self.bits.peek_bits(8);
                    let input1 = (self.bits.peek_bits(16) >> 8) & 0xff;
                    if input0 & 0x0f != 0x08
                        || (input0 & 0xf0) > 0x70
                        || input1 & 0x20 != 0
                        || ((input0 << 8) | input1) % 31 != 0
                    {
                        return Err(DecompressionError::BadZlibHeader);
                    }

                    self.bits.consume_bits(16);
                    self.state = State::BlockHeader;
                }
                State::BlockHeader => {
                    self.read_block_header(&mut remaining_input)?;
                }
                State::CodeLengthCodes => {
                    self.read_code_length_codes(&mut remaining_input)?;
                }
                State::CodeLengths => {
                    self.read_code_lengths(&mut remaining_input)?;
                }
                State::CompressedData => {
                    let (compresed_block_status, new_output_index) =
                        self.compression.read_compressed(
                            &mut self.bits,
                            &mut remaining_input,
                            output,
                            output_index,
                            &mut self.queued_output,
                        )?;
                    output_index = new_output_index;
                    if compresed_block_status == CompressedBlockStatus::ReachedEndOfBlock {
                        self.state = match self.last_block {
                            true => State::Checksum,
                            false => State::BlockHeader,
                        };
                    }
                }
                State::UncompressedData => {
                    // Drain any bytes from our buffer.
                    debug_assert_eq!(self.bits.nbits % 8, 0);
                    while self.bits.nbits > 0
                        && self.uncompressed_bytes_left > 0
                        && output_index < output.len()
                    {
                        output[output_index] = self.bits.peek_bits(8) as u8;
                        self.bits.consume_bits(8);
                        output_index += 1;
                        self.uncompressed_bytes_left -= 1;
                    }
                    // Buffer may contain one additional byte. Clear it to avoid confusion.
                    if self.bits.nbits == 0 {
                        self.bits.buffer = 0;
                    }

                    // Copy subsequent bytes directly from the input.
                    let copy_bytes = (self.uncompressed_bytes_left as usize)
                        .min(remaining_input.len())
                        .min(output.len() - output_index);
                    output[output_index..][..copy_bytes]
                        .copy_from_slice(&remaining_input[..copy_bytes]);
                    remaining_input = &remaining_input[copy_bytes..];
                    output_index += copy_bytes;
                    self.uncompressed_bytes_left -= copy_bytes as u16;

                    if self.uncompressed_bytes_left == 0 {
                        self.state = if self.last_block {
                            State::Checksum
                        } else {
                            State::BlockHeader
                        };
                    }
                }
                State::Checksum => {
                    self.bits.fill_buffer(&mut remaining_input);

                    let align_bits = self.bits.nbits % 8;
                    if self.bits.nbits >= 32 + align_bits {
                        self.checksum.write(&output[output_position..output_index]);
                        if align_bits != 0 {
                            self.bits.consume_bits(align_bits);
                        }
                        #[cfg(not(fuzzing))]
                        if !self.ignore_adler32
                            && (self.bits.peek_bits(32) as u32).swap_bytes()
                                != self.checksum.finish()
                        {
                            return Err(DecompressionError::WrongChecksum);
                        }
                        self.state = State::Done;
                        self.bits.consume_bits(32);
                        break;
                    }
                }
                State::Done => unreachable!(),
            }
        }

        if !self.ignore_adler32 && self.state != State::Done {
            self.checksum.write(&output[output_position..output_index]);
        }

        if self.state == State::Done || !end_of_input || output_index == output.len() {
            let input_left = remaining_input.len();
            Ok((input.len() - input_left, output_index - output_position))
        } else {
            Err(DecompressionError::InsufficientInput)
        }
    }

    /// Returns true if the decompressor has finished decompressing the input.
    pub fn is_done(&self) -> bool {
        self.state == State::Done
    }

    fn read_block_header(&mut self, remaining_input: &mut &[u8]) -> Result<(), DecompressionError> {
        self.bits.fill_buffer(remaining_input);
        if self.bits.nbits < 10 {
            return Ok(());
        }

        let start = self.bits.peek_bits(3);
        self.last_block = start & 1 != 0;
        match start >> 1 {
            0b00 => {
                let align_bits = (self.bits.nbits - 3) % 8;
                let header_bits = 3 + 32 + align_bits;
                if self.bits.nbits < header_bits {
                    return Ok(());
                }

                let len = (self.bits.peek_bits(align_bits + 19) >> (align_bits + 3)) as u16;
                let nlen = (self.bits.peek_bits(header_bits) >> (align_bits + 19)) as u16;
                if nlen != !len {
                    return Err(DecompressionError::InvalidUncompressedBlockLength);
                }

                self.state = State::UncompressedData;
                self.uncompressed_bytes_left = len;
                self.bits.consume_bits(header_bits);
                Ok(())
            }
            0b01 => {
                self.bits.consume_bits(3);

                // Check for an entirely empty blocks which can happen if there are "partial
                // flushes" in the deflate stream. With fixed huffman codes, the EOF symbol is
                // 7-bits of zeros so we peak ahead and see if the next 7-bits are all zero.
                if self.bits.peek_bits(7) == 0 {
                    self.bits.consume_bits(7);
                    if self.last_block {
                        self.state = State::Checksum;
                        return Ok(());
                    }

                    // At this point we've consumed the entire block and need to read the next block
                    // header. If tail call optimization were guaranteed, we could just recurse
                    // here. But without it, a long sequence of empty fixed-blocks might cause a
                    // stack overflow. Instead, we consume all empty blocks in a loop and then
                    // recurse. This is the only recursive call this function, and thus is safe.
                    while self.bits.nbits >= 10 && self.bits.peek_bits(10) == 0b010 {
                        self.bits.consume_bits(10);
                        self.bits.fill_buffer(remaining_input);
                    }
                    return self.read_block_header(remaining_input);
                }

                // Build decoding tables if the previous block wasn't also a fixed block.
                if !self.fixed_table {
                    self.fixed_table = true;
                    assert!(self.compression.litlen_table.len() >= FIXED_LITLEN_TABLE.len());
                    for chunk in self.compression.litlen_table.chunks_exact_mut(512) {
                        chunk.copy_from_slice(&FIXED_LITLEN_TABLE);
                    }
                    assert!(self.compression.dist_table.len() >= FIXED_DIST_TABLE.len());
                    for chunk in self.compression.dist_table.chunks_exact_mut(32) {
                        chunk.copy_from_slice(&FIXED_DIST_TABLE);
                    }
                    self.compression.eof_bits = 7;
                    self.compression.eof_code = 0;
                    self.compression.eof_mask = 0x7f;
                }

                self.state = State::CompressedData;
                Ok(())
            }
            0b10 => {
                if self.bits.nbits < 17 {
                    return Ok(());
                }

                self.header.hlit = (self.bits.peek_bits(8) >> 3) as usize + 257;
                self.header.hdist = (self.bits.peek_bits(13) >> 8) as usize + 1;
                self.header.hclen = (self.bits.peek_bits(17) >> 13) as usize + 4;
                if self.header.hlit > 286 {
                    return Err(DecompressionError::InvalidHlit);
                }
                if self.header.hdist > 30 {
                    return Err(DecompressionError::InvalidHdist);
                }

                self.bits.consume_bits(17);
                self.state = State::CodeLengthCodes;
                self.fixed_table = false;
                Ok(())
            }
            0b11 => Err(DecompressionError::InvalidBlockType),
            _ => unreachable!(),
        }
    }

    fn read_code_length_codes(
        &mut self,
        remaining_input: &mut &[u8],
    ) -> Result<(), DecompressionError> {
        self.bits.fill_buffer(remaining_input);
        if self.bits.nbits as usize + remaining_input.len() * 8 < 3 * self.header.hclen {
            return Ok(());
        }

        let mut code_length_lengths = [0; 19];
        for i in 0..self.header.hclen {
            code_length_lengths[CLCL_ORDER[i]] = self.bits.peek_bits(3) as u8;
            self.bits.consume_bits(3);

            // We need to refill the buffer after reading 3 * 18 = 54 bits since the buffer holds
            // between 56 and 63 bits total.
            if i == 17 {
                self.bits.fill_buffer(remaining_input);
            }
        }

        let mut codes = [0; 19];
        if !build_table(
            &code_length_lengths,
            &[],
            &mut codes,
            &mut self.header.table,
            &mut Vec::new(),
            false,
            false,
        ) {
            return Err(DecompressionError::BadCodeLengthHuffmanTree);
        }

        self.state = State::CodeLengths;
        self.header.num_lengths_read = 0;
        Ok(())
    }

    fn read_code_lengths(&mut self, remaining_input: &mut &[u8]) -> Result<(), DecompressionError> {
        let total_lengths = self.header.hlit + self.header.hdist;
        while self.header.num_lengths_read < total_lengths {
            self.bits.fill_buffer(remaining_input);
            if self.bits.nbits < 7 {
                return Ok(());
            }

            let code = self.bits.peek_bits(7);
            let entry = self.header.table[code as usize];
            let length = (entry & 0x7) as u8;
            let symbol = (entry >> 16) as u8;

            debug_assert!(length != 0);
            match symbol {
                0..=15 => {
                    self.header.code_lengths[self.header.num_lengths_read] = symbol;
                    self.header.num_lengths_read += 1;
                    self.bits.consume_bits(length);
                }
                16..=18 => {
                    let (base_repeat, extra_bits) = match symbol {
                        16 => (3, 2),
                        17 => (3, 3),
                        18 => (11, 7),
                        _ => unreachable!(),
                    };

                    if self.bits.nbits < length + extra_bits {
                        return Ok(());
                    }

                    let value = match symbol {
                        16 => {
                            self.header.code_lengths[self
                                .header
                                .num_lengths_read
                                .checked_sub(1)
                                .ok_or(DecompressionError::InvalidCodeLengthRepeat)?]
                            // TODO: is this right?
                        }
                        17 => 0,
                        18 => 0,
                        _ => unreachable!(),
                    };

                    let repeat =
                        (self.bits.peek_bits(length + extra_bits) >> length) as usize + base_repeat;
                    if self.header.num_lengths_read + repeat > total_lengths {
                        return Err(DecompressionError::InvalidCodeLengthRepeat);
                    }

                    for i in 0..repeat {
                        self.header.code_lengths[self.header.num_lengths_read + i] = value;
                    }
                    self.header.num_lengths_read += repeat;
                    self.bits.consume_bits(length + extra_bits);
                }
                _ => unreachable!(),
            }
        }

        self.header
            .code_lengths
            .copy_within(self.header.hlit..total_lengths, 288);
        for i in self.header.hlit..288 {
            self.header.code_lengths[i] = 0;
        }
        for i in 288 + self.header.hdist..320 {
            self.header.code_lengths[i] = 0;
        }

        self.compression
            .build_tables(self.header.hlit, &self.header.code_lengths)?;
        self.state = State::CompressedData;
        Ok(())
    }
}

impl<const LITLEN_TABLE_SIZE: usize, const DIST_TABLE_SIZE: usize>
    CompressedBlock<LITLEN_TABLE_SIZE, DIST_TABLE_SIZE>
{
    fn build_tables(&mut self, hlit: usize, code_lengths: &[u8]) -> Result<(), DecompressionError> {
        // If there is no code assigned for the EOF symbol then the bitstream is invalid.
        if code_lengths[256] == 0 {
            // TODO: Return a dedicated error in this case.
            return Err(DecompressionError::BadLiteralLengthHuffmanTree);
        }

        let mut codes = [0; 288];
        self.secondary_table.clear();
        if !huffman::build_table(
            &code_lengths[..hlit],
            &LITLEN_TABLE_ENTRIES,
            &mut codes[..hlit],
            &mut *self.litlen_table,
            &mut self.secondary_table,
            false,
            true,
        ) {
            return Err(DecompressionError::BadCodeLengthHuffmanTree);
        }

        self.eof_code = codes[256];
        self.eof_mask = (1 << code_lengths[256]) - 1;
        self.eof_bits = code_lengths[256];

        // Build the distance code table.
        let lengths = &code_lengths[288..320];
        if lengths == [0; 32] {
            self.dist_table.fill(0);
        } else {
            let mut dist_codes = [0; 32];
            if !huffman::build_table(
                lengths,
                &tables::DISTANCE_TABLE_ENTRIES,
                &mut dist_codes,
                &mut *self.dist_table,
                &mut self.dist_secondary_table,
                true,
                false,
            ) {
                return Err(DecompressionError::BadDistanceHuffmanTree);
            }
        }

        Ok(())
    }

    /// Returns:
    /// - Whether this compressed block ended or not
    /// - The new value of `output_index`
    fn read_compressed(
        &self,
        bit_buffer: &mut BitBuffer,
        remaining_input: &mut &[u8],
        output: &mut [u8],
        mut output_index: usize,
        queued_output: &mut Option<QueuedOutput>,
    ) -> Result<(CompressedBlockStatus, usize), DecompressionError> {
        // `litlen_table_mask` (and `dist_table_mask`) calculation assumes that `LITLEN_TABLE_SIZE`
        // (or `DIST_TABLE_SIZE`) is a power of two.
        assert!(LITLEN_TABLE_SIZE.count_ones() == 1);
        assert!(DIST_TABLE_SIZE.count_ones() == 1);
        let litlen_table_mask = (LITLEN_TABLE_SIZE as u64) - 1;
        let litlen_table_bits = LITLEN_TABLE_SIZE.trailing_zeros();
        let dist_table_mask = (DIST_TABLE_SIZE as u64) - 1;
        let dist_table_bits = DIST_TABLE_SIZE.trailing_zeros();
        // Lower bound on table sizes, because 1a) RFC1951 uses at most 15 bits for codewords and
        // 1b) we can fit at most 8 bits of `overflow_bits_mask` in the last byte of a primary
        // table entry.
        assert!(litlen_table_bits + 8 >= 15);
        assert!(dist_table_bits + 8 >= 15);

        // Fast decoding loop.
        //
        // This loop is optimized for speed and is the main decoding loop for the decompressor,
        // which is used when there are at least 8 bytes of input and output data available. It
        // assumes that the bitbuffer is full (nbits >= 56) and that litlen_entry has been loaded.
        //
        // These assumptions enable a few optimizations:
        // - Nearly all checks for nbits are avoided.
        // - Checking the input size is optimized out in the refill function call.
        // - The litlen_entry for the next loop iteration can be loaded in parallel with refilling
        //   the bit buffer. This is because when the input is non-empty, the bit buffer actually
        //   has 64-bits of valid data (even though nbits will be in 56..=63).
        bit_buffer.fill_buffer(remaining_input);
        let mut litlen_entry = self.litlen_table[(bit_buffer.buffer & litlen_table_mask) as usize];
        while output_index + 8 <= output.len() && remaining_input.len() >= 8 {
            // First check whether the next symbol is a literal. This code does up to 2 additional
            // table lookups to decode more literals.
            let mut bits;
            let mut litlen_code_bits = litlen_entry as u8;
            if litlen_entry & LITERAL_ENTRY != 0 {
                let litlen_entry2 = self.litlen_table
                    [((bit_buffer.buffer >> litlen_code_bits) & litlen_table_mask) as usize];
                let litlen_code_bits2 = litlen_entry2 as u8;
                let litlen_entry3 = self.litlen_table[((bit_buffer.buffer
                    >> (litlen_code_bits + litlen_code_bits2))
                    & litlen_table_mask)
                    as usize];
                let litlen_code_bits3 = litlen_entry3 as u8;
                let litlen_entry4 = self.litlen_table[((bit_buffer.buffer
                    >> (litlen_code_bits + litlen_code_bits2 + litlen_code_bits3))
                    & litlen_table_mask)
                    as usize];

                let advance_output_bytes = ((litlen_entry & 0xf00) >> 8) as usize;
                output[output_index] = (litlen_entry >> 16) as u8;
                output[output_index + 1] = (litlen_entry >> 24) as u8;
                output_index += advance_output_bytes;

                if litlen_entry2 & LITERAL_ENTRY != 0 {
                    let advance_output_bytes2 = ((litlen_entry2 & 0xf00) >> 8) as usize;
                    output[output_index] = (litlen_entry2 >> 16) as u8;
                    output[output_index + 1] = (litlen_entry2 >> 24) as u8;
                    output_index += advance_output_bytes2;

                    if litlen_entry3 & LITERAL_ENTRY != 0 {
                        let advance_output_bytes3 = ((litlen_entry3 & 0xf00) >> 8) as usize;
                        output[output_index] = (litlen_entry3 >> 16) as u8;
                        output[output_index + 1] = (litlen_entry3 >> 24) as u8;
                        output_index += advance_output_bytes3;

                        litlen_entry = litlen_entry4;
                        bit_buffer
                            .consume_bits(litlen_code_bits + litlen_code_bits2 + litlen_code_bits3);
                        bit_buffer.fill_buffer(remaining_input);
                        continue;
                    } else {
                        bit_buffer.consume_bits(litlen_code_bits + litlen_code_bits2);
                        litlen_entry = litlen_entry3;
                        litlen_code_bits = litlen_code_bits3;
                        bit_buffer.fill_buffer(remaining_input);
                        bits = bit_buffer.buffer;
                    }
                } else {
                    bit_buffer.consume_bits(litlen_code_bits);
                    bits = bit_buffer.buffer;
                    litlen_entry = litlen_entry2;
                    litlen_code_bits = litlen_code_bits2;
                    if bit_buffer.nbits < 48 {
                        bit_buffer.fill_buffer(remaining_input);
                    }
                }
            } else {
                bits = bit_buffer.buffer;
            }

            // The next symbol is either a 13+ bit literal, back-reference, or an EOF symbol.
            let (length_base, length_extra_bits, litlen_code_bits) =
                if litlen_entry & EXCEPTIONAL_ENTRY == 0 {
                    (
                        litlen_entry >> 16,
                        (litlen_entry >> 8) as u8,
                        litlen_code_bits,
                    )
                } else if litlen_entry & SECONDARY_TABLE_ENTRY != 0 {
                    let secondary_table_index = (litlen_entry >> 16)
                        + ((bits >> litlen_table_bits) as u32 & (litlen_entry & 0xff));
                    let secondary_entry = self.secondary_table[secondary_table_index as usize];
                    let litlen_symbol = secondary_entry >> 4;
                    let litlen_code_bits = (secondary_entry & 0xf) as u8;

                    match litlen_symbol {
                        0..=255 => {
                            bit_buffer.consume_bits(litlen_code_bits);
                            litlen_entry =
                                self.litlen_table[(bit_buffer.buffer & litlen_table_mask) as usize];
                            bit_buffer.fill_buffer(remaining_input);
                            output[output_index] = litlen_symbol as u8;
                            output_index += 1;
                            continue;
                        }
                        256 => {
                            bit_buffer.consume_bits(litlen_code_bits);
                            return Ok((CompressedBlockStatus::ReachedEndOfBlock, output_index));
                        }
                        _ => (
                            LEN_SYM_TO_LEN_BASE[litlen_symbol as usize - 257] as u32,
                            LEN_SYM_TO_LEN_EXTRA[litlen_symbol as usize - 257],
                            litlen_code_bits,
                        ),
                    }
                } else if litlen_code_bits == 0 {
                    return Err(DecompressionError::InvalidLiteralLengthCode);
                } else {
                    bit_buffer.consume_bits(litlen_code_bits);
                    return Ok((CompressedBlockStatus::ReachedEndOfBlock, output_index));
                };
            bits >>= litlen_code_bits;

            let length_extra_mask = (1 << length_extra_bits) - 1;
            let length = length_base as usize + (bits & length_extra_mask) as usize;
            bits >>= length_extra_bits;

            let dist_entry = self.dist_table[(bits & dist_table_mask) as usize];
            let (dist_base, dist_extra_bits, dist_code_bits) = if dist_entry & LITERAL_ENTRY != 0 {
                (
                    (dist_entry >> 16) as u16,
                    (dist_entry >> 8) as u8 & 0xf,
                    dist_entry as u8,
                )
            } else if dist_entry >> 8 == 0 {
                return Err(DecompressionError::InvalidDistanceCode);
            } else {
                let secondary_table_index =
                    (dist_entry >> 16) + ((bits >> dist_table_bits) as u32 & (dist_entry & 0xff));
                let secondary_entry = self.dist_secondary_table[secondary_table_index as usize];
                let dist_symbol = (secondary_entry >> 4) as usize;
                if dist_symbol >= 30 {
                    return Err(DecompressionError::InvalidDistanceCode);
                }

                (
                    DIST_SYM_TO_DIST_BASE[dist_symbol],
                    DIST_SYM_TO_DIST_EXTRA[dist_symbol],
                    (secondary_entry & 0xf) as u8,
                )
            };
            bits >>= dist_code_bits;

            let dist = dist_base as usize + (bits & ((1 << dist_extra_bits) - 1)) as usize;
            if dist > output_index {
                return Err(DecompressionError::DistanceTooFarBack);
            }

            bit_buffer.consume_bits(
                litlen_code_bits + length_extra_bits + dist_code_bits + dist_extra_bits,
            );
            bit_buffer.fill_buffer(remaining_input);
            litlen_entry = self.litlen_table[(bit_buffer.buffer & litlen_table_mask) as usize];

            let copy_length = length.min(output.len() - output_index);
            if dist == 1 {
                let last = output[output_index - 1];
                output[output_index..][..copy_length].fill(last);

                if let Ok(length) = NonZeroUsize::try_from(length - copy_length) {
                    *queued_output = Some(QueuedOutput::Rle { data: last, length });
                    output_index = output.len();
                    break;
                }
            } else if output_index + length + 15 <= output.len() {
                let start = output_index - dist;
                output.copy_within(start..start + 16, output_index);

                if length > 16 || dist < 16 {
                    for i in (0..length).step_by(dist.min(16)).skip(1) {
                        output.copy_within(start + i..start + i + 16, output_index + i);
                    }
                }
            } else {
                if dist < copy_length {
                    for i in 0..copy_length {
                        output[output_index + i] = output[output_index + i - dist];
                    }
                } else {
                    output.copy_within(
                        output_index - dist..output_index + copy_length - dist,
                        output_index,
                    )
                }

                if let Ok(length) = NonZeroUsize::try_from(length - copy_length) {
                    *queued_output = Some(QueuedOutput::Backref { dist, length });
                    output_index = output.len();
                    break;
                }
            }
            output_index += copy_length;
        }

        // Careful decoding loop.
        //
        // This loop processes the remaining input when we're too close to the end of the input or
        // output to use the fast loop.
        loop {
            bit_buffer.fill_buffer(remaining_input);
            if output_index == output.len() {
                break;
            }

            let mut bits = bit_buffer.buffer;
            let litlen_entry = self.litlen_table[(bits & litlen_table_mask) as usize];
            let litlen_code_bits = litlen_entry as u8;

            if litlen_entry & LITERAL_ENTRY != 0 {
                // Fast path: the next symbol is <= `litlen_table_bits` bits and a literal, the
                // table specifies the output bytes and we can directly write them to the output
                // buffer.
                let advance_output_bytes = ((litlen_entry & 0xf00) >> 8) as usize;

                if bit_buffer.nbits < litlen_code_bits {
                    break;
                } else if output_index + 1 < output.len() {
                    output[output_index] = (litlen_entry >> 16) as u8;
                    output[output_index + 1] = (litlen_entry >> 24) as u8;
                    output_index += advance_output_bytes;
                    bit_buffer.consume_bits(litlen_code_bits);
                    continue;
                } else if output_index + advance_output_bytes == output.len() {
                    debug_assert_eq!(advance_output_bytes, 1);
                    output[output_index] = (litlen_entry >> 16) as u8;
                    output_index += 1;
                    bit_buffer.consume_bits(litlen_code_bits);
                    break;
                } else {
                    debug_assert_eq!(advance_output_bytes, 2);
                    output[output_index] = (litlen_entry >> 16) as u8;
                    *queued_output = Some(QueuedOutput::Rle {
                        data: (litlen_entry >> 24) as u8,
                        length: NonZeroUsize::new(1).unwrap(),
                    });
                    output_index += 1;
                    bit_buffer.consume_bits(litlen_code_bits);
                    break;
                }
            }

            let (length_base, length_extra_bits, litlen_code_bits) =
                if litlen_entry & EXCEPTIONAL_ENTRY == 0 {
                    (
                        litlen_entry >> 16,
                        (litlen_entry >> 8) as u8,
                        litlen_code_bits,
                    )
                } else if litlen_entry & SECONDARY_TABLE_ENTRY != 0 {
                    let secondary_table_index = (litlen_entry >> 16)
                        + ((bits >> litlen_table_bits) as u32 & (litlen_entry & 0xff));
                    let secondary_entry = self.secondary_table[secondary_table_index as usize];
                    let litlen_symbol = secondary_entry >> 4;
                    let litlen_code_bits = (secondary_entry & 0xf) as u8;

                    if bit_buffer.nbits < litlen_code_bits {
                        break;
                    } else if litlen_symbol < 256 {
                        bit_buffer.consume_bits(litlen_code_bits);
                        output[output_index] = litlen_symbol as u8;
                        output_index += 1;
                        continue;
                    } else if litlen_symbol == 256 {
                        bit_buffer.consume_bits(litlen_code_bits);
                        return Ok((CompressedBlockStatus::ReachedEndOfBlock, output_index));
                    }

                    (
                        LEN_SYM_TO_LEN_BASE[litlen_symbol as usize - 257] as u32,
                        LEN_SYM_TO_LEN_EXTRA[litlen_symbol as usize - 257],
                        litlen_code_bits,
                    )
                } else if litlen_code_bits == 0 {
                    return Err(DecompressionError::InvalidLiteralLengthCode);
                } else {
                    if bit_buffer.nbits < litlen_code_bits {
                        break;
                    }
                    bit_buffer.consume_bits(litlen_code_bits);
                    return Ok((CompressedBlockStatus::ReachedEndOfBlock, output_index));
                };
            bits >>= litlen_code_bits;

            let length_extra_mask = (1 << length_extra_bits) - 1;
            let length = length_base as usize + (bits & length_extra_mask) as usize;
            bits >>= length_extra_bits;

            let dist_entry = self.dist_table[(bits & dist_table_mask) as usize];
            let (dist_base, dist_extra_bits, dist_code_bits) = if dist_entry & LITERAL_ENTRY != 0 {
                (
                    (dist_entry >> 16) as u16,
                    (dist_entry >> 8) as u8 & 0xf,
                    dist_entry as u8,
                )
            } else if bit_buffer.nbits
                > litlen_code_bits + length_extra_bits + dist_table_bits as u8
            {
                if dist_entry >> 8 == 0 {
                    return Err(DecompressionError::InvalidDistanceCode);
                }

                let secondary_table_index =
                    (dist_entry >> 16) + ((bits >> dist_table_bits) as u32 & (dist_entry & 0xff));
                let secondary_entry = self.dist_secondary_table[secondary_table_index as usize];
                let dist_symbol = (secondary_entry >> 4) as usize;
                if dist_symbol >= 30 {
                    return Err(DecompressionError::InvalidDistanceCode);
                }

                (
                    DIST_SYM_TO_DIST_BASE[dist_symbol],
                    DIST_SYM_TO_DIST_EXTRA[dist_symbol],
                    (secondary_entry & 0xf) as u8,
                )
            } else {
                break;
            };
            bits >>= dist_code_bits;

            let dist = dist_base as usize + (bits & ((1 << dist_extra_bits) - 1)) as usize;
            let total_bits =
                litlen_code_bits + length_extra_bits + dist_code_bits + dist_extra_bits;

            if bit_buffer.nbits < total_bits {
                break;
            } else if dist > output_index {
                return Err(DecompressionError::DistanceTooFarBack);
            }

            bit_buffer.consume_bits(total_bits);

            let copy_length = length.min(output.len() - output_index);
            if dist == 1 {
                let last = output[output_index - 1];
                output[output_index..][..copy_length].fill(last);

                if let Ok(length) = NonZeroUsize::try_from(length - copy_length) {
                    *queued_output = Some(QueuedOutput::Rle { data: last, length });
                    output_index = output.len();
                    break;
                }
            } else if output_index + length + 15 <= output.len() {
                let start = output_index - dist;
                output.copy_within(start..start + 16, output_index);

                if length > 16 || dist < 16 {
                    for i in (0..length).step_by(dist.min(16)).skip(1) {
                        output.copy_within(start + i..start + i + 16, output_index + i);
                    }
                }
            } else {
                if dist < copy_length {
                    for i in 0..copy_length {
                        output[output_index + i] = output[output_index + i - dist];
                    }
                } else {
                    output.copy_within(
                        output_index - dist..output_index + copy_length - dist,
                        output_index,
                    )
                }

                if let Ok(length) = NonZeroUsize::try_from(length - copy_length) {
                    *queued_output = Some(QueuedOutput::Backref { dist, length });
                    output_index = output.len();
                    break;
                }
            }
            output_index += copy_length;
        }

        if queued_output.is_none()
            && bit_buffer.nbits >= 15
            && bit_buffer.peek_bits(15) as u16 & self.eof_mask == self.eof_code
        {
            bit_buffer.consume_bits(self.eof_bits);
            return Ok((CompressedBlockStatus::ReachedEndOfBlock, output_index));
        }

        Ok((CompressedBlockStatus::MoreDataPresent, output_index))
    }
}

#[derive(Debug)]
struct BitBuffer {
    buffer: u64,
    nbits: u8,
}

impl BitBuffer {
    fn new() -> Self {
        Self {
            buffer: 0,
            nbits: 0,
        }
    }

    fn fill_buffer(&mut self, input: &mut &[u8]) {
        if input.len() >= 8 {
            let mut bits = self.nbits & 63; // limits `bits` to 63 or less, elides bounds checks
            self.buffer |= u64::from_le_bytes(input[..8].try_into().unwrap()) << bits;
            *input = &input[((63 - bits) / 8) as usize..];
            bits |= 56;
            self.nbits = bits;
        } else {
            let nbytes = input.len().min((63 - self.nbits as usize) / 8);
            let mut input_data = [0; 8];
            input_data[..nbytes].copy_from_slice(&input[..nbytes]);
            self.buffer |= u64::from_le_bytes(input_data)
                .checked_shl(self.nbits as u32)
                .unwrap_or(0);
            self.nbits += nbytes as u8 * 8;
            *input = &input[nbytes..];
        }
    }

    fn peek_bits(&mut self, nbits: u8) -> u64 {
        debug_assert!(nbits <= 56 && nbits <= self.nbits);
        self.buffer & ((1u64 << nbits) - 1)
    }

    fn consume_bits(&mut self, nbits: u8) {
        debug_assert!(self.nbits >= nbits);
        self.buffer >>= nbits;
        self.nbits -= nbits;
    }
}

#[derive(Debug)]
enum QueuedOutput {
    Rle { data: u8, length: NonZeroUsize },
    Backref { dist: usize, length: NonZeroUsize },
}

#[derive(Debug, Eq, PartialEq)]
enum CompressedBlockStatus {
    MoreDataPresent,
    ReachedEndOfBlock,
}

/// Decompress the given data.
pub fn decompress_to_vec(input: &[u8]) -> Result<Vec<u8>, DecompressionError> {
    match decompress_to_vec_bounded(input, usize::MAX) {
        Ok(output) => Ok(output),
        Err(BoundedDecompressionError::DecompressionError { inner }) => Err(inner),
        Err(BoundedDecompressionError::OutputTooLarge { .. }) => {
            unreachable!("Impossible to allocate more than isize::MAX bytes")
        }
    }
}

/// An error encountered while decompressing a deflate stream given a bounded maximum output.
pub enum BoundedDecompressionError {
    /// The input is not a valid deflate stream.
    DecompressionError {
        /// The underlying error.
        inner: DecompressionError,
    },

    /// The output is too large.
    OutputTooLarge {
        /// The output decoded so far.
        partial_output: Vec<u8>,
    },
}
impl From<DecompressionError> for BoundedDecompressionError {
    fn from(inner: DecompressionError) -> Self {
        BoundedDecompressionError::DecompressionError { inner }
    }
}

/// Decompress the given data, returning an error if the output is larger than
/// `maxlen` bytes.
pub fn decompress_to_vec_bounded(
    input: &[u8],
    maxlen: usize,
) -> Result<Vec<u8>, BoundedDecompressionError> {
    let mut decoder = Decompressor::new();
    let mut output = vec![0; 1024.min(maxlen)];
    let mut input_index = 0;
    let mut output_index = 0;
    loop {
        let (consumed, produced) =
            decoder.read(&input[input_index..], &mut output, output_index, true)?;
        input_index += consumed;
        output_index += produced;
        if decoder.is_done() || output_index == maxlen {
            break;
        }
        output.resize((output_index + 32 * 1024).min(maxlen), 0);
    }
    output.resize(output_index, 0);

    if decoder.is_done() {
        Ok(output)
    } else {
        Err(BoundedDecompressionError::OutputTooLarge {
            partial_output: output,
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::tables::{LENGTH_TO_LEN_EXTRA, LENGTH_TO_SYMBOL};

    use super::*;
    use rand::Rng;

    fn roundtrip(data: &[u8]) {
        let compressed = crate::compress_to_vec(data);
        let decompressed = decompress_to_vec(&compressed).unwrap();
        assert_eq!(&decompressed, data);
    }

    fn roundtrip_miniz_oxide(data: &[u8]) {
        let compressed = miniz_oxide::deflate::compress_to_vec_zlib(data, 3);
        let decompressed = decompress_to_vec(&compressed).unwrap();
        assert_eq!(decompressed.len(), data.len());
        for (i, (a, b)) in decompressed.chunks(1).zip(data.chunks(1)).enumerate() {
            assert_eq!(a, b, "chunk {}..{}", i, i + 1);
        }
        assert_eq!(&decompressed, data);
    }

    #[allow(unused)]
    fn compare_decompression(data: &[u8]) {
        // let decompressed0 = flate2::read::ZlibDecoder::new(std::io::Cursor::new(&data))
        //     .bytes()
        //     .collect::<Result<Vec<_>, _>>()
        //     .unwrap();
        let decompressed = decompress_to_vec(data).unwrap();
        let decompressed2 = miniz_oxide::inflate::decompress_to_vec_zlib(data).unwrap();
        for i in 0..decompressed.len().min(decompressed2.len()) {
            if decompressed[i] != decompressed2[i] {
                panic!(
                    "mismatch at index {} {:?} {:?}",
                    i,
                    &decompressed[i.saturating_sub(1)..(i + 16).min(decompressed.len())],
                    &decompressed2[i.saturating_sub(1)..(i + 16).min(decompressed2.len())]
                );
            }
        }
        if decompressed != decompressed2 {
            panic!(
                "length mismatch {} {} {:x?}",
                decompressed.len(),
                decompressed2.len(),
                &decompressed2[decompressed.len()..][..16]
            );
        }
        //assert_eq!(decompressed, decompressed2);
    }

    #[test]
    fn tables() {
        for (i, &bits) in LEN_SYM_TO_LEN_EXTRA.iter().enumerate() {
            let len_base = LEN_SYM_TO_LEN_BASE[i];
            for j in 0..(1 << bits) {
                if i == 27 && j == 31 {
                    continue;
                }
                assert_eq!(LENGTH_TO_LEN_EXTRA[len_base + j - 3], bits, "{} {}", i, j);
                assert_eq!(
                    LENGTH_TO_SYMBOL[len_base + j - 3],
                    i as u16 + 257,
                    "{} {}",
                    i,
                    j
                );
            }
        }
    }

    #[test]
    fn fixed_tables() {
        let mut compression = CompressedBlock {
            litlen_table: Box::new([0; DEFAULT_LITLEN_TABLE_SIZE]),
            dist_table: Box::new([0; DEFAULT_DIST_TABLE_SIZE]),
            secondary_table: Vec::new(),
            dist_secondary_table: Vec::new(),
            eof_code: 0,
            eof_mask: 0,
            eof_bits: 0,
        };
        compression.build_tables(288, &FIXED_CODE_LENGTHS).unwrap();

        assert_eq!(compression.litlen_table[..512], FIXED_LITLEN_TABLE);
        assert_eq!(compression.dist_table[..32], FIXED_DIST_TABLE);
    }

    #[test]
    fn it_works() {
        roundtrip(b"Hello world!");
    }

    #[test]
    fn constant() {
        roundtrip_miniz_oxide(&[0; 50]);
        roundtrip_miniz_oxide(&vec![5; 2048]);
        roundtrip_miniz_oxide(&vec![128; 2048]);
        roundtrip_miniz_oxide(&vec![254; 2048]);
    }

    #[test]
    fn random() {
        let mut rng = rand::thread_rng();
        let mut data = vec![0; 50000];
        for _ in 0..10 {
            for byte in &mut data {
                *byte = rng.gen::<u8>() % 5;
            }
            println!("Random data: {:?}", data);
            roundtrip_miniz_oxide(&data);
        }
    }

    #[test]
    fn ignore_adler32() {
        let mut compressed = crate::compress_to_vec(b"Hello world!");
        let last_byte = compressed.len() - 1;
        compressed[last_byte] = compressed[last_byte].wrapping_add(1);

        match decompress_to_vec(&compressed) {
            Err(DecompressionError::WrongChecksum) => {}
            r => panic!("expected WrongChecksum, got {:?}", r),
        }

        let mut decompressor = Decompressor::new();
        decompressor.ignore_adler32();
        let mut decompressed = vec![0; 1024];
        let decompressed_len = decompressor
            .read(&compressed, &mut decompressed, 0, true)
            .unwrap()
            .1;
        assert_eq!(&decompressed[..decompressed_len], b"Hello world!");
    }

    #[test]
    fn checksum_after_eof() {
        let input = b"Hello world!";
        let compressed = crate::compress_to_vec(input);

        let mut decompressor = Decompressor::new();
        let mut decompressed = vec![0; 1024];
        let (input_consumed, output_written) = decompressor
            .read(
                &compressed[..compressed.len() - 1],
                &mut decompressed,
                0,
                false,
            )
            .unwrap();
        assert_eq!(output_written, input.len());
        assert_eq!(input_consumed, compressed.len() - 1);

        let (input_consumed, output_written) = decompressor
            .read(
                &compressed[input_consumed..],
                &mut decompressed[..output_written],
                output_written,
                true,
            )
            .unwrap();
        assert!(decompressor.is_done());
        assert_eq!(input_consumed, 1);
        assert_eq!(output_written, 0);

        assert_eq!(&decompressed[..input.len()], input);
    }

    #[test]
    fn zero_length() {
        let mut compressed = crate::compress_to_vec(b"").to_vec();

        // Splice in zero-length non-compressed blocks.
        for _ in 0..10 {
            println!("compressed len: {}", compressed.len());
            compressed.splice(2..2, [0u8, 0, 0, 0xff, 0xff].into_iter());
        }

        // Ensure that the full input is decompressed, regardless of whether
        // `end_of_input` is set.
        for end_of_input in [true, false] {
            let mut decompressor = Decompressor::new();
            let (input_consumed, output_written) = decompressor
                .read(&compressed, &mut [], 0, end_of_input)
                .unwrap();

            assert!(decompressor.is_done());
            assert_eq!(input_consumed, compressed.len());
            assert_eq!(output_written, 0);
        }
    }

    mod test_utils;
    use tables::FIXED_CODE_LENGTHS;
    use test_utils::{decompress_by_chunks, TestDecompressionError};

    fn verify_no_sensitivity_to_input_chunking(
        input: &[u8],
    ) -> Result<Vec<u8>, TestDecompressionError> {
        let r_whole = decompress_by_chunks(input, vec![input.len()], false);
        let r_bytewise = decompress_by_chunks(input, std::iter::repeat(1), false);
        assert_eq!(r_whole, r_bytewise);
        r_whole // Returning an arbitrary result, since this is equal to `r_bytewise`.
    }

    /// This is a regression test found by the `buf_independent` fuzzer from the `png` crate.  When
    /// this test case was found, the results were unexpectedly different when 1) decompressing the
    /// whole input (successful result) vs 2) decompressing byte-by-byte
    /// (`Err(InvalidDistanceCode)`).
    #[test]
    fn test_input_chunking_sensitivity_when_handling_distance_codes() {
        let result = verify_no_sensitivity_to_input_chunking(include_bytes!(
            "../tests/input-chunking-sensitivity-example1.zz"
        ))
        .unwrap();
        assert_eq!(result.len(), 281);
        assert_eq!(simd_adler32::adler32(&result.as_slice()), 751299);
    }

    /// This is a regression test found by the `inflate_bytewise3` fuzzer from the `fdeflate`
    /// crate.  When this test case was found, the results were unexpectedly different when 1)
    /// decompressing the whole input (`Err(DistanceTooFarBack)`) vs 2) decompressing byte-by-byte
    /// (successful result)`).
    #[test]
    fn test_input_chunking_sensitivity_when_no_end_of_block_symbol_example1() {
        let err = verify_no_sensitivity_to_input_chunking(include_bytes!(
            "../tests/input-chunking-sensitivity-example2.zz"
        ))
        .unwrap_err();
        assert_eq!(
            err,
            TestDecompressionError::ProdError(DecompressionError::BadLiteralLengthHuffmanTree)
        );
    }

    /// This is a regression test found by the `inflate_bytewise3` fuzzer from the `fdeflate`
    /// crate.  When this test case was found, the results were unexpectedly different when 1)
    /// decompressing the whole input (`Err(InvalidDistanceCode)`) vs 2) decompressing byte-by-byte
    /// (successful result)`).
    #[test]
    fn test_input_chunking_sensitivity_when_no_end_of_block_symbol_example2() {
        let err = verify_no_sensitivity_to_input_chunking(include_bytes!(
            "../tests/input-chunking-sensitivity-example3.zz"
        ))
        .unwrap_err();
        assert_eq!(
            err,
            TestDecompressionError::ProdError(DecompressionError::BadLiteralLengthHuffmanTree)
        );
    }
}
