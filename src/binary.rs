//! The byte substrate shared by the compiler's two content-addressed wire codecs:
//! `store::codec` (the `def` frame, over anonymous Core) and `eval::kont` (the
//! `kont` frame, over the interpreter's runtime state). The two formats are
//! distinct and stay in their own homes; only the byte machinery lives here: LEB128
//! varints (unsigned and zigzag-signed), length-bounded blobs and strings,
//! fixed-width scalars, table-index lookups, and the hostile-input discipline (a
//! varint byte cap, a length bound, truncation and range checks) that keeps every
//! decode total.
//!
//! This restates, in the compiler, the discipline `lib/std/Wire.pr` states at the
//! Prism level: a varint is capped so a hostile all-continuation run cannot read
//! forever, and a length prefix is bounded so a hostile count cannot force
//! unbounded work. The schemas that ride this substrate, their tag values, and
//! their envelope layouts stay 100% in the two codecs.

use crate::store::CodecError;

// A varint is capped so a hostile all-continuation run cannot read forever, and a
// length prefix is bounded so a hostile count cannot force unbounded work.
pub(crate) const VARINT_MAX_BYTES: usize = 10;
const VARINT_CONT: u8 = 0x80;
const VARINT_LOW: u64 = 0x7f;
pub(crate) const WIRE_LEN_MAX: u64 = 1 << 20;

// The node table and the reconstructed graph are both bounded: a table larger than
// this, or a reconstruction that expands past this many nodes (a shared-DAG
// blow-up), is rejected rather than allowed to exhaust memory. Both codecs size
// their node tables and reconstruction budgets from here.
pub(crate) const MAX_NODES: u64 = 1 << 20;
pub(crate) const MAX_EXPANSION: usize = 1 << 22;

// ------------------------------- writing ----------------------------------

pub(crate) fn put_uvarint(out: &mut Vec<u8>, mut n: u64) {
    loop {
        let lo = (n & VARINT_LOW) as u8;
        n >>= 7;
        if n == 0 {
            out.push(lo);
            return;
        }
        out.push(lo | VARINT_CONT);
    }
}

// Zigzag maps a signed integer to an unsigned one so small negatives stay small
// under LEB128. The casts reinterpret the bit pattern by design, not a lossy
// conversion.
#[allow(clippy::cast_sign_loss)]
const fn zigzag(x: i64) -> u64 {
    ((x << 1) ^ (x >> 63)) as u64
}

#[allow(clippy::cast_possible_wrap)]
const fn unzigzag(z: u64) -> i64 {
    ((z >> 1) as i64) ^ -((z & 1) as i64)
}

pub(crate) fn put_svarint(out: &mut Vec<u8>, x: i64) {
    put_uvarint(out, zigzag(x));
}

pub(crate) fn put_str(out: &mut Vec<u8>, s: &str) {
    put_uvarint(out, s.len() as u64);
    out.extend_from_slice(s.as_bytes());
}

pub(crate) fn put_indices(out: &mut Vec<u8>, idxs: &[u32]) {
    put_uvarint(out, idxs.len() as u64);
    for i in idxs {
        put_uvarint(out, u64::from(*i));
    }
}

// ---------------------------- table numbering ------------------------------

/// The wire number of a table entry: its position in an ordered table that is the
/// single source of truth for the numbering. Each codec keeps its own tables (op
/// families, node tags) and numbers them through here, so encode and decode cannot
/// drift. Panics on an entry absent from its table: a codec bug on trusted input
/// (a new enum variant that was not appended), never a hostile-input path.
pub(crate) fn to_wire<T: PartialEq + Copy>(table: &[T], entry: T) -> u64 {
    table
        .iter()
        .position(|x| *x == entry)
        .map(|i| i as u64)
        .expect("operator missing from codec table (append it)")
}

/// The table entry a wire number names, the inverse of [`to_wire`], and the shared
/// tag-byte-to-variant lookup: a byte out of the table's range is rejected as
/// [`CodecError::Malformed`] rather than misread.
///
/// # Errors
/// [`CodecError::Malformed`] when the number is not a valid index into `table`.
pub(crate) fn from_wire<T: Copy>(table: &[T], n: u64) -> Result<T, CodecError> {
    usize::try_from(n)
        .ok()
        .and_then(|i| table.get(i))
        .copied()
        .ok_or(CodecError::Malformed)
}

// ------------------------------- reading ----------------------------------

/// A cursor over an untrusted byte frame. Every read is bounds- and range-checked,
/// so a decode over hostile bytes ends in a [`CodecError`], never a panic or an
/// over-read.
pub(crate) struct Reader<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl<'a> Reader<'a> {
    pub(crate) const fn new(buf: &'a [u8]) -> Self {
        Self { buf, pos: 0 }
    }

    // Whether every byte has been consumed, the trailing-byte check a total decoder
    // performs before it trusts a frame.
    pub(crate) const fn at_end(&self) -> bool {
        self.pos == self.buf.len()
    }

    pub(crate) fn byte(&mut self) -> Result<u8, CodecError> {
        let b = *self.buf.get(self.pos).ok_or(CodecError::Truncated)?;
        self.pos += 1;
        Ok(b)
    }

    pub(crate) fn uvarint(&mut self) -> Result<u64, CodecError> {
        let mut acc: u64 = 0;
        let mut shift = 0;
        for _ in 0..VARINT_MAX_BYTES {
            let b = self.byte()?;
            acc |= (u64::from(b) & VARINT_LOW) << shift;
            if b & VARINT_CONT == 0 {
                return Ok(acc);
            }
            shift += 7;
        }
        Err(CodecError::Truncated)
    }

    pub(crate) fn svarint(&mut self) -> Result<i64, CodecError> {
        Ok(unzigzag(self.uvarint()?))
    }

    pub(crate) fn bounded_len(&mut self) -> Result<usize, CodecError> {
        let n = self.uvarint()?;
        if n > WIRE_LEN_MAX {
            return Err(CodecError::TooLarge);
        }
        usize::try_from(n).map_err(|_| CodecError::TooLarge)
    }

    pub(crate) fn bytes(&mut self, n: usize) -> Result<&'a [u8], CodecError> {
        let end = self.pos.checked_add(n).ok_or(CodecError::Truncated)?;
        let slice = self.buf.get(self.pos..end).ok_or(CodecError::Truncated)?;
        self.pos = end;
        Ok(slice)
    }

    pub(crate) fn blob(&mut self) -> Result<&'a [u8], CodecError> {
        let n = self.bounded_len()?;
        self.bytes(n)
    }

    pub(crate) fn string(&mut self) -> Result<String, CodecError> {
        let slice = self.blob()?;
        std::str::from_utf8(slice)
            .map(str::to_string)
            .map_err(|_| CodecError::Utf8)
    }

    pub(crate) fn float(&mut self) -> Result<f64, CodecError> {
        let slice = self.bytes(8)?;
        let mut bytes = [0u8; 8];
        bytes.copy_from_slice(slice);
        Ok(f64::from_bits(u64::from_le_bytes(bytes)))
    }

    pub(crate) fn bool(&mut self) -> Result<bool, CodecError> {
        match self.byte()? {
            0 => Ok(false),
            1 => Ok(true),
            _ => Err(CodecError::Malformed),
        }
    }

    // A node reference: an index into the table strictly below the node being
    // parsed, so the graph is acyclic and decode is a forward pass. A hostile
    // back-reference (a cycle) lands here as a `BadReference`.
    pub(crate) fn node_ref(&mut self, below: u32) -> Result<u32, CodecError> {
        let i = u32::try_from(self.uvarint()?).map_err(|_| CodecError::BadReference)?;
        if i >= below {
            return Err(CodecError::BadReference);
        }
        Ok(i)
    }

    pub(crate) fn node_refs(&mut self, below: u32) -> Result<Vec<u32>, CodecError> {
        let n = self.bounded_len()?;
        (0..n).map(|_| self.node_ref(below)).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::{from_wire, put_str, put_svarint, put_uvarint, to_wire, Reader, VARINT_MAX_BYTES};
    use crate::store::CodecError;

    #[test]
    fn uvarint_and_svarint_round_trip() {
        for n in [0u64, 1, 127, 128, 300, u64::MAX] {
            let mut out = Vec::new();
            put_uvarint(&mut out, n);
            assert_eq!(Reader::new(&out).uvarint().unwrap(), n);
        }
        for x in [0i64, 1, -1, i64::MIN, i64::MAX] {
            let mut out = Vec::new();
            put_svarint(&mut out, x);
            assert_eq!(Reader::new(&out).svarint().unwrap(), x);
        }
    }

    #[test]
    fn truncated_varint_is_rejected() {
        // A run of continuation bytes that never terminates is capped, not looped.
        let all_cont = vec![0x80u8; VARINT_MAX_BYTES + 1];
        assert_eq!(
            Reader::new(&all_cont).uvarint().unwrap_err(),
            CodecError::Truncated
        );
        // A buffer that ends mid-varint truncates rather than over-reads.
        assert_eq!(
            Reader::new(&[0x80]).uvarint().unwrap_err(),
            CodecError::Truncated
        );
    }

    #[test]
    fn over_long_length_is_rejected() {
        // A length prefix past the bound is refused before any bytes are consumed.
        let mut out = Vec::new();
        put_uvarint(&mut out, super::WIRE_LEN_MAX + 1);
        assert_eq!(
            Reader::new(&out).bounded_len().unwrap_err(),
            CodecError::TooLarge
        );
    }

    #[test]
    fn string_bounds_and_utf8() {
        let mut out = Vec::new();
        put_str(&mut out, "prism");
        assert_eq!(Reader::new(&out).string().unwrap(), "prism");

        // A length that overruns the buffer truncates.
        let mut over = Vec::new();
        put_uvarint(&mut over, 9);
        over.extend_from_slice(b"short");
        assert_eq!(
            Reader::new(&over).string().unwrap_err(),
            CodecError::Truncated
        );

        // Invalid UTF-8 in a length-prefixed string is caught.
        let mut bad = Vec::new();
        put_uvarint(&mut bad, 1);
        bad.push(0xff);
        assert_eq!(Reader::new(&bad).string().unwrap_err(), CodecError::Utf8);
    }

    #[test]
    fn table_numbering_is_inverse_and_range_checked() {
        const TABLE: &[u8] = &[10, 20, 30];
        for (i, &v) in TABLE.iter().enumerate() {
            assert_eq!(to_wire(TABLE, v), i as u64);
            assert_eq!(from_wire(TABLE, i as u64).unwrap(), v);
        }
        // An index past the table (an unknown tag) is rejected, not misread.
        assert_eq!(
            from_wire::<u8>(TABLE, TABLE.len() as u64).unwrap_err(),
            CodecError::Malformed
        );
    }
}
