pub(super) const TAG_OFF: i64 = 8;
pub(super) const HDR_BYTES: i64 = 24;
pub(super) const WORD_BYTES: i64 = 8;

pub(super) const STR_TAG: i64 = 0x5354_5200;
pub(super) const BIG_TAG: i64 = 0x4249_4700;

const _: () = assert!(
    size_of::<usize>() == 8 && size_of::<u64>() == 8,
    "prism tagging scheme assumes LP64"
);

pub(super) fn idx64(n: usize) -> i64 {
    i64::try_from(n).unwrap_or(i64::MAX)
}
