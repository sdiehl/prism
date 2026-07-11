use std::collections::BTreeMap;

use crate::kw;
use crate::types::CtorInfo;

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

/// The runtime tag a `Case` dispatches on for constructor `name`: the wired-in
/// nullable's `Null`/`This` tags, otherwise the datatype table's tag. Keeps the
/// tag source the single `kw` constant instead of a literal re-typed in codegen.
pub(super) fn ctor_tag(ctors: &BTreeMap<String, CtorInfo>, name: &str) -> Option<usize> {
    match name {
        kw::CTOR_NULL => Some(kw::OR_NULL_TAG),
        kw::CTOR_THIS => Some(kw::OR_THIS_TAG),
        _ => ctors.get(name).map(|info| info.tag),
    }
}
