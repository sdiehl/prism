// A module's imports are its header. An import written below a declaration is
// lifted to the end of the leading import block, or above the first declaration
// when there is none, and the comment written directly above it moves with it.

fn fmt(src: &str) -> String {
    let once = prism::format(src).expect("case must parse");
    let twice = prism::format(&once).expect("formatted output must parse");
    assert_eq!(once, twice, "formatter is not idempotent on this case");
    once
}

#[test]
fn a_late_import_joins_the_leading_block() {
    let src = r"-- | Module doc.

import Data.Maybe (..)

-- | Why.
pub type E = A | B deriving (Eq, Show)

-- | Lists.
import Data.List (append, reverse)

fn f() = 1
";
    let want = r"-- | Module doc.

import Data.Maybe (..)
-- | Lists.
import Data.List (append, reverse)

-- | Why.
pub type E = A | B deriving (Eq, Show)

fn f() = 1
";
    assert_eq!(fmt(src), want);
}

#[test]
fn a_late_import_with_no_leading_block_goes_above_the_first_declaration() {
    let src = r"-- | Module doc.

-- | Doc of f.
fn f() = 1

import Data.List (reverse)

fn g() = reverse([1])
";
    let want = r"-- | Module doc.

import Data.List (reverse)

-- | Doc of f.
fn f() = 1

fn g() = reverse([1])
";
    assert_eq!(fmt(src), want);
}
