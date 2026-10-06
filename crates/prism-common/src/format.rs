//! Protocol format tags: the versioned name every durable document, sidecar,
//! and store file carries in its envelope or first line.

use std::borrow::Cow;
use std::fmt;

use serde::{Deserialize, Serialize};

/// A versioned format tag, spelled `prism-<family>-v<N>` or, as the first line
/// of a line-oriented file, `prism-<family>\tv<N>`.
///
/// The family is lowercase kebab case and the version a decimal with no
/// leading zero. Constants are checked when the crate compiles; text read from
/// disk is checked once by [`FormatTag::parse`], so a reader tells a malformed
/// tag, another format, and another version of its own format apart. It renders
/// and serializes as exactly the text it was built from.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(try_from = "String", into = "String")]
pub struct FormatTag(Cow<'static, str>);

/// Why a format tag was refused.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum FormatError {
    /// The text does not spell a format tag.
    #[error("malformed format tag `{text}`")]
    Malformed {
        /// The refused text.
        text: String,
    },
    /// A well-formed tag naming a different format.
    #[error("unrecognized format `{found}` (expected `{expected}`)")]
    Foreign {
        /// The tag read.
        found: FormatTag,
        /// The tag this reader speaks.
        expected: FormatTag,
    },
    /// The expected format at a version this build does not read.
    #[error("unsupported format version `{found}`; this build reads `{expected}`")]
    Version {
        /// The tag read.
        found: FormatTag,
        /// The tag this reader speaks.
        expected: FormatTag,
    },
}

const PREFIX: &[u8] = b"prism-";

// The byte offset of the separator before `v<N>`, when `text` is well formed.
const fn split(text: &[u8]) -> Option<usize> {
    if text.len() < PREFIX.len() {
        return None;
    }
    let mut i = 0;
    while i < PREFIX.len() {
        if text[i] != PREFIX[i] {
            return None;
        }
        i += 1;
    }
    // The version: `v`, then digits with no leading zero, at the end.
    let mut d = text.len();
    while d > 0 && text[d - 1].is_ascii_digit() {
        d -= 1;
    }
    if d == text.len() || (text[d] == b'0' && d + 1 < text.len()) || d < 2 || text[d - 1] != b'v' {
        return None;
    }
    let sep = d - 2;
    if sep <= PREFIX.len() || !(text[sep] == b'-' || text[sep] == b'\t') {
        return None;
    }
    // The family: kebab-case words after the prefix.
    let mut prev_dash = true;
    let mut j = PREFIX.len();
    while j < sep {
        let b = text[j];
        let dash = b == b'-';
        if !(dash || b.is_ascii_lowercase() || b.is_ascii_digit()) || (dash && prev_dash) {
            return None;
        }
        prev_dash = dash;
        j += 1;
    }
    if prev_dash {
        return None;
    }
    Some(sep)
}

impl FormatTag {
    /// A tag fixed at compile time.
    ///
    /// # Panics
    /// When `text` is not a well-formed tag; in a `const` item that is a
    /// compile error.
    #[must_use]
    pub const fn new(text: &'static str) -> Self {
        assert!(split(text.as_bytes()).is_some(), "malformed format tag");
        Self(Cow::Borrowed(text))
    }

    /// Validate `text` as a format tag.
    ///
    /// # Errors
    /// [`FormatError::Malformed`] when `text` is not a tag.
    pub fn parse(text: impl Into<String>) -> Result<Self, FormatError> {
        let text = text.into();
        if split(text.as_bytes()).is_some() {
            Ok(Self(Cow::Owned(text)))
        } else {
            Err(FormatError::Malformed { text })
        }
    }

    /// Parse `text` and require it to be `self`.
    ///
    /// # Errors
    /// [`FormatError`] naming whether `text` is malformed, another format, or
    /// another version of this one.
    pub fn expect(&self, text: &str) -> Result<(), FormatError> {
        self.expect_since(self.version(), text).map(drop)
    }

    /// Parse `text` and require it to be this format at a version from
    /// `oldest` through `self`'s, returning the version read.
    ///
    /// # Errors
    /// As [`FormatTag::expect`].
    pub fn expect_since(&self, oldest: u32, text: &str) -> Result<u32, FormatError> {
        let found = Self::parse(text)?;
        let separator = |tag: &Self| tag.0.as_bytes()[tag.sep()];
        if found.family() != self.family() || separator(&found) != separator(self) {
            Err(FormatError::Foreign {
                found,
                expected: self.clone(),
            })
        } else if (oldest..=self.version()).contains(&found.version()) {
            Ok(found.version())
        } else {
            Err(FormatError::Version {
                found,
                expected: self.clone(),
            })
        }
    }

    /// The family, `prism-<family>`, without the version.
    #[must_use]
    pub fn family(&self) -> &str {
        &self.0[..self.sep()]
    }

    /// The version number.
    #[must_use]
    pub fn version(&self) -> u32 {
        self.0[self.sep() + 2..].parse().unwrap_or(u32::MAX)
    }

    /// The tag's text, as it is written.
    #[must_use]
    pub fn as_str(&self) -> &str {
        &self.0
    }

    fn sep(&self) -> usize {
        split(self.0.as_bytes()).unwrap_or(0)
    }
}

// Debug quotes the text, as a `&str` would, so messages naming a tag read
// the same whichever spelling carries it.
impl fmt::Debug for FormatTag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&*self.0, f)
    }
}

impl fmt::Display for FormatTag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::str::FromStr for FormatTag {
    type Err = FormatError;
    fn from_str(s: &str) -> Result<Self, FormatError> {
        Self::parse(s)
    }
}

impl TryFrom<String> for FormatTag {
    type Error = FormatError;
    fn try_from(s: String) -> Result<Self, FormatError> {
        Self::parse(s)
    }
}

impl From<FormatTag> for String {
    fn from(tag: FormatTag) -> Self {
        tag.0.into_owned()
    }
}

#[cfg(test)]
mod tests {
    use super::{FormatError, FormatTag};

    const LOCK: FormatTag = FormatTag::new("prism-lock\tv2");
    const INDEX: FormatTag = FormatTag::new("prism-index-v1");

    #[test]
    fn a_reader_tells_malformed_foreign_and_version_apart() {
        assert_eq!(INDEX.expect("prism-index-v1"), Ok(()));
        assert!(matches!(
            INDEX.expect("prism-index-v2"),
            Err(FormatError::Version { .. })
        ));
        assert!(matches!(
            INDEX.expect("prism-occurrences-v1"),
            Err(FormatError::Foreign { .. })
        ));
        assert!(matches!(
            LOCK.expect("prism-lock\tv3"),
            Err(FormatError::Version { .. })
        ));
        assert!(matches!(
            LOCK.expect("prism-lock-v2"),
            Err(FormatError::Foreign { .. })
        ));
        assert_eq!(LOCK.expect_since(1, "prism-lock\tv1"), Ok(1));
        assert!(matches!(
            LOCK.expect_since(1, "prism-lock\tv0"),
            Err(FormatError::Version { .. })
        ));
        for text in [
            "",
            "prism-index",
            "prism-index-v",
            "prism-index-v01",
            "prism--index-v1",
            "prism-index--v1",
            "prism-Index-v1",
            "index-v1",
            "prism-v1",
            "prism-index-v1 ",
        ] {
            assert!(
                matches!(INDEX.expect(text), Err(FormatError::Malformed { .. })),
                "{text:?}"
            );
        }
    }

    #[test]
    fn family_and_version_split_either_spelling() {
        assert_eq!((INDEX.family(), INDEX.version()), ("prism-index", 1));
        assert_eq!((LOCK.family(), LOCK.version()), ("prism-lock", 2));
        assert_eq!(LOCK.to_string(), "prism-lock\tv2");
    }
}
