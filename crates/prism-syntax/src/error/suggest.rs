//! "Did you mean ...?" name suggestions.
//!
//! A small, dependency-free fuzzy matcher: when the checker reports an unknown
//! name (a class, type, field, variable), it offers the closest name in scope,
//! the way `rustc` and GHC do. The distance is Damerau-Levenshtein (so a single
//! adjacent transposition, `flie` for `file`, counts as one edit), and the
//! acceptance threshold scales with the name's length so a longer name tolerates
//! a proportionally larger typo without matching wild guesses.

/// The Damerau-Levenshtein distance between `a` and `b`: the minimum number of
/// single-character insertions, deletions, substitutions, or adjacent
/// transpositions that turn one into the other.
#[must_use]
pub fn edit_distance(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let (m, n) = (a.len(), b.len());
    if m == 0 {
        return n;
    }
    if n == 0 {
        return m;
    }
    // Three rolling rows: two-back (for the transposition case), one-back, current.
    let mut prev2 = vec![0usize; n + 1];
    let mut prev1: Vec<usize> = (0..=n).collect();
    let mut cur = vec![0usize; n + 1];
    for i in 1..=m {
        cur[0] = i;
        for j in 1..=n {
            let cost = usize::from(a[i - 1] != b[j - 1]);
            let mut best = (cur[j - 1] + 1) // insertion
                .min(prev1[j] + 1) // deletion
                .min(prev1[j - 1] + cost); // substitution
            if i > 1 && j > 1 && a[i - 1] == b[j - 2] && a[i - 2] == b[j - 1] {
                best = best.min(prev2[j - 2] + 1); // adjacent transposition
            }
            cur[j] = best;
        }
        std::mem::swap(&mut prev2, &mut prev1);
        std::mem::swap(&mut prev1, &mut cur);
    }
    prev1[n]
}

/// The candidate closest to `target`, for a "did you mean" hint, or `None` if
/// nothing is close enough.
///
/// Accepts an edit up to `ceil(len/3)` (at least one), and among matches picks
/// the smallest distance, breaking ties toward the shorter name. Exact matches
/// are never suggested (the caller already knows the name is unknown, so an
/// identical candidate would be a bug, not a typo).
#[must_use]
pub fn did_you_mean<'a, I>(target: &str, candidates: I) -> Option<&'a str>
where
    I: IntoIterator<Item = &'a str>,
{
    let len = target.chars().count();
    let threshold = len.div_ceil(3).max(1);
    candidates
        .into_iter()
        .filter_map(|c| {
            let d = edit_distance(target, c);
            (d > 0 && d <= threshold).then_some((d, c))
        })
        .min_by_key(|&(d, c)| (d, c.len()))
        .map(|(_, c)| c)
}

/// A ready-to-use `help` line, when a close name exists: `did you mean `foo`?`.
#[must_use]
pub fn suggestion<'a, I>(target: &str, candidates: I) -> Option<String>
where
    I: IntoIterator<Item = &'a str>,
{
    did_you_mean(target, candidates).map(|c| format!("did you mean `{c}`?"))
}

#[cfg(test)]
mod tests {
    use super::{did_you_mean, edit_distance};

    #[test]
    fn transposition_is_one_edit() {
        assert_eq!(edit_distance("file", "flie"), 1);
        assert_eq!(edit_distance("Show", "Shwo"), 1);
    }

    #[test]
    fn suggests_the_closest_in_scope() {
        let names = ["Show", "Ord", "Eq", "Functor"];
        assert_eq!(did_you_mean("Shwo", names), Some("Show"));
        assert_eq!(did_you_mean("Eqq", names), Some("Eq"));
        // Nothing close: no wild guess.
        assert_eq!(did_you_mean("Monad", names), None);
        // An exact name is never offered back as a suggestion.
        assert_eq!(did_you_mean("Show", names), None);
    }
}
