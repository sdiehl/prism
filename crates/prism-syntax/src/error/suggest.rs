//! "Did you mean ...?" name suggestions.
//!
//! A small, dependency-free fuzzy matcher: when the checker reports an unknown
//! name (a class, type, field, variable, effect operation, module), it offers
//! the closest name in scope, the way `rustc` and GHC do. The distance is
//! Damerau-Levenshtein (so a single adjacent transposition, `flie` for `file`,
//! counts as one edit), and the acceptance bound widens by one for names long
//! enough that a single typo is not the only plausible slip.
//!
//! This is the compiler's only edit-distance implementation; every consumer
//! (checker diagnostics, the REPL, pass-name parsing) routes through it.

/// Names no longer than this tolerate only [`MAX_EDITS_SHORT`]: at three
/// characters or fewer, two edits reach most of the namespace.
pub const SHORT_NAME_LEN: usize = 3;

/// Edit budget for a name of at most [`SHORT_NAME_LEN`] characters.
pub const MAX_EDITS_SHORT: usize = 1;

/// Edit budget for a name longer than [`SHORT_NAME_LEN`].
pub const MAX_EDITS_LONG: usize = 2;

/// How many candidates a suggestion lists before it stops being a hint.
pub const MAX_SUGGESTIONS: usize = 3;

/// The edit budget allowed for a name of `len` characters.
#[must_use]
pub const fn max_edits(len: usize) -> usize {
    if len <= SHORT_NAME_LEN {
        MAX_EDITS_SHORT
    } else {
        MAX_EDITS_LONG
    }
}

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

/// Every candidate within the edit budget for `target`, closest first, ties
/// broken alphabetically, capped at [`MAX_SUGGESTIONS`].
///
/// Exact matches are never suggested: the caller already knows the name is
/// unknown, so an identical candidate is a scoping bug, not a typo.
#[must_use]
pub fn suggest<'a, I>(target: &str, candidates: I) -> Vec<&'a str>
where
    I: IntoIterator<Item = &'a str>,
{
    let budget = max_edits(target.chars().count());
    let mut scored: Vec<(usize, &str)> = candidates
        .into_iter()
        .filter_map(|c| {
            let d = edit_distance(target, c);
            (d > 0 && d <= budget).then_some((d, c))
        })
        .collect();
    scored.sort_unstable();
    scored.dedup();
    scored.truncate(MAX_SUGGESTIONS);
    scored.into_iter().map(|(_, c)| c).collect()
}

/// The candidate closest to `target`, for a "did you mean" hint, or `None` if
/// nothing is close enough.
#[must_use]
pub fn did_you_mean<'a, I>(target: &str, candidates: I) -> Option<&'a str>
where
    I: IntoIterator<Item = &'a str>,
{
    suggest(target, candidates).first().copied()
}

/// A ready-to-use `help` line naming the close candidates.
///
/// Renders up to [`MAX_SUGGESTIONS`] of them: ``did you mean `a`, `b`, or
/// `c`?``. `None` when nothing in `candidates` is within the edit budget,
/// since a wrong guess is worse than no guess.
#[must_use]
pub fn suggestion<'a, I>(target: &str, candidates: I) -> Option<String>
where
    I: IntoIterator<Item = &'a str>,
{
    let hits = suggest(target, candidates);
    let (last, rest) = hits.split_last()?;
    let head: Vec<String> = rest.iter().map(|c| format!("`{c}`")).collect();
    let named = match head.len() {
        0 => format!("`{last}`"),
        1 => format!("{} or `{last}`", head[0]),
        _ => format!("{}, or `{last}`", head.join(", ")),
    };
    Some(format!("did you mean {named}?"))
}

#[cfg(test)]
mod tests {
    use super::{did_you_mean, edit_distance, suggest, suggestion, MAX_SUGGESTIONS};

    #[test]
    fn transposition_is_one_edit() {
        assert_eq!(edit_distance("file", "flie"), 1);
        assert_eq!(edit_distance("Show", "Shwo"), 1);
        // Insertion, deletion, substitution.
        assert_eq!(edit_distance("length", "lenght"), 1);
        assert_eq!(edit_distance("map", "maps"), 1);
        assert_eq!(edit_distance("map", "ma"), 1);
        assert_eq!(edit_distance("map", "mop"), 1);
        assert_eq!(edit_distance("", "abc"), 3);
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

    #[test]
    fn short_names_get_one_edit_only() {
        // Two edits away from a three-character name is a different name.
        assert_eq!(did_you_mean("abc", ["xyc"]), None);
        assert_eq!(did_you_mean("abc", ["abd"]), Some("abd"));
        // A longer name tolerates two.
        assert_eq!(did_you_mean("lenght", ["length"]), Some("length"));
        assert_eq!(did_you_mean("colour_of", ["color_of"]), Some("color_of"));
        assert_eq!(did_you_mean("elephant", ["element"]), None);
    }

    #[test]
    fn ranks_by_distance_then_alphabetically_and_caps() {
        let names = ["fold", "folds", "hold", "gold", "bold", "cold"];
        // All one edit away: alphabetical, capped.
        let hits = suggest("mold", names);
        assert_eq!(hits, ["bold", "cold", "fold"]);
        assert_eq!(hits.len(), MAX_SUGGESTIONS);
        // Distance wins over spelling: `fold` (1) before `folds` (2).
        assert_eq!(suggest("foldd", ["zfold", "folds"]), ["folds", "zfold"]);
    }

    #[test]
    fn suggestion_reads_as_prose() {
        assert_eq!(
            suggestion("mold", ["bold"]),
            Some("did you mean `bold`?".to_string())
        );
        assert_eq!(
            suggestion("mold", ["bold", "cold"]),
            Some("did you mean `bold` or `cold`?".to_string())
        );
        assert_eq!(suggestion("mold", ["zebra"]), None);
    }
}
