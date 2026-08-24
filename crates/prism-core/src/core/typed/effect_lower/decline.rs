//! Why a free-monad rewrite was refused.
//!
//! A confined region is an optimization, so refusing one is a cost outcome the
//! program survives: the whole-program lowering below it is always available.
//! That makes the refusal invisible unless it is carried, which is what this
//! module is for. The whole-program rung has nothing below it, so the same
//! reason travels out of it as the message of an internal error, and it has to
//! name the declaration and the form or the reader is left to bisect for them. The reason travels as data from the site that found it to the
//! plan artifact and the fallback warning, so neither has to re-derive it and
//! neither parses it back out of a message.

use std::fmt;

use prism_common::sym::Sym;

/// The stable words a refusal renders as, together in one place because the
/// plan artifact and the warning must agree on them. Read as an artifact and
/// matched by tooling, so they are named, not spelled at each site.
const DIRECT_FORCE: &str = "direct-force";
const DIRECT_HOLDS: &str = "direct-holds";
const THUNK_BOUNDARY: &str = "thunk-boundary";
const WORD_CAPTURE: &str = "word-capture";
const HANDLER_ANSWER: &str = "handler-answer";
const HANDLER_ARMS: &str = "handler-arms";
const MEMBER_TAIL: &str = "member-tail";
const MISSING_ROW: &str = "missing-row";
const PLAN_MISMATCH: &str = "plan-mismatch";
const UNSUPPORTED_FORM: &str = "unsupported-form";

/// The shapes a free-monad attempt can refuse at.
///
/// Every refusal in the builder and in the convention-boundary check is one of
/// these; there is no free-prose refusal, because a reason nobody can match on
/// is a reason nobody can act on.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Refusal {
    /// Direct code forces a suspended computation the region owns. The force
    /// would consume an effect cell as an ordinary result.
    DirectForce,
    /// A computation the rewrite copies verbatim holds a suspended computation
    /// the region owns, so copying it would strand the thunk at the wrong
    /// convention.
    DirectHolds,
    /// A thunk left at the direct convention reaches the other one inside its
    /// body: it calls a member, or answers with an effect cell.
    ThunkBoundary,
    /// A value the rewrite copies verbatim mentions, somewhere no crossing
    /// reaches, a binder the region reified into a runtime word. The copy would
    /// read that binder at its source type where the word is what is in scope.
    WordCapture,
    /// A handler that still performs answers with a transformer: a lambda the
    /// code around the handle applies afterwards. The confined region rewrites
    /// that lambda at the monadic convention, and the answer carrying it is an
    /// ordinary value word by then, so no use site can tell which convention it
    /// holds.
    HandlerAnswer,
    /// A handler's clauses answer at Core types that differ, so the one
    /// dispatch every clause flows into has no type to carry. The checker
    /// agrees the clauses answer alike at the source; the difference is the
    /// row a clause that never performs leaves empty inside the answered
    /// function type where a performing sibling carries the ambient one.
    HandlerArms,
    /// A region member's tail is not `Eff`-shaped, so its caller would bind a
    /// value that is not a cell.
    MemberTail,
    /// The residual row solution names no row for a declaration, so the
    /// monadic signature for it cannot be written.
    MissingRow,
    /// A committed region plan and the program disagree about which
    /// declarations exist: the plan names one the program does not define, or
    /// the preparation the plan committed to has gone missing between building
    /// the signatures and using them.
    PlanMismatch,
    /// The builder has no rewrite for a form the declaration contains,
    /// independently of the two conventions meeting. From the confined rung
    /// this widens to whole-program lowering; from whole-program lowering there
    /// is nothing left to widen to.
    UnsupportedForm,
}

impl Refusal {
    /// The stable word for this refusal.
    #[must_use]
    pub const fn word(self) -> &'static str {
        match self {
            Self::DirectForce => DIRECT_FORCE,
            Self::DirectHolds => DIRECT_HOLDS,
            Self::ThunkBoundary => THUNK_BOUNDARY,
            Self::WordCapture => WORD_CAPTURE,
            Self::HandlerAnswer => HANDLER_ANSWER,
            Self::HandlerArms => HANDLER_ARMS,
            Self::MemberTail => MEMBER_TAIL,
            Self::MissingRow => MISSING_ROW,
            Self::PlanMismatch => PLAN_MISMATCH,
            Self::UnsupportedForm => UNSUPPORTED_FORM,
        }
    }

    /// What the refusal claims, in one clause, for a reader who has the
    /// function name in front of them.
    #[must_use]
    pub const fn claim(self) -> &'static str {
        match self {
            Self::DirectForce => "forces a computation the free-monad rewrite owns",
            Self::DirectHolds => "holds a computation the free-monad rewrite owns",
            Self::ThunkBoundary => "holds a direct thunk that reaches the other convention",
            Self::WordCapture => "copies a value that reads a binder the rewrite reified",
            Self::HandlerAnswer => "installs a performing handler that answers with a transformer",
            Self::HandlerArms => "installs a handler whose clauses answer at different types",
            Self::MemberTail => "is a region member whose tail is not effect-shaped",
            Self::MissingRow => "has no residual row to write a monadic signature from",
            Self::PlanMismatch => "is named by a region plan the program does not agree with",
            Self::UnsupportedForm => "contains a form the free-monad builder cannot rewrite",
        }
    }
}

/// What the refusal turned on inside the function, when it turned on anything
/// narrower than the function itself.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Site {
    /// The function alone.
    Function,
    /// A name the function mentions: the callee whose convention disagreed, or
    /// the binder whose force would cross the boundary.
    Name(Sym),
    /// A computation of this shape, named by the shape vocabulary the tail
    /// check already uses.
    Shape(&'static str),
}

/// What a refusal with no declaration to attribute it to is named after.
///
/// The whole-program builder walks the program as one unit, so what it
/// refuses is the program. The cost explainer names its whole-program row
/// after the same word, from here rather than from a second spelling of it.
pub const PROGRAM: &str = "program";

/// A refusal, the declaration it was found in, and the site inside it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Decline {
    pub reason: Refusal,
    /// The declaration the refusal was found in. `None` when the refusing
    /// builder has no per-declaration position to report.
    pub function: Option<Sym>,
    pub site: Site,
}

impl Decline {
    #[must_use]
    pub const fn new(reason: Refusal, function: Sym, site: Site) -> Self {
        Self {
            reason,
            function: Some(function),
            site,
        }
    }

    /// A refusal that turns on the declaration alone.
    #[must_use]
    pub const fn whole(reason: Refusal, function: Sym) -> Self {
        Self::new(reason, function, Site::Function)
    }

    /// A refusal that turns on the program rather than any one declaration.
    #[must_use]
    pub const fn program(reason: Refusal) -> Self {
        Self {
            reason,
            function: None,
            site: Site::Function,
        }
    }

    fn where_found(&self) -> &str {
        self.function.map_or(PROGRAM, |name| name.as_str())
    }

    /// The one-line artifact cell: the word, then where it was found.
    #[must_use]
    pub fn cell(&self) -> String {
        let (word, found) = (self.reason.word(), self.where_found());
        match self.site {
            Site::Function => format!("{word} at {found}"),
            Site::Name(name) => format!("{word} at {found} via {}", name.as_str()),
            Site::Shape(shape) => format!("{word} at {found} ({shape})"),
        }
    }
}

// The sentence a user is shown, in the warning and as the message of the
// internal error a whole-program refusal raises.
impl fmt::Display for Decline {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "`{}` {}", self.where_found(), self.reason.claim())?;
        match self.site {
            Site::Function => Ok(()),
            Site::Name(name) => write!(f, " (`{}`)", name.as_str()),
            Site::Shape(shape) => write!(f, " ({shape})"),
        }
    }
}
