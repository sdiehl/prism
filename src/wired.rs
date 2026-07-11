//! Wired-in standard-library symbols the compiler references by name.
//!
//! The `kw.rs` analogue for the standard library: the container type
//! constructors the index sugar dispatches on, and the accessor / setter
//! functions the elaborator injects for `e[k]` and `e[k] := v`. Keeping them here
//! behind an [`Indexable`] classifier means a stdlib rename and its compiler hook
//! move together, and the receiver-type knowledge lives in one match rather than
//! three stringly-typed ones scattered across typecheck and elaboration.

use crate::names::bare_name;
use crate::sym::Sym;
use crate::types::ty::LIST;
use crate::types::Type;

// Container type constructors. The builtin containers (`Array`, `HashMap`) carry
// bare names; a stdlib container (`Tensor` is `Data.Tensor.Tensor`) is matched on
// its bare name, so classification is independent of the defining module path.
const TY_ARRAY: &str = "Array";
const TY_HASHMAP: &str = "HashMap";
const TY_TENSOR: &str = "Tensor";

/// A container the `e[k]` / `e[k] := v` index sugar supports.
///
/// Classifying a receiver type once, here, is what lets the typing rule
/// ([`Self::signature`]) and the two elaboration hooks ([`Self::getter`],
/// [`Self::setter`]) share one source of truth instead of re-matching type names.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Indexable {
    Array,
    HashMap,
    List,
    Str,
    Tensor,
}

impl Indexable {
    /// Classify an index-sugar receiver type, or `None` if it is not indexable.
    /// The single home for the container type names.
    #[must_use]
    pub fn classify(ty: &Type) -> Option<Self> {
        match ty {
            Type::Con(n, args) if bare_name(n.as_str()) == TY_ARRAY && args.len() == 1 => {
                Some(Self::Array)
            }
            Type::Con(n, args) if bare_name(n.as_str()) == TY_HASHMAP && args.len() == 1 => {
                Some(Self::HashMap)
            }
            Type::Con(n, args) if bare_name(n.as_str()) == LIST && args.len() == 1 => {
                Some(Self::List)
            }
            Type::Str => Some(Self::Str),
            Type::Con(n, args) if bare_name(n.as_str()) == TY_TENSOR && args.is_empty() => {
                Some(Self::Tensor)
            }
            _ => None,
        }
    }

    /// The key type, element type, and writability the typechecker gives `e[k]`.
    /// `ty` is the already-classified receiver; its type argument supplies the
    /// element for the polymorphic containers.
    #[must_use]
    pub fn signature(self, ty: &Type) -> (Type, Type, bool) {
        let elem = || match ty {
            Type::Con(_, args) if !args.is_empty() => args[0].clone(),
            _ => Type::Int,
        };
        match self {
            // Writable through the in-place `array_set` / functional `list_set`.
            Self::Array | Self::List => (Type::Int, elem(), true),
            Self::HashMap => (Type::Str, elem(), true),
            Self::Str => (Type::Int, Type::Int, false),
            // A dense tensor is indexed by a list of per-axis indices into a float.
            Self::Tensor => (
                Type::Con(Sym::from(LIST), vec![Type::Int]),
                Type::Float,
                true,
            ),
        }
    }

    /// The function backing a read `e[k]`. The builtin containers use bare prelude
    /// accessors; the tensor accessor is a `Data.Tensor` function, so it is named
    /// by its canonical (module-qualified) form the elaborator can call directly.
    #[must_use]
    pub const fn getter(self) -> &'static str {
        match self {
            Self::Array => "at_array",
            Self::HashMap => "at_hashmap",
            Self::List => "at_list",
            Self::Str => "at_byte",
            Self::Tensor => "Data.Tensor.at_tensor",
        }
    }

    /// The setter backing `e[k] := v`, or `None` for a read-only container.
    #[must_use]
    pub const fn setter(self) -> Option<&'static str> {
        match self {
            Self::Array => Some("array_set"),
            Self::HashMap => Some("hm_insert"),
            Self::List => Some("list_set"),
            Self::Str => None,
            Self::Tensor => Some("Data.Tensor.tensor_set"),
        }
    }
}
