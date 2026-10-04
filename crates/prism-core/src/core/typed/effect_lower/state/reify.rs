//! Reification: the operations no parameter can carry.
//!
//! A clause that needs its continuation as a value cannot be answered by
//! threading. Threading works because the rest of the performer is a fixed
//! amount of work the clause can be handed as an accumulator; a clause that
//! resumes twice, or lets its resumption escape, needs the rest of the
//! performer as a first-class thing, and no accumulator is that.
//!
//! So the operations such a clause handles are reified. Their performers stop
//! answering with a value and answer with an effect cell instead: `EPure` for
//! a value, `EOp` for an operation not yet answered, each carrying the queue
//! of work that follows it. The handle site becomes a driver that reads the
//! cell, and the continuation the clause wanted is that queue, wrapped as a
//! thunk it can apply as many times as it likes.
//!
//! The cell vocabulary is [`abi`]; this module is the rewrite that speaks it
//! and the driver that reads it. The functions a reified operation reaches
//! form an island: inside it every body is cells, outside it nothing changes.

use prism_common::fresh::Fresh;
use prism_common::sym::Sym;
use prism_syntax::names;

use crate::core::builtins::Builtin;
use crate::core::cbpv::CoreOp;
use crate::core::effect_abi::FreeMonadDriver;
use crate::core::typed::traverse::{free_comp_var_witnesses, Rewrite};
use crate::core::typed::{CoreInstantiation, LoweredType};
use crate::types::ty::Label;

use super::super::super::verify::row_included;
use super::super::abi;
use super::super::flow::ThunkFlow;
use super::super::latent::{self, Latent};
use super::super::ops::OpIds;
use super::super::{peel, walk};
use super::{
    generic_quantifiers, instantiate_constructor, instantiate_fn, residual_row, union_rows,
    BTreeMap, BTreeSet, CompSig, CoreFnSig, CoreQuantifier, CoreType, EffRow, Type, TypedBinder,
    TypedComp, TypedCompKind, TypedCoreFn, TypedPattern, TypedValue, TypedValueKind, VerifyEnv,
};
use crate::core::typed::TypedHandleOp;

/// The rewrite from a producer's body to the cells that stand for it.
pub(super) struct Reifier<'a> {
    /// The residual row the cells being built carry. Every `Eff`, every
    /// queue and every call to the queue combinators is indexed by it. It is
    /// the island's row, except inside a driver site whose own code performs
    /// more than the island does: there it is that site's row, and a cell
    /// the island answers widens to it.
    pub(super) row: EffRow,
    /// The island's row: the closed union of what its members still perform.
    /// A member answers a cell over this row, and so does a thunk handed to
    /// one, wherever it was written.
    pub(super) island: EffRow,
    /// The row the cells of the function being rewritten run at: the
    /// island's row, or, for a member the threader runs at a gained ambient,
    /// the island's labels over that ambient. A thunk written inside the
    /// function runs there whichever site it was written at.
    pub(super) home: EffRow,
    /// Per member, the island's labels over the ambient the threader will
    /// gain for it; absent for a member that threads nothing.
    pub(super) ambients: &'a BTreeMap<Sym, EffRow>,
    /// Whether the code being rebuilt runs at its own site rather than inside
    /// cells: a driver's direct clause keeps the row variables of the function
    /// it was written in, since its site's row still spells them.
    pub(super) open: bool,
    /// The row quantifier the function being rebuilt answers cells over, when
    /// it has one (see [`Reifier::answering_quantifier`]).
    pub(super) answering: Option<Sym>,
    /// The row the function being rewritten runs at once its reified labels
    /// are gone: what it declared less those, joined with the island's row,
    /// since driving the island performs whatever the island's direct code
    /// does. Cells code is typed at the island's row alone; this is the row
    /// of a driver site outside the island and of the function's signature.
    pub(super) ambient: EffRow,
    /// The operations that answer with cells. Any other operation a body
    /// performs is threaded afterwards, so its `do` is direct code here.
    pub(super) reified: &'a BTreeSet<Sym>,
    /// Every operation the fold answers, threaded or reified: the labels a
    /// carrying position stops naming, since the threader strips the same.
    pub(super) fused: &'a BTreeSet<Sym>,
    /// The island: the functions whose answers are cells already.
    pub(super) members: &'a BTreeSet<Sym>,
    /// The environment that maps an operation to the effect it belongs to.
    pub(super) env: &'a VerifyEnv,
    /// The operation numbering `EOp` cells carry.
    pub(super) ids: &'a OpIds,
    /// Which thunk parameters carry which operations, so a parameter typed
    /// over a bare row variable is still known to answer with cells.
    pub(super) flow: &'a ThunkFlow,
    /// Which parameters a driver in their function forces: a driver reads
    /// cells, so such a parameter is cells at every caller, whatever it
    /// performs.
    pub(super) driven: &'a BTreeMap<Sym, BTreeSet<usize>>,
    /// Every function's signature as the program declared it: what a call
    /// site's arguments are asked to fit, once its carrying positions are
    /// retyped.
    pub(super) sigs: &'a BTreeMap<Sym, CoreFnSig>,
    /// The functions whose tails the island's row was spelled under: a call
    /// to one hands its tail a row less the labels the extension added.
    pub(super) extended: &'a BTreeSet<Sym>,
    /// What every function still performs: a thunk written here reads the
    /// evidence of this scope when its body performs something threaded.
    pub(super) latent: &'a Latent,
    /// What every bound name is to the cells: the width it crosses at and
    /// the reading its force or application gets. A name absent here is read
    /// by its type.
    pub(super) names: BTreeMap<Sym, Carrier>,
    /// The reifying row quantifiers of every function, by name.
    pub(super) reifying_quantifiers: &'a BTreeMap<Sym, BTreeSet<Sym>>,
    /// The row quantifiers of the function being rewritten some call
    /// instantiates at a row a reified effect reaches. A callable answered at
    /// such a row inside this function answers with cells, wherever it is
    /// read, since that is the only representation every instantiation
    /// shares.
    pub(super) reifying: BTreeSet<Sym>,
    /// The drivers minted for handles met inside cells, drained by the
    /// caller into the program.
    pub(super) drivers: Vec<TypedCoreFn>,
    /// The type the computation being rewritten is read at, when its reader
    /// expects something other than what its own type spells: a tail `return`
    /// of a thunk literal builds the thunk at this type.
    pub(super) answer: Option<CoreType>,
    /// The quantifiers of the function being rewritten, which a driver minted
    /// inside it binds again so the types it mentions stay in scope.
    pub(super) quantifiers: Vec<CoreQuantifier>,
    /// Names for the cell binders the rewrite introduces.
    pub(super) fresh: &'a mut Fresh,
    /// Why the rewrite gave up, for the decline the caller reports.
    pub(super) why: Option<String>,
}

/// What a force or application of a bound name is to the cells.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Reading {
    /// Cells, whatever row the name's type spells: a parameter the flow says
    /// a reified operation reaches, or a name bound to such a value.
    Cells,
    /// Direct code, whatever row the name's type spells: a parameter typed
    /// over a reifying row quantifier that the flow says nothing reaches.
    Direct,
    /// Whatever the name's type says.
    ByType,
}

/// The carrier descriptor of a bound name: how it crosses and how it reads.
///
/// A name a cell `Bind` introduces crosses at word width, because the queue
/// that may answer it later carries words and nothing else, and a use of it
/// recovers the type it was bound at from the word. Width and reading are
/// separate: such a name is also cells when it was bound to a carrying value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Carrier {
    /// The type the name was bound at, when it crosses as a runtime word.
    pub(super) word: Option<CoreType>,
    pub(super) reading: Reading,
}

impl Carrier {
    const fn own(reading: Reading) -> Self {
        Self {
            word: None,
            reading,
        }
    }

    const fn word(declared: CoreType, reading: Reading) -> Self {
        Self {
            word: Some(declared),
            reading,
        }
    }
}

impl Reifier<'_> {
    /// Start on a function: note which of its parameters carry a reified
    /// operation, which are typed over a reifying row quantifier and carry
    /// nothing, and which quantifiers its drivers must bind.
    pub(super) fn enter(&mut self, f: &TypedCoreFn) -> Option<()> {
        let residual = residual_row(f.sig().body().effects(), self.reified, self.env);
        self.home = self.row.clone();
        self.answering = self.answering_quantifier(f.name());
        self.ambient = match union_rows(&residual, &self.island) {
            Ok(ambient) => ambient,
            Err(why) => {
                return self.refuse(&format!(
                    "`{}`: a row the island's row does not join ({why})",
                    f.name().as_str()
                ))
            }
        };
        self.quantifiers = f.sig().quantifiers().to_vec();
        self.reifying = self
            .reifying_quantifiers
            .get(&f.name())
            .cloned()
            .unwrap_or_default();
        self.names = f
            .params()
            .iter()
            .enumerate()
            .filter_map(|(i, param)| {
                let reading = if self.carries(f.name(), i) {
                    Reading::Cells
                } else {
                    let mut vars = BTreeSet::new();
                    row_vars(param.ty(), &mut vars);
                    if vars.is_disjoint(&self.reifying) {
                        return None;
                    }
                    Reading::Direct
                };
                Some((param.name(), Carrier::own(reading)))
            })
            .collect();
        Some(())
    }

    /// Run a rewrite with the bound-name context cleared: a clause body of a
    /// nested driver is its own scope, bound by the driver's parameters. A
    /// parameter read as direct code keeps that reading there, since the
    /// clause is quantified as the function it is minted inside.
    fn hoisted<T>(&mut self, f: impl FnOnce(&mut Self) -> Option<T>) -> Option<T> {
        let names = std::mem::take(&mut self.names);
        self.names = names
            .iter()
            .filter(|(_, carrier)| carrier.reading == Reading::Direct && carrier.word.is_none())
            .map(|(name, carrier)| (*name, carrier.clone()))
            .collect();
        let result = f(self);
        self.names = names;
        result
    }

    /// Whether a callee's parameter is cells: the flow says it carries a
    /// reified operation and the callee's declared type for it does not
    /// read it plain, or a driver in the callee forces it.
    ///
    /// The flow joins by name, so a thunk built where something reified
    /// reaches it still reaches a callee instantiated where nothing does.
    /// That callee forces the parameter as its type says, plain, and the
    /// caller settles the thunk before handing it over.
    pub(super) fn carries(&self, callee: Sym, position: usize) -> bool {
        (self
            .flow
            .param
            .get(&callee)
            .and_then(|params| params.get(position))
            .is_some_and(|sig| sig.iter().any(|m| self.reified.contains(&m.id)))
            && !self.reads_plain(callee, position))
            || self
                .driven
                .get(&callee)
                .is_some_and(|positions| positions.contains(&position))
    }

    /// Whether a row reifies as `owner` reads it: it spells a reified
    /// effect, or ends in a quantifier some call instantiates at one.
    fn row_reifies_for(&self, owner: Sym, row: &EffRow) -> bool {
        self.reifies(row)
            || matches!(row.tail(), EffRow::Var(v) if self
                .reifying_quantifiers
                .get(&owner)
                .is_some_and(|quantifiers| quantifiers.contains(v)))
    }

    /// Whether a callee declares a parameter as a thunk whose row reifies
    /// nothing for it: such a parameter is forced plain in its body.
    fn reads_plain(&self, callee: Sym, position: usize) -> bool {
        let Some(CoreType::Thunk(sig)) = self
            .sigs
            .get(&callee)
            .and_then(|sig| sig.params().get(position))
        else {
            return false;
        };
        !self.row_reifies_for(callee, Self::thunk_body_row(sig))
    }

    /// Whether a callee answers a thunk it built as cells, at a site whose
    /// type reads the thunk plain: the callee's declared result reifies for
    /// the callee, so the thunk was rebuilt as cells where it was made, and
    /// the site's instantiation of that result reifies nothing.
    fn settled_result(&self, callee: Sym, site: &CoreType) -> bool {
        let Some(CoreType::Thunk(declared)) = self.sigs.get(&callee).map(|sig| sig.body().result())
        else {
            return false;
        };
        matches!(site, CoreType::Thunk(_))
            && self.reified_thunk_type(site).is_none()
            && self.row_reifies_for(callee, Self::thunk_body_row(declared))
    }

    /// A call whose result the site reads plain while the callee answers it
    /// as cells, bound and settled; any other call as it is.
    fn settled_call(&mut self, call: TypedComp, callee: Sym) -> Option<TypedComp> {
        if !self.settled_result(callee, call.sig().result()) {
            return Some(call);
        }
        let raw = TypedBinder::new(self.mint("t"), call.sig().result().clone());
        let settled = self.settle(&var(raw.name(), raw.ty().clone()))?;
        let read = TypedComp::new(
            CompSig::new(raw.ty().clone(), EffRow::Empty),
            TypedCompKind::Return(settled),
        );
        Some(TypedComp::new(
            call.sig().clone(),
            TypedCompKind::Bind(Box::new(call), raw, Box::new(read)),
        ))
    }

    /// A thunk that answers cells, read at a site whose row admits nothing
    /// reified, settled into the plain thunk that site's type spells: the
    /// dual of the eta expansion that hands a plain thunk to a cells
    /// position. The settled thunk forces the cells thunk through the bridge
    /// and reads the value out of the cell it answers; an operation cell
    /// cannot arrive, since the site's row admits none.
    fn settle(&mut self, value: &TypedValue) -> Option<TypedValue> {
        let CoreType::Thunk(sig) = value.ty().clone() else {
            return None;
        };
        let island = self.island.clone();
        let body = match sig.result() {
            CoreType::Function(fun) if fun.quantifiers().is_empty() => {
                let params: Vec<TypedBinder> = fun
                    .params()
                    .iter()
                    .map(|ty| TypedBinder::new(self.mint("x"), ty.clone()))
                    .collect();
                let args = params
                    .iter()
                    .map(|param| var(param.name(), param.ty().clone()))
                    .collect();
                let cells = CoreFnSig::new(
                    Vec::new(),
                    fun.params().to_vec(),
                    CompSig::new(abi::eff(island.clone()), fun.body().effects().clone()),
                );
                let retyped = CoreType::Thunk(Box::new(CompSig::new(
                    CoreType::Function(Box::new(cells.clone())),
                    sig.effects().clone(),
                )));
                let held = self.bridge(value.clone(), retyped)?;
                let callee = TypedComp::new(
                    CompSig::new(
                        CoreType::Function(Box::new(cells.clone())),
                        sig.effects().clone(),
                    ),
                    TypedCompKind::Force(held),
                );
                let applied = TypedComp::new(
                    cells.body().clone(),
                    TypedCompKind::App {
                        callee: Box::new(callee),
                        instantiation: Vec::new(),
                        args,
                    },
                );
                let ambient = self.settled_row(fun.body().effects())?;
                let driven = driven_clause(applied, fun.body().result(), &ambient, &island, self);
                lam(params, driven)
            }
            CoreType::Function(_) => {
                return self.refuse("a quantified thunk answering cells read as plain")
            }
            result => {
                let retyped = CoreType::Thunk(Box::new(CompSig::new(
                    abi::eff(island.clone()),
                    sig.effects().clone(),
                )));
                let held = self.bridge(value.clone(), retyped)?;
                let forced = TypedComp::new(
                    CompSig::new(abi::eff(island.clone()), sig.effects().clone()),
                    TypedCompKind::Force(held),
                );
                let ambient = self.settled_row(sig.effects())?;
                driven_clause(forced, result, &ambient, &island, self)
            }
        };
        // Driving the cells runs at the island's row whatever the declared
        // type says, so the literal is spelled at that row and handed back
        // at the declared type across the word bridge, as a rebuilt thunk is.
        let literal = TypedValue::new(
            CoreType::Thunk(Box::new(body.sig().clone())),
            TypedValueKind::Thunk(Box::new(body)),
        );
        self.bridge(literal, value.ty().clone())
    }

    /// The row a settled reader's body runs at: the declared row joined with
    /// the island's, which is what driving the island's cells performs.
    fn settled_row(&mut self, declared: &EffRow) -> Option<EffRow> {
        match union_rows(declared, &self.island) {
            Ok(joined) => Some(joined),
            Err(why) => self.refuse(&format!("a settled row the island does not join ({why})")),
        }
    }

    /// How a bound name reads: by its descriptor, or by its type.
    fn reading(&self, name: Sym) -> Reading {
        self.names
            .get(&name)
            .map_or(Reading::ByType, |carrier| carrier.reading)
    }

    /// The type a name bound at word width was bound at.
    fn word_of(&self, name: Sym) -> Option<&CoreType> {
        self.names
            .get(&name)
            .and_then(|carrier| carrier.word.as_ref())
    }

    /// Whether a value is a name that carries a reified operation.
    fn carrier(&self, value: &TypedValue) -> bool {
        matches!(&value.kind, TypedValueKind::Var { name, .. } if self.reading(*name) == Reading::Cells)
    }

    /// Whether a value is a parameter forced as direct code.
    fn direct_param(&self, value: &TypedValue) -> bool {
        matches!(&peel(value).kind, TypedValueKind::Var { name, .. } if self.reading(*name) == Reading::Direct)
    }

    /// Whether a value is cells already: a carrying parameter, or a name
    /// typed as a thunk that performs something reified, since every such
    /// thunk was rebuilt as cells where it was made, wherever it travelled
    /// through data since.
    fn cells_value(&self, value: &TypedValue) -> bool {
        self.carrier(value)
            || (matches!(peel(value).kind, TypedValueKind::Var { .. })
                && !self.direct_param(value)
                && self.reified_thunk_type(value.ty()).is_some())
    }

    /// A thunk literal bound to `name` that is cells: its own row says so, or
    /// `tail` hands the name to a position some callee reads as cells. The
    /// literal comes back at the type it was bound at, wrappers peeled.
    fn bound_literal(
        &self,
        value: &TypedValue,
        tail: &TypedComp,
        name: Sym,
    ) -> Option<(TypedValue, Box<TypedComp>)> {
        let TypedValueKind::Thunk(body) = &peel(value).kind else {
            return None;
        };
        (self.reified_thunk_type(value.ty()).is_some() || self.hands_as_cells(tail, name)).then(
            || {
                (
                    TypedValue::new(value.ty().clone(), peel(value).kind.clone()),
                    body.clone(),
                )
            },
        )
    }

    /// Whether a computation hands `name` to a position some callee reads as
    /// cells.
    fn hands_as_cells(&self, comp: &TypedComp, name: Sym) -> bool {
        let mut pending = vec![comp];
        while let Some(comp) = pending.pop() {
            if let TypedCompKind::Call { callee, args, .. } = comp.kind() {
                let handed = args.iter().enumerate().any(|(i, arg)| {
                    matches!(&peel(arg).kind, TypedValueKind::Var { name: n, .. } if *n == name)
                        && self.carries(*callee, i)
                });
                if handed {
                    return true;
                }
            }
            walk::each_subterm(comp, &mut |child| pending.push(child));
        }
        false
    }

    /// Whether an application's callee forces a carrying parameter.
    fn applies_carrier(&self, callee: &TypedComp) -> bool {
        matches!(callee.kind(), TypedCompKind::Force(thunk) if self.carrier(thunk))
    }

    /// Whether an application's callee forces a parameter that is direct code.
    fn applies_direct(&self, callee: &TypedComp) -> bool {
        matches!(callee.kind(), TypedCompKind::Force(thunk) if self.direct_param(thunk))
    }

    fn refuse<T>(&mut self, why: &str) -> Option<T> {
        if self.why.is_none() {
            self.why = Some(why.to_string());
        }
        None
    }

    fn mint(&mut self, hint: &str) -> Sym {
        Sym::from(names::lowered(hint, self.fresh.bump()))
    }

    /// Whether a row mentions an effect a reified operation belongs to.
    fn reifies(&self, row: &EffRow) -> bool {
        residual_row(row, self.reified, self.env) != *row
    }

    /// Whether a row answers with cells here: it mentions a reified effect,
    /// or its tail is a variable a carrying parameter is typed over.
    fn reifying_row(&self, row: &EffRow) -> bool {
        self.reifies(row) || matches!(row.tail(), EffRow::Var(v) if self.reifying.contains(v))
    }

    fn eff(&self) -> CoreType {
        abi::eff(self.row.clone())
    }

    /// The signature of a computation that answers with a cell: cells code
    /// runs at the row of the cells being built, whichever function it was
    /// written in, since the continuations it builds are stored in queues
    /// typed over that row.
    fn cells(&self) -> CompSig {
        CompSig::new(self.eff(), self.row.clone())
    }

    /// The row a thunk type's body runs at: the function's for a thunk that
    /// returns one, and its own otherwise.
    fn thunk_body_row(sig: &CompSig) -> &EffRow {
        match sig.result() {
            CoreType::Function(fun) => fun.body().effects(),
            _ => sig.effects(),
        }
    }

    /// A thunk type with the reified labels gone from its rows: what a thunk
    /// still performs once its reified operations answer with cells.
    pub(super) fn residual_type(&self, ty: &CoreType) -> CoreType {
        residual_type(ty, self.reified, self.env)
    }

    /// A call's instantiation with the reified labels gone from its rows: an
    /// island callee's row variables stand for what it still performs.
    fn residual_instantiation(
        &self,
        instantiation: &[CoreInstantiation],
    ) -> Vec<CoreInstantiation> {
        residual_instantiation(instantiation, self.reified, self.env)
    }

    /// A call into the island's instantiation: the reified labels gone from
    /// its rows, and every label the callee's row spells already taken out
    /// of what the caller hands the callee's tail, one copy each. Rows count
    /// their labels, and a caller never doubles a label the callee declared
    /// itself, so what comes out is the share the extended tail took on: the
    /// extension merges per label only if the caller stops naming it.
    fn island_instantiation(
        &self,
        callee: Sym,
        instantiation: &[CoreInstantiation],
    ) -> Vec<CoreInstantiation> {
        let mut residual = self.residual_instantiation(instantiation);
        let Some(sig) = self.sigs.get(&callee) else {
            return residual;
        };
        let declared = sig.body().effects();
        let EffRow::Var(tail) = declared.tail() else {
            return residual;
        };
        let own = residual_row(declared, self.fused, self.env);
        let mut extra: Vec<Sym> = own.labels().into_iter().map(|label| label.name).collect();
        let position = sig
            .quantifiers()
            .iter()
            .position(|quantifier| matches!(quantifier, CoreQuantifier::Row(v) if v == tail));
        if let Some(CoreInstantiation::Row(row)) = position.and_then(|i| residual.get_mut(i)) {
            let labels: Vec<Label> = row
                .labels()
                .into_iter()
                .filter(|label| {
                    extra
                        .iter()
                        .position(|name| *name == label.name)
                        .is_none_or(|found| {
                            extra.swap_remove(found);
                            false
                        })
                })
                .cloned()
                .collect();
            *row = EffRow::canonical(labels, row.tail().clone());
        }
        residual
    }

    /// A call's instantiation as the callee's signature now reads it: an
    /// island call, or a call to a function whose tail the island's row was
    /// spelled under, hands the tail its share; any other call is unchanged.
    fn site_instantiation(
        &self,
        callee: Sym,
        instantiation: &[CoreInstantiation],
    ) -> Vec<CoreInstantiation> {
        if self.members.contains(&callee) || self.extended.contains(&callee) {
            self.island_instantiation(callee, instantiation)
        } else {
            instantiation.to_vec()
        }
    }

    /// An island call's instantiation as cells code makes it: the row
    /// variables of the function the code was written in closed off, since
    /// cells run at the island's row and no caller's row variable reaches
    /// them, except the one the cells themselves run under, which the callee
    /// is handed as it is. The callee then answers at the cells' row exactly.
    fn closed_instantiation(
        &self,
        instantiation: Vec<CoreInstantiation>,
    ) -> Vec<CoreInstantiation> {
        if self.open {
            return instantiation;
        }
        let own = |v: &Sym| {
            self.quantifiers.contains(&CoreQuantifier::Row(*v))
                && self.row.tail() != &EffRow::Var(*v)
        };
        instantiation
            .into_iter()
            .map(|arg| match arg {
                CoreInstantiation::Row(row) if matches!(row.tail(), EffRow::Var(v) if own(v)) => {
                    CoreInstantiation::Row(EffRow::canonical(
                        row.labels().into_iter().cloned(),
                        EffRow::Empty,
                    ))
                }
                other => other,
            })
            .collect()
    }

    /// A member's parameter types as its island signature declares them: a
    /// carrying parameter at what it still performs, since the member reads
    /// it as cells, and every other parameter as it was.
    pub(super) fn residual_params(&self, f: &TypedCoreFn) -> Vec<CoreType> {
        f.params()
            .iter()
            .enumerate()
            .map(|(i, param)| {
                if self.carries(f.name(), i) {
                    self.carrying_type(f.name(), param.ty())
                } else {
                    param.ty().clone()
                }
            })
            .collect()
    }

    /// The type a carrying position declares: what the thunk still performs
    /// once every fused operation is answered, closed, since the cells behind
    /// it answer at the island's row and no caller's row variable reaches
    /// them. A threaded operation the flow hands the position is evidence the
    /// threader adds back, at the row it strips to.
    fn carrying_type(&self, owner: Sym, ty: &CoreType) -> CoreType {
        close_thunk_row(
            &residual_type(ty, self.fused, self.env),
            self.answering_quantifier(owner),
        )
    }

    /// The row quantifier a function answers cells over: the tail of its
    /// declared row when that is a variable the island extended and the
    /// threader names no ambient for. Its cells row is the island's labels
    /// ahead of that quantifier, and a carrying position keeps the quantifier
    /// for the same reason: the values its body types over the quantifier
    /// meet its own calls, and a caller instantiates the quantifier away.
    pub(super) fn answering_quantifier(&self, owner: Sym) -> Option<Sym> {
        if self.ambients.contains_key(&owner) {
            return None;
        }
        if !self.members.contains(&owner) && !self.extended.contains(&owner) {
            return None;
        }
        match self.sigs.get(&owner)?.body().effects().tail() {
            EffRow::Var(tail) => Some(*tail),
            _ => None,
        }
    }

    /// The types a call's arguments are asked to fit: the callee's declared
    /// signature with its carrying positions retyped, at the instantiation
    /// the call records. Unknown for a callee the program does not declare.
    fn wanted(&self, callee: Sym, instantiation: &[CoreInstantiation]) -> Option<Vec<CoreType>> {
        let sig = self.sigs.get(&callee)?;
        let params = sig
            .params()
            .iter()
            .enumerate()
            .map(|(i, param)| {
                if self.carries(callee, i) {
                    self.carrying_type(callee, param)
                } else {
                    param.clone()
                }
            })
            .collect();
        let island = CoreFnSig::new(sig.quantifiers().to_vec(), params, sig.body().clone());
        instantiate_fn(&island, instantiation)
            .ok()
            .map(|applied| applied.params().to_vec())
    }

    /// An argument handed to a carrying position, at the type the callee's
    /// parameter reads it: the wanted type when the callee is known, else
    /// what the argument still performs.
    fn carried(&mut self, arg: TypedValue, want: Option<&CoreType>) -> Option<TypedValue> {
        let target = want.map_or_else(|| self.residual_type(arg.ty()), Clone::clone);
        if target == *arg.ty() {
            return Some(arg);
        }
        self.bridge(arg, target)
    }

    /// The type a thunk answers cells at, when its body performs something
    /// reified: the same parameters, and a cell over the island's row in
    /// place of the value. A thunk performing nothing reified has no such
    /// type, and stays what it is.
    pub(super) fn reified_thunk_type(&self, ty: &CoreType) -> Option<CoreType> {
        let CoreType::Thunk(sig) = ty else {
            return None;
        };
        self.reifying_row(Self::thunk_body_row(sig))
            .then(|| self.cells_thunk_type(ty))
            .flatten()
    }

    /// A thunk type with its body retyped to answer with cells, asked of
    /// nothing but the shape: same parameters, same quantifiers.
    fn cells_thunk_type(&self, ty: &CoreType) -> Option<CoreType> {
        let CoreType::Thunk(sig) = ty else {
            return None;
        };
        let cells = self.cells();
        if let CoreType::Function(fun) = sig.result() {
            let fun = CoreFnSig::new(fun.quantifiers().to_vec(), fun.params().to_vec(), cells);
            return Some(CoreType::Thunk(Box::new(CompSig::new(
                CoreType::Function(Box::new(fun)),
                sig.effects().clone(),
            ))));
        }
        Some(CoreType::Thunk(Box::new(cells)))
    }

    /// The cells type a forced thunk is read at: what its row says it
    /// performs, or, for a parameter the flow marks as carrying, whatever its
    /// row says.
    fn forced_thunk_type(&self, thunk: &TypedValue) -> Option<CoreType> {
        self.reified_thunk_type(thunk.ty()).or_else(|| {
            self.carrier(thunk)
                .then(|| self.cells_thunk_type(thunk.ty()))
                .flatten()
        })
    }

    /// A call's arguments, with every literal thunk handed to a carrying
    /// position rebuilt to answer with cells whether or not its own row says
    /// so: the callee forces that position as cells for every caller.
    fn call_args(
        &mut self,
        callee: Sym,
        instantiation: &[CoreInstantiation],
        args: &[TypedValue],
    ) -> Option<Vec<TypedValue>> {
        let wanted = self.wanted(callee, instantiation);
        let want = |i: usize| wanted.as_ref().and_then(|w| w.get(i).cloned());
        args.iter()
            .enumerate()
            .map(|(i, arg)| match &arg.kind {
                TypedValueKind::Thunk(body) if self.carries(callee, i) => {
                    let rebuilt = self.reified_thunk(arg, body)?;
                    self.carried(rebuilt, want(i).as_ref())
                }
                _ if self.carries(callee, i) => {
                    let value = if self.cells_value(arg) {
                        self.value(arg)?
                    } else if let Some(rebuilt) = self.eta_cells(arg) {
                        rebuilt
                    } else {
                        let why = format!(
                            "`{}` handed to a cells position of `{}` and not cells",
                            describe(arg),
                            callee.as_str()
                        );
                        return self.refuse(&why);
                    };
                    self.carried(value, want(i).as_ref())
                }
                _ => {
                    let value = self.value(arg)?;
                    match want(i) {
                        Some(want) if phantom_rows_apart(value.ty(), &want) => {
                            self.bridge(value, want)
                        }
                        _ => Some(value),
                    }
                }
            })
            .collect()
    }

    /// An application's arguments as the function applied declares them. A
    /// value a member answered spells the closed row of the cells that
    /// answered it, while the function applied still spells the row variable
    /// of the function it was written in; the two are one representation,
    /// and the argument crosses through the word bridge.
    fn app_args(&mut self, callee: &TypedComp, args: &[TypedValue]) -> Option<Vec<TypedValue>> {
        let params: Vec<CoreType> = match callee.sig().result() {
            CoreType::Function(fun) => fun.params().to_vec(),
            _ => Vec::new(),
        };
        args.iter()
            .enumerate()
            .map(|(i, arg)| {
                let value = self.value(arg)?;
                match params.get(i) {
                    Some(want) if phantom_rows_apart(value.ty(), want) => {
                        self.bridge(value, want.clone())
                    }
                    _ => Some(value),
                }
            })
            .collect()
    }

    /// A thunk seen at another thunk type. Both are one machine word, so the
    /// bridge is the same one every cell boundary crosses, and nothing about
    /// the closure itself changes.
    fn bridge(&mut self, value: TypedValue, ty: CoreType) -> Option<TypedValue> {
        let have = value.ty().clone();
        let want = ty.clone();
        abi::try_word_bridge(value, ty).or_else(|| {
            self.refuse(&format!(
                "a value the word bridge does not carry ({have} at {want})"
            ))
        })
    }

    /// Run `f` with the lambda parameters `params` shadowing any word-width
    /// names they spell.
    fn shadow<T>(
        &mut self,
        params: &[TypedBinder],
        f: impl FnOnce(&mut Self) -> Option<T>,
    ) -> Option<T> {
        let saved: Vec<(Sym, Option<Carrier>)> = params
            .iter()
            .map(|param| (param.name(), self.names.remove(&param.name())))
            .collect();
        let result = f(self);
        for (name, carrier) in saved {
            if let Some(carrier) = carrier {
                self.names.insert(name, carrier);
            }
        }
        result
    }

    /// A thunk whose body performs something reified, rebuilt to answer with
    /// cells and handed back at the type it was declared at. Every receiver
    /// keeps seeing the declared type; only an application inside the island
    /// looks through the bridge to the cells.
    pub(super) fn reified_thunk(
        &mut self,
        value: &TypedValue,
        body: &TypedComp,
    ) -> Option<TypedValue> {
        let answered = match value.ty() {
            CoreType::Thunk(sig) => match sig.result() {
                CoreType::Function(fun) => Some(fun.body().result().clone()),
                _ => Some(sig.result().clone()),
            },
            _ => None,
        };
        // The thunk reads the evidence of the scope that built it: one whose
        // body performs something the threader answers reads that scope's,
        // so it runs where that evidence is typed, and one performing nothing
        // threaded makes whatever evidence it reads itself, so it runs at the
        // island's row whichever site it was written at, unless the scope
        // answers cells over its own quantifier, which the thunk keeps: what
        // it closes over is typed over that quantifier. The threader reads
        // the choice back off the rebuilt thunk's row.
        let mut performed = BTreeSet::new();
        let inner = match body.kind() {
            TypedCompKind::Lam(_, inner) => inner.as_ref(),
            _ => body,
        };
        latent::latent(inner, self.latent, &mut performed);
        let reads_evidence = performed
            .iter()
            .any(|op| self.fused.contains(&op.id) && !self.reified.contains(&op.id));
        let answering = matches!(self.home.tail(), EffRow::Var(v) if self.answering == Some(*v));
        let home = if reads_evidence || answering {
            self.home.clone()
        } else {
            self.island.clone()
        };
        let site = std::mem::replace(&mut self.row, home);
        let open = std::mem::replace(&mut self.open, false);
        let cells = match body.kind() {
            TypedCompKind::Lam(params, inner) => {
                let inner = self.shadow(params, |this| this.comp_at(inner, answered.as_ref()));
                inner.map(|inner| lam(params.clone(), inner))
            }
            _ => self.comp_at(body, answered.as_ref()),
        };
        self.row = site;
        self.open = open;
        let cells = cells?;
        let thunk = TypedValue::new(
            CoreType::Thunk(Box::new(cells.sig().clone())),
            TypedValueKind::Thunk(Box::new(cells)),
        );
        self.bridge(thunk, value.ty().clone())
    }

    /// A thunk value that is not cells, handed to a position read as cells:
    /// the thunk it names is forced by a literal written here, and that
    /// literal is rebuilt to answer with cells like any other. A thunk over
    /// a scheme of its own has no literal spelling and stays refused.
    fn eta_cells(&mut self, value: &TypedValue) -> Option<TypedValue> {
        let CoreType::Thunk(sig) = value.ty() else {
            return None;
        };
        let held = self.value(value)?;
        let body = match sig.result() {
            CoreType::Function(fun) if fun.quantifiers().is_empty() => {
                let params: Vec<TypedBinder> = fun
                    .params()
                    .iter()
                    .map(|ty| TypedBinder::new(self.mint("x"), ty.clone()))
                    .collect();
                let args = params
                    .iter()
                    .map(|param| {
                        TypedValue::new(
                            param.ty().clone(),
                            TypedValueKind::Var {
                                name: param.name(),
                                instantiation: Vec::new(),
                            },
                        )
                    })
                    .collect();
                let callee = TypedComp::new(
                    CompSig::new(sig.result().clone(), sig.effects().clone()),
                    TypedCompKind::Force(held),
                );
                let applied = TypedComp::new(
                    fun.body().clone(),
                    TypedCompKind::App {
                        callee: Box::new(callee),
                        instantiation: Vec::new(),
                        args,
                    },
                );
                lam(params, applied)
            }
            CoreType::Function(_) => return None,
            _ => TypedComp::new(
                CompSig::new(sig.result().clone(), sig.effects().clone()),
                TypedCompKind::Force(held),
            ),
        };
        let literal = TypedValue::new(
            value.ty().clone(),
            TypedValueKind::Thunk(Box::new(body.clone())),
        );
        self.reified_thunk(&literal, &body)
    }

    /// The callee of an application inside the island: a forced thunk, seen
    /// through the bridge at the type its cells answer at.
    fn callee(&mut self, callee: &TypedComp) -> Option<TypedComp> {
        let TypedCompKind::Force(thunk) = callee.kind() else {
            return self.refuse("an application whose callee is not a forced thunk");
        };
        let Some(retyped) = self.forced_thunk_type(thunk) else {
            return self.refuse("an application of a thunk that performs nothing reified");
        };
        let CoreType::Thunk(sig) = &retyped else {
            return None;
        };
        let forced = CompSig::new(sig.result().clone(), sig.effects().clone());
        let thunk = self.value(thunk)?;
        let thunk = self.bridge(thunk, retyped.clone())?;
        Some(TypedComp::new(forced, TypedCompKind::Force(thunk)))
    }

    /// Run `f` with `name` described by `carrier`.
    fn with_carrier<T>(
        &mut self,
        name: Sym,
        carrier: Carrier,
        f: impl FnOnce(&mut Self) -> Option<T>,
    ) -> Option<T> {
        let old = self.names.insert(name, carrier);
        let result = f(self);
        match old {
            Some(carrier) => self.names.insert(name, carrier),
            None => self.names.remove(&name),
        };
        result
    }

    /// A value, with every word-width name recovered at the type its use
    /// expects. Nothing else about a value changes: the cells carry values as
    /// they were, and only the width they cross at is new.
    fn value(&mut self, value: &TypedValue) -> Option<TypedValue> {
        let ty = value.ty().clone();
        match &value.kind {
            TypedValueKind::Var {
                name,
                instantiation,
            } if self.word_of(*name).is_some() => {
                // A read at word width is the bridge's own, already rebuilt.
                if instantiation.is_empty() && ty == abi::word() {
                    return Some(value.clone());
                }
                if !instantiation.is_empty() || self.word_of(*name) != Some(&ty) {
                    let why = format!(
                        "a word-width name `{}` used at {} and bound at {}",
                        name.as_str(),
                        ty,
                        self.word_of(*name).expect("bound at word width")
                    );
                    return self.refuse(&why);
                }
                Some(abi::lowered_repr(var(*name, abi::word()), ty))
            }
            // A function whose quantifiers some call reifies has a convention
            // fixed per instantiation by its callers, which a bare value does
            // not record. Such a value reaches this pass as a lambda calling
            // the function by name at the reader's row, so this arm is a
            // backstop for a representation no program has produced yet.
            TypedValueKind::Var { name, .. }
                if self
                    .reifying_quantifiers
                    .get(name)
                    .is_some_and(|quantifiers| !quantifiers.is_empty()) =>
            {
                let why = format!(
                    "`{}`: a function answering cells read as a value",
                    name.as_str()
                );
                self.refuse(&why)
            }
            TypedValueKind::Thunk(body) if self.reified_thunk_type(&ty).is_some() => {
                self.reified_thunk(value, body)
            }
            TypedValueKind::Thunk(body) => {
                let body = self.direct(body)?;
                Some(TypedValue::new(ty, TypedValueKind::Thunk(Box::new(body))))
            }
            TypedValueKind::Ctor {
                name,
                tag,
                instantiation,
                fields,
            } => {
                let fields = fields
                    .iter()
                    .map(|field| self.value(field))
                    .collect::<Option<Vec<_>>>()?;
                Some(TypedValue::new(
                    ty,
                    TypedValueKind::Ctor {
                        name: *name,
                        tag: *tag,
                        instantiation: instantiation.clone(),
                        fields,
                    },
                ))
            }
            TypedValueKind::Tuple(fields) => {
                let fields = fields
                    .iter()
                    .map(|field| self.value(field))
                    .collect::<Option<Vec<_>>>()?;
                Some(TypedValue::new(ty, TypedValueKind::Tuple(fields)))
            }
            // A source reinterpretation keeps its target: whatever it wraps
            // comes back at the type it had, bridged if it was rebuilt.
            TypedValueKind::Reinterpret(inner) => {
                let inner = self.value(inner)?;
                Some(TypedValue::new(
                    ty,
                    TypedValueKind::Reinterpret(Box::new(inner)),
                ))
            }
            TypedValueKind::NewtypeRepr {
                constructor,
                instantiation,
                value: inner,
            } => {
                let inner = self.value(inner)?;
                Some(TypedValue::new(
                    ty,
                    TypedValueKind::NewtypeRepr {
                        constructor: *constructor,
                        instantiation: instantiation.clone(),
                        value: Box::new(inner),
                    },
                ))
            }
            TypedValueKind::LoweredRepr {
                value: inner,
                proof,
            } => {
                let inner = self.value(inner)?;
                Some(TypedValue::new(
                    ty,
                    TypedValueKind::LoweredRepr {
                        value: Box::new(inner),
                        proof: proof.clone(),
                    },
                ))
            }
            TypedValueKind::UnboxedTuple(fields) => {
                let fields = fields
                    .iter()
                    .map(|field| self.value(field))
                    .collect::<Option<Vec<_>>>()?;
                Some(TypedValue::new(ty, TypedValueKind::UnboxedTuple(fields)))
            }
            TypedValueKind::UnboxedRecord(fields) => {
                let fields = fields
                    .iter()
                    .map(|(name, field)| Some((*name, self.value(field)?)))
                    .collect::<Option<Vec<_>>>()?;
                Some(TypedValue::new(ty, TypedValueKind::UnboxedRecord(fields)))
            }
            _ => Some(value.clone()),
        }
    }

    /// A computation that performs nothing reified, rebuilt so its uses of
    /// word-width names recover their own types.
    fn direct(&mut self, comp: &TypedComp) -> Option<TypedComp> {
        let kind = match comp.kind() {
            TypedCompKind::Return(value) => TypedCompKind::Return(self.value(value)?),
            TypedCompKind::Prim(op, a, b) => {
                TypedCompKind::Prim(*op, self.value(a)?, self.value(b)?)
            }
            TypedCompKind::Bind(head, binder, tail) => {
                let reading = match head.kind() {
                    TypedCompKind::Return(value) if self.carrier(value) => Reading::Cells,
                    _ => Reading::ByType,
                };
                let head = self.direct(head)?;
                let tail = self.with_carrier(binder.name(), Carrier::own(reading), |this| {
                    this.direct(tail)
                })?;
                TypedCompKind::Bind(Box::new(head), binder.clone(), Box::new(tail))
            }
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } => {
                let instantiation =
                    self.closed_instantiation(self.site_instantiation(*callee, instantiation));
                let call = TypedComp::new(
                    comp.sig().clone(),
                    TypedCompKind::Call {
                        callee: *callee,
                        args: self.call_args(*callee, &instantiation, args)?,
                        instantiation,
                    },
                );
                self.settled_call(call, *callee)?.kind().clone()
            }
            TypedCompKind::Force(value) => {
                // A pure thunk can close over a queue-backed resumption.
                // Its caller expects the declared answer, not the cell the
                // captured resumption returns inside the reified island.
                let settle = self.carrier(value) && self.reified_thunk_type(value.ty()).is_none();
                let value = self.value(value)?;
                let value = if settle { self.settle(&value)? } else { value };
                TypedCompKind::Force(value)
            }
            TypedCompKind::Lam(params, body) => {
                let body = self.shadow(params, |this| this.direct(body))?;
                TypedCompKind::Lam(params.clone(), Box::new(body))
            }
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } => {
                let callee = self.direct(callee)?;
                let args = self.app_args(&callee, args)?;
                TypedCompKind::App {
                    callee: Box::new(callee),
                    instantiation: instantiation.clone(),
                    args,
                }
            }
            TypedCompKind::If(condition, then, otherwise) => TypedCompKind::If(
                self.value(condition)?,
                Box::new(self.direct(then)?),
                Box::new(self.direct(otherwise)?),
            ),
            TypedCompKind::Case(scrutinee, arms) => TypedCompKind::Case(
                self.value(scrutinee)?,
                arms.iter()
                    .map(|(pattern, body)| Some((pattern.clone(), self.direct(body)?)))
                    .collect::<Option<Vec<_>>>()?,
            ),
            TypedCompKind::Io(op, args) => TypedCompKind::Io(
                *op,
                args.iter()
                    .map(|arg| self.value(arg))
                    .collect::<Option<Vec<_>>>()?,
            ),
            TypedCompKind::StrBuiltin {
                op,
                instantiation,
                args,
            } => TypedCompKind::StrBuiltin {
                op: *op,
                instantiation: instantiation.clone(),
                args: args
                    .iter()
                    .map(|arg| self.value(arg))
                    .collect::<Option<Vec<_>>>()?,
            },
            TypedCompKind::Error(value) => TypedCompKind::Error(self.value(value)?),
            TypedCompKind::Neg(lane, value) => TypedCompKind::Neg(*lane, self.value(value)?),
            TypedCompKind::FloatBuiltin(op, value) => {
                TypedCompKind::FloatBuiltin(*op, self.value(value)?)
            }
            TypedCompKind::UnboxedProject(value, field) => {
                TypedCompKind::UnboxedProject(self.value(value)?, *field)
            }
            // An operation that is threaded rather than reified stays a `do`
            // for the threader to answer.
            TypedCompKind::Do {
                operation,
                instantiation,
                args,
            } => TypedCompKind::Do {
                operation: *operation,
                instantiation: instantiation.clone(),
                args: args
                    .iter()
                    .map(|arg| self.value(arg))
                    .collect::<Option<Vec<_>>>()?,
            },
            // A lowered `var` cell is read and written through values alone.
            TypedCompKind::RefNew(value) => TypedCompKind::RefNew(self.value(value)?),
            TypedCompKind::RefGet(cell) => TypedCompKind::RefGet(self.value(cell)?),
            TypedCompKind::RefSet(cell, value) => {
                TypedCompKind::RefSet(self.value(cell)?, self.value(value)?)
            }
            _ => {
                return self.refuse(&format!(
                    "a direct {} the reified rewrite does not cover",
                    comp_kind_name(comp)
                ))
            }
        };
        Some(TypedComp::new(comp.sig().clone(), kind))
    }

    /// A value as the machine word the cells carry. Everything crossing a cell
    /// boundary is one word wide, so the bridge is where a value's own type is
    /// traded for the representation proof that it fits.
    fn word(&mut self, value: &TypedValue) -> Option<TypedValue> {
        let value = self.value(value)?;
        abi::try_word_bridge(value.clone(), abi::word())
            .or_else(|| Some(abi::lowered_repr(value, abi::word())))
    }

    /// A value as a word, read at the type its receiver expects: a thunk
    /// literal answered where a cells thunk is expected is rebuilt as one,
    /// whatever row its own type spells.
    fn word_at(&mut self, value: &TypedValue, expected: Option<&CoreType>) -> Option<TypedValue> {
        match (expected, &value.kind) {
            (Some(expected), TypedValueKind::Thunk(body))
                if self.reified_thunk_type(expected).is_some()
                    && self.reified_thunk_type(value.ty()).is_none() =>
            {
                let declared = TypedValue::new(expected.clone(), value.kind.clone());
                let rebuilt = self.reified_thunk(&declared, body)?;
                abi::try_word_bridge(rebuilt.clone(), abi::word())
                    .or_else(|| Some(abi::lowered_repr(rebuilt, abi::word())))
            }
            _ => self.word(value),
        }
    }

    /// A call into the island answers with a cell already; only its recorded
    /// type catches up.
    fn member_call(
        &mut self,
        callee: Sym,
        instantiation: &[CoreInstantiation],
        args: &[TypedValue],
    ) -> Option<TypedComp> {
        let instantiation =
            self.closed_instantiation(self.island_instantiation(callee, instantiation));
        // A member the threader runs at a gained ambient answers at
        // the caller's ambient, which is the caller's own row when
        // the caller is such a member too; any other member answers
        // over the island's row.
        let open = matches!(self.row.tail(), EffRow::Var(_))
            && instantiation.iter().any(
                |arg| matches!(arg, CoreInstantiation::Row(row) if row.tail() == self.row.tail()),
            );
        let answers = match self.ambients.get(&callee) {
            Some(_) if matches!(self.row.tail(), EffRow::Var(_)) => self.row.clone(),
            _ if open => self.row.clone(),
            _ => self.island.clone(),
        };
        let call = TypedComp::new(
            CompSig::new(abi::eff(answers.clone()), answers.clone()),
            TypedCompKind::Call {
                callee,
                args: self.call_args(callee, &instantiation, args)?,
                instantiation,
            },
        );
        if self.row == answers {
            return Some(call);
        }
        // The member answers a cell over the island's row; the site's
        // row is wider, and the cell is read at it.
        let answered = TypedBinder::new(self.mint("i"), abi::eff(answers));
        let read = var(answered.name(), answered.ty().clone());
        let Some(widened) = abi::try_widen_cell(read, self.row.clone()) else {
            return self.refuse(&format!(
                "a cell the site does not read ({} at {})",
                answered.ty(),
                self.eff()
            ));
        };
        let read = TypedComp::new(
            CompSig::new(self.eff(), EffRow::Empty),
            TypedCompKind::Return(widened),
        );
        Some(TypedComp::new(
            self.cells(),
            TypedCompKind::Bind(Box::new(call), answered, Box::new(read)),
        ))
    }

    /// An operation's arguments as the single word `EOp` carries: none is a
    /// placeholder, one is itself, and several travel as one tuple the
    /// clause takes apart again.
    fn packed(&mut self, operation: Sym, args: &[TypedValue]) -> Option<TypedValue> {
        let declared: Vec<CoreType> = self
            .env
            .operation(operation)
            .map(|sig| sig.params().to_vec())
            .unwrap_or_default();
        let payloads = args
            .iter()
            .enumerate()
            .map(|(i, arg)| self.payload(arg, declared.get(i)))
            .collect::<Option<Vec<_>>>()?;
        let value = match payloads.as_slice() {
            [] => TypedValue::new(CoreType::Source(Type::Int), TypedValueKind::Int(0)),
            [only] => only.clone(),
            _ => {
                let Some(tuple) = source_tuple(payloads.iter().map(TypedValue::ty)) else {
                    return self.refuse("an operation argument no tuple carries");
                };
                TypedValue::new(tuple, TypedValueKind::Tuple(payloads))
            }
        };
        abi::try_word_bridge(value.clone(), abi::word())
            .or_else(|| Some(abi::lowered_repr(value, abi::word())))
    }

    /// An operation's argument as the clause reads it. The clause reads a
    /// payload by the row the operation declares it at, so a thunk handed to
    /// a payload declared at a reifying row answers with cells whatever row
    /// its own type spells: a literal is rebuilt, a thunk the site holds by
    /// name is forced inside a literal that is. Either comes back at its own
    /// type; the word carries only the representation.
    fn payload(&mut self, value: &TypedValue, declared: Option<&CoreType>) -> Option<TypedValue> {
        let cells = declared.is_some_and(|ty| self.reified_thunk_type(ty).is_some());
        if !cells || self.cells_value(value) || self.reified_thunk_type(value.ty()).is_some() {
            return self.value(value);
        }
        match &peel(value).kind {
            TypedValueKind::Thunk(body) => self.reified_thunk(value, body),
            _ => self.eta_cells(value).or_else(|| {
                let why = format!(
                    "`{}` handed to a payload the clause reads as cells and not cells",
                    describe(value)
                );
                self.refuse(&why)
            }),
        }
    }

    /// A computation that performs nothing reified, lifted into a cell: run it
    /// for its value, then answer with that value as a pure cell.
    fn lift(&mut self, direct: TypedComp) -> Option<TypedComp> {
        let result = direct.sig().result().clone();
        let binder = TypedBinder::new(self.mint("p"), result);
        let value = TypedValue::new(
            binder.ty().clone(),
            TypedValueKind::Var {
                name: binder.name(),
                instantiation: Vec::new(),
            },
        );
        let pure = abi::epure(self.word(&value)?, self.row.clone());
        Some(TypedComp::new(
            self.cells(),
            TypedCompKind::Bind(Box::new(direct), binder, Box::new(pure)),
        ))
    }

    /// Rewrite a computation whose answer is read at `expected`.
    pub(super) fn comp_at(
        &mut self,
        comp: &TypedComp,
        expected: Option<&CoreType>,
    ) -> Option<TypedComp> {
        self.answer = expected.cloned();
        self.comp(comp)
    }

    /// Rewrite one computation into the cell that stands for it.
    pub(super) fn comp(&mut self, comp: &TypedComp) -> Option<TypedComp> {
        let answer = self.answer.take();
        match comp.kind() {
            TypedCompKind::Return(value) => {
                let word = self.word_at(value, answer.as_ref())?;
                Some(abi::epure(word, self.row.clone()))
            }
            TypedCompKind::Bind(head, binder, tail) => {
                let cell = TypedBinder::new(self.mint("m"), self.eff());
                // A name bound to a carrying parameter carries too, and so
                // does one bound to a thunk literal the tail hands to a cells
                // position: that literal is rebuilt as cells here.
                let literal = match head.kind() {
                    TypedCompKind::Return(value) => self.bound_literal(value, tail, binder.name()),
                    _ => None,
                };
                let reading = if literal.is_some()
                    || matches!(head.kind(), TypedCompKind::Return(value) if self.carrier(value))
                {
                    Reading::Cells
                } else {
                    Reading::ByType
                };
                // A member's result the binder's type reads plain is settled
                // ahead of the rest, which then reads the name at its type.
                let settled = matches!(
                    head.kind(),
                    TypedCompKind::Call { callee, .. }
                        if self.members.contains(callee)
                            && self.settled_result(*callee, binder.ty())
                );
                let tail = if settled {
                    self.shadow(std::slice::from_ref(binder), |this| {
                        this.comp_at(tail, answer.as_ref())
                    })?
                } else {
                    let carrier = Carrier::word(binder.ty().clone(), reading);
                    self.with_carrier(binder.name(), carrier, |this| {
                        this.comp_at(tail, answer.as_ref())
                    })?
                };
                let head = match (literal, head.kind()) {
                    (Some((declared, body)), _) => {
                        let rebuilt = self.reified_thunk(&declared, &body)?;
                        let word = abi::try_word_bridge(rebuilt.clone(), abi::word())
                            .unwrap_or_else(|| abi::lowered_repr(rebuilt, abi::word()));
                        abi::epure(word, self.row.clone())
                    }
                    (
                        None,
                        TypedCompKind::Call {
                            callee,
                            instantiation,
                            args,
                        },
                    ) if settled => self.member_call(*callee, instantiation, args)?,
                    (None, _) => self.comp(head)?,
                };
                // The bound name crosses as a word, because the queue that
                // may answer it later carries words and nothing else.
                let (parameter, tail) = if settled {
                    let raw = TypedBinder::new(self.mint("w"), abi::word());
                    let read = abi::lowered_repr(var(raw.name(), abi::word()), binder.ty().clone());
                    let settled = self.settle(&read)?;
                    let prologue = TypedComp::new(
                        CompSig::new(binder.ty().clone(), EffRow::Empty),
                        TypedCompKind::Return(settled),
                    );
                    let tail = TypedComp::new(
                        tail.sig().clone(),
                        TypedCompKind::Bind(Box::new(prologue), binder.clone(), Box::new(tail)),
                    );
                    (raw, tail)
                } else {
                    (TypedBinder::new(binder.name(), abi::word()), tail)
                };
                let lambda = lam(vec![parameter], tail);
                let continuation = TypedValue::new(
                    CoreType::Thunk(Box::new(lambda.sig().clone())),
                    TypedValueKind::Thunk(Box::new(lambda)),
                );
                let bind = TypedComp::new(
                    self.cells(),
                    TypedCompKind::Call {
                        callee: Sym::from("ebind"),
                        instantiation: abi::row_instantiation(self.row.clone()),
                        args: vec![
                            TypedValue::new(
                                cell.ty().clone(),
                                TypedValueKind::Var {
                                    name: cell.name(),
                                    instantiation: Vec::new(),
                                },
                            ),
                            continuation,
                        ],
                    },
                );
                Some(TypedComp::new(
                    bind.sig().clone(),
                    TypedCompKind::Bind(Box::new(head), cell, Box::new(bind)),
                ))
            }
            TypedCompKind::Do {
                operation, args, ..
            } if self.reified.contains(operation) => {
                let id = self.ids.id(*operation)?;
                let packed = self.packed(*operation, args)?;
                Some(abi::eop(
                    TypedValue::new(CoreType::Source(Type::Int), TypedValueKind::Int(id)),
                    TypedValue::new(CoreType::Source(Type::Int), TypedValueKind::Int(0)),
                    packed,
                    abi::empty_queue(self.row.clone()),
                    self.row.clone(),
                ))
            }
            // A call into the island answers with a cell already; only its
            // recorded type catches up.
            TypedCompKind::Call {
                callee,
                instantiation,
                args,
            } if self.members.contains(callee) => {
                // A member's result this site reads plain is bound and
                // settled before it is answered.
                if self.settled_result(*callee, comp.sig().result()) {
                    let raw = TypedBinder::new(self.mint("t"), comp.sig().result().clone());
                    let read = TypedComp::new(
                        CompSig::new(raw.ty().clone(), EffRow::Empty),
                        TypedCompKind::Return(var(raw.name(), raw.ty().clone())),
                    );
                    let bound = TypedComp::new(
                        comp.sig().clone(),
                        TypedCompKind::Bind(Box::new(comp.clone()), raw, Box::new(read)),
                    );
                    self.answer = answer;
                    return self.comp(&bound);
                }
                self.member_call(*callee, instantiation, args)
            }
            TypedCompKind::If(condition, then, otherwise) => Some(TypedComp::new(
                self.cells(),
                TypedCompKind::If(
                    self.value(condition)?,
                    Box::new(self.comp_at(then, answer.as_ref())?),
                    Box::new(self.comp_at(otherwise, answer.as_ref())?),
                ),
            )),
            TypedCompKind::Case(scrutinee, arms) => {
                let scrutinee = self.value(scrutinee)?;
                let arms = arms
                    .iter()
                    .map(|(pattern, body)| {
                        Some((pattern.clone(), self.comp_at(body, answer.as_ref())?))
                    })
                    .collect::<Option<Vec<_>>>()?;
                Some(TypedComp::new(
                    self.cells(),
                    TypedCompKind::Case(scrutinee, arms),
                ))
            }
            // A handle met inside cells whose clauses answer a reified
            // operation: its body answers with a cell, and a driver over
            // cells reads it, forwarding what it does not handle.
            TypedCompKind::Handle { body, ops, .. }
                if ops
                    .arms()
                    .iter()
                    .any(|arm| self.reified.contains(&arm.name())) =>
            {
                let (name, minted, passed) = driver(comp, self, true)?;
                self.drivers.push(minted);
                let cell = TypedBinder::new(self.mint("r"), self.eff());
                let mut args = passed
                    .iter()
                    .map(|local| self.value(local))
                    .collect::<Option<Vec<_>>>()?;
                args.push(var(cell.name(), cell.ty().clone()));
                let driven = TypedComp::new(
                    self.cells(),
                    TypedCompKind::Call {
                        callee: name,
                        instantiation: identity_instantiation(&self.quantifiers),
                        args,
                    },
                );
                let body = self.comp(body)?;
                Some(TypedComp::new(
                    driven.sig().clone(),
                    TypedCompKind::Bind(Box::new(body), cell, Box::new(driven)),
                ))
            }
            // An application of a thunk that performs something reified
            // answers with a cell already: the thunk was rebuilt where it was
            // made, and only the application looks through to that.
            TypedCompKind::App {
                callee,
                instantiation,
                args,
            } if (self.reifying_row(comp.sig().effects()) && !self.applies_direct(callee))
                || self.applies_carrier(callee) =>
            {
                let callee = self.callee(callee)?;
                let args = self.app_args(&callee, args)?;
                Some(TypedComp::new(
                    self.cells(),
                    TypedCompKind::App {
                        callee: Box::new(callee),
                        instantiation: self.residual_instantiation(instantiation),
                        args,
                    },
                ))
            }
            TypedCompKind::Force(thunk)
                if (self.reifying_row(comp.sig().effects()) && !self.direct_param(thunk))
                    || self.carrier(thunk) =>
            {
                let Some(retyped) = self.forced_thunk_type(thunk) else {
                    return self.refuse("a force of a thunk that performs nothing reified");
                };
                let thunk = self.value(thunk)?;
                let thunk = self.bridge(thunk, retyped)?;
                Some(TypedComp::new(self.cells(), TypedCompKind::Force(thunk)))
            }
            // A call to a function off the island performs nothing reified,
            // whatever row its site was instantiated at: it is direct code.
            TypedCompKind::Call { callee, .. } if !self.members.contains(callee) => {
                let direct = self.direct(comp)?;
                self.lift(direct)
            }
            // Anything that performs no reified operation is direct code as far
            // as the cells are concerned, whatever else it performs, and lifts.
            // A shape that does perform one and is not covered yet declines
            // with its own name so the gap is legible rather than silent.
            _ if !self.reifies(comp.sig().effects()) => {
                let direct = self.direct(comp)?;
                self.lift(direct)
            }
            TypedCompKind::Call { callee, .. } => self.refuse(&format!(
                "a call to `{}` the reified rewrite does not cover",
                callee.as_str()
            )),
            other => self.refuse(&format!("a {} the reified rewrite does not cover", {
                let _ = other;
                comp_kind_name(comp)
            })),
        }
    }
}

/// The name of a computation's shape, for a decline that has to say what it
/// met without printing the term.
const fn comp_kind_name(comp: &TypedComp) -> &'static str {
    match comp.kind() {
        TypedCompKind::Return(_) => "return",
        TypedCompKind::Bind(..) => "bind",
        TypedCompKind::Do { .. } => "operation",
        TypedCompKind::If(..) => "conditional",
        TypedCompKind::Case(..) => "case",
        TypedCompKind::App { .. } => "application",
        TypedCompKind::Call { .. } => "call",
        TypedCompKind::Force(_) => "force",
        TypedCompKind::Lam(..) => "lambda",
        TypedCompKind::Handle { .. } => "handle",
        _ => "computation",
    }
}

/// The signature an island member declares: it takes what it took, and answers
/// with a cell over the residual row rather than with a value.
#[must_use]
pub(super) fn producer_signature(
    f: &TypedCoreFn,
    params: Vec<CoreType>,
    cells: &EffRow,
    declared: EffRow,
) -> CoreFnSig {
    CoreFnSig::new(
        f.sig().quantifiers().to_vec(),
        params,
        CompSig::new(abi::eff(cells.clone()), declared),
    )
}

/// A handled computation retyped to the cell its island call answers with:
/// the binds ahead of the call keep their heads and every signature down the
/// spine reads `Eff`. Only a call to a member answers with a cell; a driver
/// or a host answers with the value it drove to.
fn cells_tail(
    body: &TypedComp,
    row: &EffRow,
    ambient: &EffRow,
    members: &BTreeSet<Sym>,
) -> Option<TypedComp> {
    let signature = CompSig::new(abi::eff(row.clone()), ambient.clone());
    match body.kind() {
        TypedCompKind::Bind(head, binder, tail) => Some(TypedComp::new(
            signature,
            TypedCompKind::Bind(
                head.clone(),
                binder.clone(),
                Box::new(cells_tail(tail, row, ambient, members)?),
            ),
        )),
        TypedCompKind::Call { callee, .. } if members.contains(callee) => {
            Some(TypedComp::new(signature, body.kind().clone()))
        }
        _ => None,
    }
}

/// The driver a reifying handle site becomes.
///
/// The handle no longer runs its body: the body answers with a cell, and the
/// driver reads it. A pure cell is the answer, and the return clause finishes
/// it. An operation cell is a clause's turn, and the queue the cell carries is
/// the continuation the clause asked for, handed over as a thunk that applies
/// the queue and drives whatever comes back. Applying it twice therefore runs
/// the rest of the performer twice, which is the whole point.
///
/// A nested driver is one met inside cells: it answers with a cell itself,
/// its clauses are cells code, and an operation it does not handle is
/// forwarded outward as a fresh operation cell whose queue resumes here.
///
/// Answers the driver's name and its declaration; the caller replaces the
/// handle with a call to it.
/// A driver clause's body, rebuilt. One whose resumption is a carrying thunk
/// is cells code: applying the resumption answers with a cell, whatever its
/// row says, and the body runs at the row the clause's cells are driven at. A
/// direct clause still hands what it holds to the island: a call into a cells
/// position crosses the word bridge to the closed type that position
/// declares.
fn clause_body(
    arm: &TypedHandleOp,
    cells: bool,
    row: &EffRow,
    answered: &CoreType,
    reifier: &mut Reifier<'_>,
) -> Option<TypedComp> {
    reifier.hoisted(|this| {
        if cells {
            let site = std::mem::replace(&mut this.row, row.clone());
            this.names
                .insert(arm.resume().name(), Carrier::own(Reading::Cells));
            let rebuilt = this.comp_at(arm.body(), Some(answered));
            this.row = site;
            rebuilt
        } else {
            let open = std::mem::replace(&mut this.open, true);
            let rebuilt = this.direct(arm.body());
            this.open = open;
            rebuilt
        }
    })
}

fn driver(
    handle: &TypedComp,
    reifier: &mut Reifier<'_>,
    nested: bool,
) -> Option<(Sym, TypedCoreFn, Vec<TypedValue>)> {
    let row = reifier.row.clone();
    let row = &row;
    let TypedCompKind::Handle {
        body: _,
        return_binder,
        return_body,
        ops,
    } = handle.kind()
    else {
        return reifier.refuse("a driver for something that is not a handle");
    };
    // A nested driver is cells code and runs at the island's row. A top-level
    // one runs at that row joined with what its clauses perform, which is
    // less than the row the handle it replaces was declared at: that row is
    // the enclosing function's, and names what the function performs
    // elsewhere.
    let mut ambient = row.clone();
    if !nested {
        let clauses = ops
            .arms()
            .iter()
            .map(TypedHandleOp::body)
            .chain(return_body.as_deref());
        for clause in clauses {
            let performed = residual_row(clause.sig().effects(), reifier.reified, reifier.env);
            ambient = match union_rows(&ambient, &performed) {
                Ok(joined) => joined,
                Err(why) => {
                    return reifier
                        .refuse(&format!("a clause row the driver does not join ({why})"))
                }
            };
        }
    }
    if return_binder.is_some() != return_body.is_some() || ops.arms().is_empty() {
        return reifier.refuse("a handler with no clauses");
    }
    let answered = handle.sig().result().clone();
    let result = if nested {
        abi::eff(row.clone())
    } else {
        answered.clone()
    };
    let name = Sym::from(FreeMonadDriver::Handle.mint(reifier.fresh.bump()));
    let cell = TypedBinder::new(reifier.mint("res"), abi::eff(row.clone()));

    // The clauses read the locals of the function the handle stood in. The
    // driver takes them as parameters ahead of the cell and hands them back
    // to itself whenever it resumes.
    let mut seen: BTreeMap<Sym, TypedValue> = BTreeMap::new();
    for arm in ops.arms() {
        let mut free = free_comp_var_witnesses(arm.body());
        for param in arm.params() {
            free.remove(&param.name());
        }
        free.remove(&arm.resume().name());
        seen.extend(free);
    }
    if let (Some(binder), Some(body)) = (return_binder, return_body) {
        let mut free = free_comp_var_witnesses(body);
        free.remove(&binder.name());
        seen.extend(free);
    }
    seen.retain(|local, _| !reifier.sigs.contains_key(local));
    let captured: Vec<TypedBinder> = seen
        .iter()
        .map(|(local, witness)| TypedBinder::new(*local, witness.ty().clone()))
        .collect();
    let hands = |cell: &TypedBinder| -> Vec<TypedValue> {
        captured
            .iter()
            .chain(std::iter::once(cell))
            .map(|binder| var(binder.name(), binder.ty().clone()))
            .collect()
    };
    let signature = CoreFnSig::new(
        reifier.quantifiers.clone(),
        captured
            .iter()
            .chain(std::iter::once(&cell))
            .map(|binder| binder.ty().clone())
            .collect(),
        CompSig::new(result.clone(), ambient.clone()),
    );

    // The pure arm: the body's answer, run through the return clause.
    let word = TypedBinder::new(reifier.mint("x"), abi::word());
    let pure_body = match (return_binder, return_body) {
        (Some(binder), Some(body)) => {
            let unpacked =
                abi::lowered_repr(var(word.name(), word.ty().clone()), binder.ty().clone());
            let body = if nested {
                reifier.hoisted(|this| this.comp_at(body, Some(&answered)))?
            } else {
                (**body).clone()
            };
            TypedComp::new(
                body.sig().clone(),
                TypedCompKind::Bind(
                    Box::new(TypedComp::new(
                        CompSig::new(binder.ty().clone(), EffRow::Empty),
                        TypedCompKind::Return(unpacked),
                    )),
                    binder.clone(),
                    Box::new(body),
                ),
            )
        }
        _ if nested => abi::epure(var(word.name(), word.ty().clone()), row.clone()),
        _ => TypedComp::new(
            CompSig::new(result.clone(), EffRow::Empty),
            TypedCompKind::Return(abi::lowered_repr(
                var(word.name(), word.ty().clone()),
                result.clone(),
            )),
        ),
    };
    let pure_arm = (abi::epure_pattern(row.clone(), word), pure_body);

    // The operation arm: one clause per handled operation, chosen by id.
    let id = TypedBinder::new(reifier.mint("id"), CoreType::Source(Type::Int));
    let skip = TypedBinder::new(reifier.mint("sk"), CoreType::Source(Type::Int));
    let argument = TypedBinder::new(reifier.mint("arg"), abi::word());
    let queue = TypedBinder::new(reifier.mint("k"), abi::queue(row.clone()));

    // The continuation: apply the queue to the resumed-with value, then drive
    // the cell that comes back. Nothing about it is single-use, so a clause is
    // free to force it as many times as it wants.
    let resume_value = TypedBinder::new(Sym::from(names::RESUME_VAL), abi::word());
    let resumed = TypedBinder::new(Sym::from(names::RESUME_KONT), abi::eff(row.clone()));
    let applied = abi::qapply(
        var(queue.name(), queue.ty().clone()),
        var(resume_value.name(), resume_value.ty().clone()),
        row.clone(),
    );
    let redrive = TypedComp::new(
        CompSig::new(result.clone(), ambient.clone()),
        TypedCompKind::Call {
            callee: name,
            instantiation: identity_instantiation(&reifier.quantifiers),
            args: hands(&resumed),
        },
    );
    let resume_lambda = lam(
        vec![resume_value],
        TypedComp::new(
            redrive.sig().clone(),
            TypedCompKind::Bind(
                Box::new(applied.clone()),
                resumed.clone(),
                Box::new(redrive.clone()),
            ),
        ),
    );
    let resume = TypedValue::new(
        CoreType::Thunk(Box::new(resume_lambda.sig().clone())),
        TypedValueKind::Thunk(Box::new(resume_lambda)),
    );

    // The callable convention is decided by the type: a resumption whose
    // declared row reifies answers with a cell, and everything reading such a
    // value applies it as cells code. A top-level driver whose clauses
    // declare their resumption at a reifying row therefore lowers those
    // clauses as cells code around a cell-answering resumption, and drives
    // the clause's cell to the answer it returns itself. A driver whose
    // clauses declare a row that does not reify keeps them direct.
    let reifying = !nested && clauses_resume_at_a_reifying_row(ops.arms(), reifier);
    // A top-level driver's clause cells are driven here and never queued, so
    // they run at the driver's own row: what a clause performs directly while
    // it builds them is part of that row. A nested driver's clause cells are
    // forwarded into queues over the island's row and stay there.
    let clause_row = if reifying {
        ambient.clone()
    } else {
        row.clone()
    };
    let cells_resume = if reifying {
        let Some(lambda) =
            cell_answering_resume(&result, &ambient, &clause_row, applied, resumed, &redrive)
        else {
            return reifier.refuse("a resumption answer no word carries");
        };
        Some(lambda)
    } else {
        None
    };

    // What no clause answers: forwarded outward as an operation cell whose
    // queue resumes this driver, or, for a top-level driver, impossible.
    let mut dispatch = if nested {
        let queue = TypedBinder::new(reifier.mint("q"), abi::queue(row.clone()));
        let snoc = TypedComp::new(
            CompSig::new(abi::queue(row.clone()), EffRow::Empty),
            TypedCompKind::StrBuiltin {
                op: Builtin::TaqSnoc,
                instantiation: abi::row_instantiation(row.clone()),
                args: vec![abi::empty_queue(row.clone()), resume.clone()],
            },
        );
        let forwarded = abi::eop(
            var(id.name(), id.ty().clone()),
            var(skip.name(), skip.ty().clone()),
            var(argument.name(), argument.ty().clone()),
            var(queue.name(), queue.ty().clone()),
            row.clone(),
        );
        TypedComp::new(
            CompSig::new(result.clone(), ambient.clone()),
            TypedCompKind::Bind(Box::new(snoc), queue, Box::new(forwarded)),
        )
    } else {
        TypedComp::new(
            CompSig::new(result.clone(), ambient.clone()),
            TypedCompKind::Error(TypedValue::new(
                CoreType::Source(Type::Str),
                TypedValueKind::Str("ICE: unhandled effect op in closed handler dispatch".into()),
            )),
        )
    };
    for arm in ops.arms().iter().rev() {
        let Some(arm_id) = reifier.ids.id(arm.name()) else {
            return reifier.refuse("a clause for an operation without an id");
        };
        let mut handled = clause_body(arm, nested || reifying, &clause_row, &answered, reifier)?;
        if cells_resume.is_some() {
            handled = driven_clause(handled, &result, &ambient, &clause_row, reifier);
        }
        // The clause's own resumption binder stands for the queue-backed
        // continuation. Spelled as the lambda the clause declared, taking the
        // answer at the clause's own type, it is a value a later threading
        // can widen; a declaration the driver cannot spell that way, or one
        // whose row reifies, is bridged to instead.
        let lambda = cells_resume
            .clone()
            .or_else(|| spelled_resume(arm.resume().ty(), &queue, name, &redrive, reifier))
            .unwrap_or_else(|| resume.clone());
        let bound = if lambda.ty() == arm.resume().ty() {
            lambda
        } else {
            abi::lowered_repr(
                abi::lowered_repr(lambda, abi::word()),
                arm.resume().ty().clone(),
            )
        };
        handled = TypedComp::new(
            handled.sig().clone(),
            TypedCompKind::Bind(
                Box::new(TypedComp::new(
                    CompSig::new(bound.ty().clone(), EffRow::Empty),
                    TypedCompKind::Return(bound),
                )),
                arm.resume().clone(),
                Box::new(handled),
            ),
        );
        let Some(bound) = bind_params(arm.params(), &argument, handled) else {
            return reifier.refuse("a clause parameter no word carries");
        };
        handled = bound;
        // A clause at the operation's own scheme is generic in the types the
        // arm left to the operation. Out of the arm nothing binds them, and
        // the cell hands the clause words: the clause reads them as such.
        let generic: BTreeSet<Sym> = reifier
            .env
            .operation(arm.name())
            .map(|sig| generic_quantifiers(sig, arm.instantiation(), &reifier.quantifiers))
            .unwrap_or_default()
            .into_iter()
            .filter_map(|quantifier| match quantifier {
                CoreQuantifier::Type(v) => Some(v),
                CoreQuantifier::Row(_) => None,
            })
            .collect();
        if !generic.is_empty() {
            let mut worded = Worded {
                generic: &generic,
                nested: false,
            };
            handled = worded.comp(&handled, &());
            if worded.nested {
                return reifier
                    .refuse("a clause generic in a type the driver reads only as a word");
            }
        }
        let test = TypedBinder::new(reifier.mint("t"), CoreType::Source(Type::Bool));
        let compare = TypedComp::new(
            CompSig::new(CoreType::Source(Type::Bool), EffRow::Empty),
            TypedCompKind::Prim(
                CoreOp::Eq,
                var(id.name(), id.ty().clone()),
                TypedValue::new(CoreType::Source(Type::Int), TypedValueKind::Int(arm_id)),
            ),
        );
        let branch = TypedComp::new(
            CompSig::new(result.clone(), ambient.clone()),
            TypedCompKind::If(
                var(test.name(), test.ty().clone()),
                Box::new(handled),
                Box::new(dispatch),
            ),
        );
        dispatch = TypedComp::new(
            branch.sig().clone(),
            TypedCompKind::Bind(Box::new(compare), test, Box::new(branch)),
        );
    }
    let op_arm = (
        abi::eop_pattern(row.clone(), id, skip, argument, queue),
        dispatch,
    );

    let case = TypedComp::new(
        CompSig::new(result, ambient),
        TypedCompKind::Case(var(cell.name(), cell.ty().clone()), vec![pure_arm, op_arm]),
    );
    let passed: Vec<TypedValue> = seen.into_values().collect();
    let mut params = captured;
    params.push(cell);
    Some((
        name,
        TypedCoreFn::new(name, params, case, signature, 0),
        passed,
    ))
}

/// The row variables a thunk type's rows end in, in the thunk's own row and
/// in the row of the function it suspends.
fn row_vars(ty: &CoreType, out: &mut BTreeSet<Sym>) {
    let tail = |row: &EffRow, out: &mut BTreeSet<Sym>| {
        if let EffRow::Var(v) = row.tail() {
            out.insert(*v);
        }
    };
    match ty {
        CoreType::Thunk(sig) => {
            tail(sig.effects(), out);
            row_vars(sig.result(), out);
        }
        CoreType::Function(fun) => {
            for param in fun.params() {
                row_vars(param, out);
            }
            tail(fun.body().effects(), out);
            row_vars(fun.body().result(), out);
        }
        _ => {}
    }
}

/// The instantiation that binds each quantifier to itself: a driver is
/// quantified exactly as the function it is minted inside, and is called from
/// there.
fn identity_instantiation(quantifiers: &[CoreQuantifier]) -> Vec<CoreInstantiation> {
    quantifiers
        .iter()
        .map(|q| match q {
            CoreQuantifier::Type(name) => CoreInstantiation::Type(Type::Var(*name)),
            CoreQuantifier::Row(name) => CoreInstantiation::Row(EffRow::Var(*name)),
        })
        .collect()
}

/// Whether any clause declares its resumption at a row that reifies.
fn clauses_resume_at_a_reifying_row(arms: &[TypedHandleOp], reifier: &Reifier<'_>) -> bool {
    arms.iter().any(|arm| match arm.resume().ty() {
        CoreType::Thunk(outer) => match outer.result() {
            CoreType::Function(fun) => reifier.reifying_row(fun.body().effects()),
            _ => false,
        },
        _ => false,
    })
}

/// The queue-backed resumption of a top-level driver whose clauses read it
/// at a reifying row: it applies the queue, drives the driver to its answer,
/// and hands that answer back as a pure cell, the way every cells reader of
/// the value applies it.
fn cell_answering_resume(
    result: &CoreType,
    ambient: &EffRow,
    row: &EffRow,
    applied: TypedComp,
    resumed: TypedBinder,
    redrive: &TypedComp,
) -> Option<TypedValue> {
    let answer = TypedBinder::new(Sym::from(names::RESUME_ANSWER), result.clone());
    let word = abi::try_word_bridge(var(answer.name(), answer.ty().clone()), abi::word())?;
    let answered = TypedComp::new(
        CompSig::new(abi::eff(row.clone()), ambient.clone()),
        TypedCompKind::Bind(
            Box::new(redrive.clone()),
            answer,
            Box::new(abi::epure(word, row.clone())),
        ),
    );
    let lambda = lam(
        vec![TypedBinder::new(Sym::from(names::RESUME_VAL), abi::word())],
        TypedComp::new(
            answered.sig().clone(),
            TypedCompKind::Bind(Box::new(applied), resumed, Box::new(answered)),
        ),
    );
    Some(TypedValue::new(
        CoreType::Thunk(Box::new(lambda.sig().clone())),
        TypedValueKind::Thunk(Box::new(lambda)),
    ))
}

/// A cell read as the value inside it, where no operation cell can arrive:
/// a clause lowered as cells code inside a top-level driver, which answers
/// the value the clause computed, or a member called from outside the
/// island, whose site's row admits nothing reified.
fn driven_clause(
    handled: TypedComp,
    result: &CoreType,
    ambient: &EffRow,
    row: &EffRow,
    reifier: &mut Reifier<'_>,
) -> TypedComp {
    let cell = TypedBinder::new(reifier.mint("res"), abi::eff(row.clone()));
    let inner = TypedBinder::new(reifier.mint("x"), abi::word());
    let pure_arm = (
        abi::epure_pattern(row.clone(), inner.clone()),
        TypedComp::new(
            CompSig::new(result.clone(), EffRow::Empty),
            TypedCompKind::Return(abi::lowered_repr(
                var(inner.name(), inner.ty().clone()),
                result.clone(),
            )),
        ),
    );
    let op_arm = (
        abi::eop_pattern(
            row.clone(),
            TypedBinder::new(reifier.mint("id"), CoreType::Source(Type::Int)),
            TypedBinder::new(reifier.mint("sk"), CoreType::Source(Type::Int)),
            TypedBinder::new(reifier.mint("arg"), abi::word()),
            TypedBinder::new(reifier.mint("k"), abi::queue(row.clone())),
        ),
        TypedComp::new(
            CompSig::new(result.clone(), EffRow::Empty),
            TypedCompKind::Error(TypedValue::new(
                CoreType::Source(Type::Str),
                TypedValueKind::Str(
                    "ICE: an operation cell reached a site whose row admits none".into(),
                ),
            )),
        ),
    );
    let driven = TypedComp::new(
        CompSig::new(result.clone(), EffRow::Empty),
        TypedCompKind::Case(var(cell.name(), cell.ty().clone()), vec![pure_arm, op_arm]),
    );
    TypedComp::new(
        CompSig::new(result.clone(), ambient.clone()),
        TypedCompKind::Bind(Box::new(handled), cell, Box::new(driven)),
    )
}

/// A lambda whose own type is the function it stands for.
/// The queue-backed resumption at the type a clause declared for it: the
/// clause's answer, bridged to the word the queue takes, applied through the
/// queue and driven on. `None` when the declaration and the driver disagree
/// on what the resumption answers with.
fn spelled_resume(
    declared: &CoreType,
    queue: &TypedBinder,
    driver: Sym,
    redrive: &TypedComp,
    reifier: &mut Reifier<'_>,
) -> Option<TypedValue> {
    let CoreType::Thunk(outer) = declared else {
        return None;
    };
    let CoreType::Function(fun) = outer.result() else {
        return None;
    };
    let [param] = fun.params() else {
        return None;
    };
    let row = reifier.row.clone();
    if !fun.quantifiers().is_empty()
        || fun.body().result() != redrive.sig().result()
        || !row_included(&row, fun.body().effects())
        || !row_included(redrive.sig().effects(), fun.body().effects())
    {
        return None;
    }
    let answer = TypedBinder::new(reifier.mint("x"), param.clone());
    let word = abi::try_word_bridge(var(answer.name(), answer.ty().clone()), abi::word());
    let word = word?;
    let applied = abi::qapply(var(queue.name(), queue.ty().clone()), word, row.clone());
    let resumed = TypedBinder::new(reifier.mint("k"), abi::eff(row));
    // The driver takes the locals it captured ahead of the cell it resumes.
    let TypedCompKind::Call { args: handed, .. } = redrive.kind() else {
        return None;
    };
    let mut args: Vec<TypedValue> = handed[..handed.len() - 1].to_vec();
    args.push(var(resumed.name(), resumed.ty().clone()));
    let redrive = TypedComp::new(
        redrive.sig().clone(),
        TypedCompKind::Call {
            callee: driver,
            instantiation: identity_instantiation(&reifier.quantifiers),
            args,
        },
    );
    let body = TypedComp::new(
        fun.body().clone(),
        TypedCompKind::Bind(Box::new(applied), resumed, Box::new(redrive)),
    );
    let lambda = lam(vec![answer], body);
    Some(TypedValue::new(
        CoreType::Thunk(Box::new(lambda.sig().clone())),
        TypedValueKind::Thunk(Box::new(lambda)),
    ))
}

fn lam(params: Vec<TypedBinder>, body: TypedComp) -> TypedComp {
    let signature = CoreFnSig::new(
        Vec::new(),
        params.iter().map(|param| param.ty().clone()).collect(),
        body.sig().clone(),
    );
    TypedComp::new(
        CompSig::new(CoreType::Function(Box::new(signature)), EffRow::Empty),
        TypedCompKind::Lam(params, Box::new(body)),
    )
}

/// A variable standing for a binder.
const fn var(name: Sym, ty: CoreType) -> TypedValue {
    TypedValue::new(
        ty,
        TypedValueKind::Var {
            name,
            instantiation: Vec::new(),
        },
    )
}

/// Recover a clause's own parameters from the single word `EOp` carried:
/// one is read back at its own type, several as the tuple `packed` built.
fn bind_params(
    parameters: &[TypedBinder],
    argument: &TypedBinder,
    body: TypedComp,
) -> Option<TypedComp> {
    match parameters {
        [] => Some(body),
        [parameter] => {
            let unpacked = abi::lowered_repr(
                var(argument.name(), argument.ty().clone()),
                parameter.ty().clone(),
            );
            Some(TypedComp::new(
                body.sig().clone(),
                TypedCompKind::Bind(
                    Box::new(TypedComp::new(
                        CompSig::new(parameter.ty().clone(), EffRow::Empty),
                        TypedCompKind::Return(unpacked),
                    )),
                    parameter.clone(),
                    Box::new(body),
                ),
            ))
        }
        parameters => {
            let tuple = source_tuple(parameters.iter().map(TypedBinder::ty))?;
            let unpacked = abi::lowered_repr(var(argument.name(), argument.ty().clone()), tuple);
            Some(TypedComp::new(
                body.sig().clone(),
                TypedCompKind::Case(
                    unpacked,
                    vec![(
                        TypedPattern::Tuple(parameters.iter().cloned().map(Some).collect()),
                        body,
                    )],
                ),
            ))
        }
    }
}

/// The tuple type over source types, which is the only tuple there is.
fn source_tuple<'a>(types: impl Iterator<Item = &'a CoreType>) -> Option<CoreType> {
    let fields = types
        .map(|ty| match ty {
            CoreType::Source(ty) => Some(ty.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    Some(CoreType::Source(Type::Tuple(fields)))
}

/// Rewrite a function that is not on the island but handles what the island
/// performs: every reifying handle in it becomes a driver call.
///
/// The handled computation is an island member, so it already answers with a
/// cell; the handle is replaced by binding that cell and driving it. Answers
/// the rewritten function and the drivers it minted.
pub(super) fn reify_handles(
    f: &TypedCoreFn,
    reified: &BTreeSet<Sym>,
    cells: &mut Reifier<'_>,
) -> Option<(TypedCoreFn, Vec<TypedCoreFn>)> {
    cells.enter(f)?;
    let mut sites = Sites {
        reified,
        reifier: cells,
        generated: Vec::new(),
    };
    let body = sites.comp(f.body(), &());
    if sites.reifier.why.is_some() {
        return None;
    }
    let mut generated = sites.generated;
    generated.append(&mut sites.reifier.drivers);
    let body = Runners {
        reifier: sites.reifier,
    }
    .comp(&body, &());
    // A host that drives the island performs what the island's direct code
    // does, on top of its own row.
    let signature = if generated.is_empty() {
        f.sig().clone()
    } else {
        CoreFnSig::new(
            f.sig().quantifiers().to_vec(),
            sites.reifier.residual_params(f),
            CompSig::new(
                f.sig().body().result().clone(),
                sites.reifier.ambient.clone(),
            ),
        )
    };
    Some((
        TypedCoreFn::new(
            f.name(),
            f.params().to_vec(),
            body,
            signature,
            f.dict_arity(),
        ),
        generated,
    ))
}

/// The traversal that reads, outside the island, the cells its members
/// answer. A site outside the island admits no reified operation, or it
/// would be inside, so the cell a member answers there is pure by typing and
/// is read as the value it carries.
struct Runners<'a, 'b> {
    reifier: &'a mut Reifier<'b>,
}

impl Rewrite for Runners<'_, '_> {
    type Ctx = ();

    fn comp(&mut self, comp: &TypedComp, cx: &Self::Ctx) -> TypedComp {
        let TypedCompKind::Call { callee, .. } = comp.kind() else {
            return self.descend_comp(comp, cx);
        };
        if !self.reifier.members.contains(callee)
            || abi::answers_with_effect_cell(comp.sig().result())
        {
            return self.descend_comp(comp, cx);
        }
        let island = self.reifier.island.clone();
        let call = TypedComp::new(
            CompSig::new(abi::eff(island.clone()), comp.sig().effects().clone()),
            comp.kind().clone(),
        );
        driven_clause(
            call,
            comp.sig().result(),
            comp.sig().effects(),
            &island,
            self.reifier,
        )
    }
}

/// The traversal that finds reifying handles. Failure is recorded on the
/// reifier rather than returned, because the rewrite has to rebuild a tree
/// either way and the caller reads the reason from one place.
struct Sites<'a, 'b> {
    reified: &'a BTreeSet<Sym>,
    reifier: &'a mut Reifier<'b>,
    generated: Vec<TypedCoreFn>,
}

impl Rewrite for Sites<'_, '_> {
    type Ctx = ();

    /// A thunk built outside the island that performs something reified is
    /// rebuilt to answer with cells: whoever applies it does so inside.
    fn value(&mut self, value: &TypedValue, cx: &Self::Ctx) -> TypedValue {
        if matches!(value.kind, TypedValueKind::Thunk(_))
            && self.reifier.reified_thunk_type(value.ty()).is_some()
        {
            return self.reifier.value(value).unwrap_or_else(|| value.clone());
        }
        self.descend_value(value, cx)
    }

    fn comp(&mut self, comp: &TypedComp, cx: &Self::Ctx) -> TypedComp {
        // A literal thunk handed to a position the callee forces as cells is
        // rebuilt here, whatever its own row says.
        if let TypedCompKind::Call {
            callee,
            instantiation,
            args,
        } = comp.kind()
        {
            let instantiation = self.reifier.site_instantiation(*callee, instantiation);
            let wanted = self.reifier.wanted(*callee, &instantiation);
            let want = |i: usize| wanted.as_ref().and_then(|w| w.get(i).cloned());
            let args = args
                .iter()
                .enumerate()
                .map(|(i, arg)| match &arg.kind {
                    TypedValueKind::Thunk(body) if self.reifier.carries(*callee, i) => self
                        .reifier
                        .reified_thunk(arg, body)
                        .and_then(|rebuilt| self.reifier.carried(rebuilt, want(i).as_ref()))
                        .unwrap_or_else(|| arg.clone()),
                    _ if self.reifier.carries(*callee, i) => {
                        let value = if self.reifier.cells_value(arg) {
                            self.value(arg, cx)
                        } else if let Some(rebuilt) = self.reifier.eta_cells(arg) {
                            rebuilt
                        } else {
                            let why = format!(
                                "`{}` handed to a cells position of `{}` and not cells (direct)",
                                describe(arg),
                                callee.as_str()
                            );
                            let _: Option<()> = self.reifier.refuse(&why);
                            return arg.clone();
                        };
                        self.reifier
                            .carried(value, want(i).as_ref())
                            .unwrap_or_else(|| arg.clone())
                    }
                    _ => self.value(arg, cx),
                })
                .collect();
            let call = TypedComp::new(
                comp.sig().clone(),
                TypedCompKind::Call {
                    callee: *callee,
                    instantiation,
                    args,
                },
            );
            return self
                .reifier
                .settled_call(call, *callee)
                .unwrap_or_else(|| comp.clone());
        }
        // A thunk literal bound to a name the rest hands over as cells is
        // rebuilt as cells here, and the name carries through the rest.
        if let TypedCompKind::Bind(head, binder, tail) = comp.kind() {
            if let TypedCompKind::Return(value) = head.kind() {
                if let Some((declared, body)) =
                    self.reifier.bound_literal(value, tail, binder.name())
                {
                    let Some(rebuilt) = self.reifier.reified_thunk(&declared, &body) else {
                        return comp.clone();
                    };
                    let head = TypedComp::new(head.sig().clone(), TypedCompKind::Return(rebuilt));
                    let old = self
                        .reifier
                        .names
                        .insert(binder.name(), Carrier::own(Reading::Cells));
                    let tail = self.comp(tail, cx);
                    match old {
                        Some(carrier) => self.reifier.names.insert(binder.name(), carrier),
                        None => self.reifier.names.remove(&binder.name()),
                    };
                    return TypedComp::new(
                        comp.sig().clone(),
                        TypedCompKind::Bind(Box::new(head), binder.clone(), Box::new(tail)),
                    );
                }
            }
        }
        let TypedCompKind::Handle { body, ops, .. } = comp.kind() else {
            return self.descend_comp(comp, cx);
        };
        if !ops
            .arms()
            .iter()
            .any(|arm| self.reified.contains(&arm.name()))
        {
            return self.descend_comp(comp, cx);
        }
        let island = self.reifier.island.clone();
        let ambient = self.reifier.ambient.clone();
        // A handled computation that ends in a call into the island answers
        // with a cell already, and only its recorded types catch up, once the
        // thunks it hands the island are rebuilt. One that performs the
        // operation itself is rewritten into cells in place, at the island's
        // row joined with what the body performs directly: the island's
        // cells are read at that row, and the driver runs at it.
        let minted = self.generated.len();
        let rebuilt = self.comp(body, cx);
        let (row, head) =
            if let Some(head) = cells_tail(&rebuilt, &island, &ambient, self.reifier.members) {
                (island, head)
            } else {
                self.generated.truncate(minted);
                let performed =
                    residual_row(body.sig().effects(), self.reifier.fused, self.reifier.env);
                let named = island.labels();
                let added = performed
                    .labels()
                    .into_iter()
                    .filter(|label| !named.iter().any(|mine| mine.name == label.name));
                let site =
                    EffRow::canonical(named.iter().copied().chain(added).cloned(), EffRow::Empty);
                let saved = std::mem::replace(&mut self.reifier.row, site.clone());
                let head = self.reifier.comp(body);
                self.reifier.row = saved;
                let Some(head) = head else {
                    return comp.clone();
                };
                (site, head)
            };
        let saved = std::mem::replace(&mut self.reifier.row, row.clone());
        let minted = driver(comp, self.reifier, false);
        self.reifier.row = saved;
        let Some((name, function, mut args)) = minted else {
            return comp.clone();
        };
        let signature = function.sig().clone();
        let instantiation = identity_instantiation(signature.quantifiers());
        self.generated.push(function);
        let cell = TypedBinder::new(self.reifier.mint("r0"), abi::eff(row));
        args.push(var(cell.name(), cell.ty().clone()));
        let drive = TypedComp::new(
            signature.body().clone(),
            TypedCompKind::Call {
                callee: name,
                instantiation,
                args,
            },
        );
        TypedComp::new(
            CompSig::new(drive.sig().result().clone(), ambient),
            TypedCompKind::Bind(Box::new(head), cell, Box::new(drive)),
        )
    }
}

fn describe(value: &TypedValue) -> String {
    match &peel(value).kind {
        TypedValueKind::Var { name, .. } => format!("{} : {}", name.as_str(), value.ty()),
        _ => format!("<{}>", value.ty()),
    }
}

/// Whether a driver stands in `f`: a handle whose clauses answer a reified
/// operation.
pub(super) fn hosts_driver(f: &TypedCoreFn, reified: &BTreeSet<Sym>) -> bool {
    installs_handler_for(f, reified)
}

/// Whether some call in `f` names one of `callees`.
pub(super) fn calls_any(f: &TypedCoreFn, callees: &BTreeSet<Sym>) -> bool {
    let mut pending = vec![f.body()];
    while let Some(comp) = pending.pop() {
        if let TypedCompKind::Call { callee, .. } = comp.kind() {
            if callees.contains(callee) {
                return true;
            }
        }
        walk::each_subterm(comp, &mut |child| pending.push(child));
    }
    false
}

/// Whether some handle in `f` names one of `ops`.
pub(super) fn installs_handler_for(f: &TypedCoreFn, ops: &BTreeSet<Sym>) -> bool {
    let mut pending = vec![f.body()];
    while let Some(comp) = pending.pop() {
        if let TypedCompKind::Handle { ops: arms, .. } = comp.kind() {
            if arms.arms().iter().any(|arm| ops.contains(&arm.name())) {
                return true;
            }
        }
        walk::each_subterm(comp, &mut |child| pending.push(child));
    }
    false
}

/// The row quantifiers of each function some call instantiates at a row a
/// reified effect reaches: one naming such an effect, or one tailed by a
/// reifying quantifier of the caller, less the effects the callee's own
/// drivers consume on that quantifier where that consumption is bounded
/// (see [`consumed_on_quantifiers`]). A value typed over such a quantifier
/// is cells whatever its declaration spells, since the declaration is read
/// at every instantiation.
pub(super) fn reifying_quantifiers(
    fns: &[TypedCoreFn],
    reified: &BTreeSet<Sym>,
    env: &VerifyEnv,
) -> BTreeMap<Sym, BTreeSet<Sym>> {
    let effects = reified_effects(reified, env);
    let quantifiers: BTreeMap<Sym, &[CoreQuantifier]> = fns
        .iter()
        .map(|f| (f.name(), f.sig().quantifiers()))
        .collect();
    let consumed: BTreeMap<Sym, BTreeMap<Sym, BTreeSet<Sym>>> = fns
        .iter()
        .map(|f| (f.name(), consumed_on_quantifiers(f, env)))
        .collect();
    let mut reaching: BTreeMap<Sym, BTreeMap<Sym, BTreeSet<Sym>>> = BTreeMap::new();
    loop {
        let mut changed = false;
        for caller in fns {
            let mut pending = vec![caller.body()];
            while let Some(comp) = pending.pop() {
                if let TypedCompKind::Call {
                    callee,
                    instantiation,
                    ..
                } = comp.kind()
                {
                    let declared = quantifiers.get(callee).copied().unwrap_or_default();
                    for (quantifier, bound) in declared.iter().zip(instantiation) {
                        let (CoreQuantifier::Row(quantifier), CoreInstantiation::Row(row)) =
                            (quantifier, bound)
                        else {
                            continue;
                        };
                        let mut flowing: BTreeSet<Sym> = row
                            .labels()
                            .into_iter()
                            .map(|label| label.name)
                            .filter(|name| effects.contains(name))
                            .collect();
                        if let EffRow::Var(v) = row.tail() {
                            if let Some(inherited) =
                                reaching.get(&caller.name()).and_then(|own| own.get(v))
                            {
                                flowing.extend(inherited.iter().copied());
                            }
                        }
                        if let Some(consumed) =
                            consumed.get(callee).and_then(|own| own.get(quantifier))
                        {
                            flowing.retain(|name| !consumed.contains(name));
                        }
                        let slot = reaching
                            .entry(*callee)
                            .or_default()
                            .entry(*quantifier)
                            .or_default();
                        for name in flowing {
                            changed |= slot.insert(name);
                        }
                    }
                }
                walk::each_subterm(comp, &mut |child| pending.push(child));
            }
        }
        if !changed {
            break;
        }
    }
    reaching
        .into_iter()
        .map(|(f, own)| {
            let own: BTreeSet<Sym> = own
                .into_iter()
                .filter(|(_, reaching)| !reaching.is_empty())
                .map(|(quantifier, _)| quantifier)
                .collect();
            (f, own)
        })
        .filter(|(_, own)| !own.is_empty())
        .collect()
}

/// The effects the reified operations belong to, by name.
pub(super) fn reified_effects(reified: &BTreeSet<Sym>, env: &VerifyEnv) -> BTreeSet<Sym> {
    reified
        .iter()
        .filter_map(|op| env.operation(*op))
        .map(|operation| operation.effect().name)
        .collect()
}

/// The effects the handles in `f` answer on each of its row quantifiers,
/// where nothing else `f` reads over the quantifier reaches it from a
/// caller: a handle whose body row is tailed by the quantifier answers its
/// clauses' effects out of whatever that quantifier is instantiated at, so
/// the caller's instantiation need not make the quantifier reifying. That
/// holds only while every value `f` reads over the quantifier is a parameter
/// that handle forces, once, inside its own body, and while `f`'s result is
/// not typed over the quantifier. A parameter read past the handle or beside
/// it, a forced one read a second time, or one forced by another handle
/// answering other effects, arrives at the row its caller built it at, cells
/// where that row names the effect, and reading it as direct code returned a
/// heap cell as a word; such a handle consumes nothing.
fn consumed_on_quantifiers(f: &TypedCoreFn, env: &VerifyEnv) -> BTreeMap<Sym, BTreeSet<Sym>> {
    let params: BTreeSet<Sym> = f.params().iter().map(TypedBinder::name).collect();
    // A name bound by returning a parameter, or another such name, reads as
    // that parameter; the bind that introduces it is not a read of it.
    let mut aliases: BTreeMap<Sym, Sym> = BTreeMap::new();
    let mut introductions: BTreeMap<Sym, usize> = BTreeMap::new();
    let mut pending = vec![f.body()];
    while let Some(comp) = pending.pop() {
        if let TypedCompKind::Bind(head, binder, _) = comp.kind() {
            if let TypedCompKind::Return(value) = head.kind() {
                if let TypedValueKind::Var { name, .. } = &peel(value).kind {
                    let root = *aliases.get(name).unwrap_or(name);
                    if params.contains(&root) {
                        aliases.insert(binder.name(), root);
                        *introductions.entry(root).or_default() += 1;
                    }
                }
            }
        }
        walk::each_subterm(comp, &mut |child| pending.push(child));
    }
    let mut uses: BTreeMap<Sym, usize> = BTreeMap::new();
    walk::each_var(f.body(), &mut |value| {
        if let TypedValueKind::Var { name, .. } = &value.kind {
            *uses.entry(*aliases.get(name).unwrap_or(name)).or_default() += 1;
        }
    });
    let reads = |name: Sym| {
        uses.get(&name).copied().unwrap_or(0) - introductions.get(&name).copied().unwrap_or(0)
    };
    let bounded = |quantifier: Sym, forced: &BTreeSet<usize>| {
        !mentions_row_var(f.sig().body().result(), quantifier)
            && f.params().iter().enumerate().all(|(i, param)| {
                !mentions_row_var(param.ty(), quantifier)
                    || (forced.contains(&i) && reads(param.name()) == 1)
            })
    };
    let mut out: BTreeMap<Sym, BTreeSet<Sym>> = BTreeMap::new();
    let mut pending = vec![f.body()];
    while let Some(comp) = pending.pop() {
        if let TypedCompKind::Handle { body, ops, .. } = comp.kind() {
            if let EffRow::Var(quantifier) = body.sig().effects().tail() {
                if bounded(*quantifier, &forced_within(body, f.params())) {
                    out.entry(*quantifier).or_default().extend(
                        ops.arms()
                            .iter()
                            .filter_map(|arm| env.operation(arm.name()))
                            .map(|operation| operation.effect().name),
                    );
                }
            }
        }
        walk::each_subterm(comp, &mut |child| pending.push(child));
    }
    out
}

/// Whether any row in a type, the rows of the data it names included, is
/// tailed by the variable.
fn mentions_row_var(ty: &CoreType, quantifier: Sym) -> bool {
    let seen = std::cell::Cell::new(false);
    map_rows_ty(ty, &|row| {
        if matches!(row.tail(), EffRow::Var(v) if *v == quantifier) {
            seen.set(true);
        }
        row.clone()
    });
    seen.get()
}

/// The positions of the parameters a handle body forces: the body itself,
/// or the body of a handle nested in it.
fn forced_within(body: &TypedComp, params: &[TypedBinder]) -> BTreeSet<usize> {
    let position = |body: &TypedComp| {
        forced_name(body, &mut BTreeMap::new())
            .and_then(|name| params.iter().position(|p| p.name() == name))
    };
    let mut out: BTreeSet<usize> = position(body).into_iter().collect();
    let mut pending = vec![body];
    while let Some(comp) = pending.pop() {
        if let TypedCompKind::Handle { body, .. } = comp.kind() {
            out.extend(position(body));
        }
        walk::each_subterm(comp, &mut |child| pending.push(child));
    }
    out
}

/// The positions of the parameters a driver in `f` forces: the body of a
/// handle whose clauses answer a reified operation, followed through the
/// names it binds by returning a parameter, down to the thunk it forces.
pub(super) fn driven_params(f: &TypedCoreFn, reified: &BTreeSet<Sym>) -> BTreeSet<usize> {
    let mut driven = BTreeSet::new();
    let mut pending = vec![f.body()];
    while let Some(comp) = pending.pop() {
        if let TypedCompKind::Handle { body, ops, .. } = comp.kind() {
            if ops.arms().iter().any(|arm| reified.contains(&arm.name())) {
                if let Some(name) = forced_name(body, &mut BTreeMap::new()) {
                    driven.extend(f.params().iter().position(|p| p.name() == name));
                }
            }
        }
        walk::each_subterm(comp, &mut |child| pending.push(child));
    }
    driven
}

/// The name a handle body forces, through the names it binds by returning
/// another name.
fn forced_name(body: &TypedComp, aliases: &mut BTreeMap<Sym, Sym>) -> Option<Sym> {
    let named = |value: &TypedValue, aliases: &BTreeMap<Sym, Sym>| match &peel(value).kind {
        TypedValueKind::Var { name, .. } => Some(*aliases.get(name).unwrap_or(name)),
        _ => None,
    };
    match body.kind() {
        TypedCompKind::Bind(head, binder, tail) => {
            if let TypedCompKind::Return(value) = head.kind() {
                if let Some(name) = named(value, aliases) {
                    aliases.insert(binder.name(), name);
                }
            }
            forced_name(tail, aliases)
        }
        TypedCompKind::App { callee, .. } => forced_name(callee, aliases),
        TypedCompKind::Force(thunk) => named(thunk, aliases),
        _ => None,
    }
}

/// A thunk type with the row its body performs closed: the labels it spells
/// and no tail, except a tail spelling `keep`, which stays.
fn close_thunk_row(ty: &CoreType, keep: Option<Sym>) -> CoreType {
    let CoreType::Thunk(sig) = ty else {
        return ty.clone();
    };
    let closed = |row: &EffRow| {
        let tail = match row.tail() {
            EffRow::Var(v) if keep == Some(*v) => EffRow::Var(*v),
            _ => EffRow::Empty,
        };
        EffRow::canonical(row.labels().into_iter().cloned(), tail)
    };
    let sig = match sig.result() {
        CoreType::Function(fun) => CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                fun.quantifiers().to_vec(),
                fun.params().to_vec(),
                CompSig::new(fun.body().result().clone(), closed(fun.body().effects())),
            ))),
            sig.effects().clone(),
        ),
        _ => CompSig::new(sig.result().clone(), closed(sig.effects())),
    };
    CoreType::Thunk(Box::new(sig))
}

/// A thunk type with the reified labels gone from its rows: what a thunk
/// still performs once its reified operations answer with cells.
pub(super) fn residual_type(ty: &CoreType, reified: &BTreeSet<Sym>, env: &VerifyEnv) -> CoreType {
    match ty {
        CoreType::Thunk(sig) => CoreType::Thunk(Box::new(CompSig::new(
            residual_type(sig.result(), reified, env),
            residual_row(sig.effects(), reified, env),
        ))),
        CoreType::Function(fun) => CoreType::Function(Box::new(CoreFnSig::new(
            fun.quantifiers().to_vec(),
            fun.params().to_vec(),
            CompSig::new(
                residual_type(fun.body().result(), reified, env),
                residual_row(fun.body().effects(), reified, env),
            ),
        ))),
        other => other.clone(),
    }
}

/// A call's instantiation with the reified labels gone from its rows.
fn residual_instantiation(
    instantiation: &[CoreInstantiation],
    reified: &BTreeSet<Sym>,
    env: &VerifyEnv,
) -> Vec<CoreInstantiation> {
    instantiation
        .iter()
        .map(|arg| match arg {
            CoreInstantiation::Row(row) => CoreInstantiation::Row(residual_row(row, reified, env)),
            CoreInstantiation::Type(_) => arg.clone(),
        })
        .collect()
}

/// The reified program with its reified labels gone from every row: no code
/// performs them any more, so no type, signature or instantiation may keep
/// naming them, or a value typed where they were struck would not fit a
/// position typed where they were kept. Calls to a host that drives the
/// island are re-signed from its widened signature on top, since the verifier
/// expects each call site to store exactly what its callee's instantiated
/// signature says.
pub(super) struct Resign<'a> {
    pub(super) widened: &'a BTreeMap<Sym, CoreFnSig>,
    pub(super) reified: &'a BTreeSet<Sym>,
    pub(super) env: &'a VerifyEnv,
    pub(super) fresh: &'a mut Fresh,
}

/// A type with every row it mentions mapped, lowered rows included.
/// Whether two types differ only in the rows they spell: a row a data type
/// carries is a phantom of its representation, so a value crosses between
/// such types through the word bridge. Cells code closes the row variables
/// of the function it stands in, while that function's locals still spell
/// them.
fn phantom_rows_apart(have: &CoreType, want: &CoreType) -> bool {
    let closed = |row: &EffRow| EffRow::canonical(row.labels().into_iter().cloned(), EffRow::Empty);
    have != want && map_rows_ty(have, &closed) == map_rows_ty(want, &closed)
}

fn map_rows_ty(ty: &CoreType, map: &impl Fn(&EffRow) -> EffRow) -> CoreType {
    match ty {
        CoreType::Source(source) => CoreType::Source(source.map_rows(map)),
        CoreType::Thunk(sig) => CoreType::Thunk(Box::new(map_rows_sig(sig, map))),
        CoreType::Function(fun) => CoreType::Function(Box::new(map_rows_fun(fun, map))),
        CoreType::Ref(inner) => CoreType::Ref(Box::new(map_rows_ty(inner, map))),
        CoreType::ReuseToken(inner) => CoreType::ReuseToken(Box::new(map_rows_ty(inner, map))),
        CoreType::Lowered(lowered) => CoreType::Lowered(match lowered {
            LoweredType::Word => LoweredType::Word,
            LoweredType::Eff(row) => LoweredType::Eff(map(row)),
            LoweredType::Queue(row) => LoweredType::Queue(map(row)),
            LoweredType::QueueView(row) => LoweredType::QueueView(map(row)),
        }),
    }
}

fn map_rows_sig(sig: &CompSig, map: &impl Fn(&EffRow) -> EffRow) -> CompSig {
    CompSig::new(map_rows_ty(sig.result(), map), map(sig.effects()))
}

fn map_rows_fun(fun: &CoreFnSig, map: &impl Fn(&EffRow) -> EffRow) -> CoreFnSig {
    CoreFnSig::new(
        fun.quantifiers().to_vec(),
        fun.params().iter().map(|ty| map_rows_ty(ty, map)).collect(),
        map_rows_sig(fun.body(), map),
    )
}

/// A rewrite that reads a clause's generic type variables as words: a bare
/// occurrence becomes the word type, and one nested inside a source type,
/// which no word can stand in for, is noted for the caller to refuse.
struct Worded<'a> {
    generic: &'a BTreeSet<Sym>,
    nested: bool,
}

impl Worded<'_> {
    fn ty(&mut self, ty: &CoreType) -> CoreType {
        match ty {
            CoreType::Source(Type::Var(v)) if self.generic.contains(v) => abi::word(),
            CoreType::Source(source) => {
                let mut mentioned = BTreeSet::new();
                source.free_ty_vars(&mut mentioned);
                if !mentioned.is_disjoint(self.generic) {
                    self.nested = true;
                }
                ty.clone()
            }
            CoreType::Thunk(sig) => CoreType::Thunk(Box::new(self.sig(sig))),
            CoreType::Function(fun) => CoreType::Function(Box::new(self.fun(fun))),
            CoreType::Ref(inner) => CoreType::Ref(Box::new(self.ty(inner))),
            CoreType::ReuseToken(inner) => CoreType::ReuseToken(Box::new(self.ty(inner))),
            CoreType::Lowered(_) => ty.clone(),
        }
    }

    fn sig(&mut self, sig: &CompSig) -> CompSig {
        CompSig::new(self.ty(sig.result()), sig.effects().clone())
    }

    fn fun(&mut self, fun: &CoreFnSig) -> CoreFnSig {
        CoreFnSig::new(
            fun.quantifiers().to_vec(),
            fun.params().iter().map(|ty| self.ty(ty)).collect(),
            self.sig(fun.body()),
        )
    }
}

impl Rewrite for Worded<'_> {
    type Ctx = ();

    fn core_type(&mut self, ty: &CoreType, _cx: &Self::Ctx) -> CoreType {
        self.ty(ty)
    }

    /// A bridge from a generic variable to the word is no bridge once the
    /// variable reads as the word itself.
    fn value(&mut self, value: &TypedValue, cx: &Self::Ctx) -> TypedValue {
        let worded = self.descend_value(value, cx);
        if let TypedValueKind::LoweredRepr { value: inner, .. } = &worded.kind {
            if inner.ty() == worded.ty() {
                return (**inner).clone();
            }
        }
        worded
    }

    fn comp_sig(&mut self, sig: &CompSig, _cx: &Self::Ctx) -> CompSig {
        self.sig(sig)
    }

    fn fn_sig(&mut self, sig: &CoreFnSig, _cx: &Self::Ctx) -> CoreFnSig {
        self.fun(sig)
    }

    fn instantiation(
        &mut self,
        instantiation: &CoreInstantiation,
        _cx: &Self::Ctx,
    ) -> CoreInstantiation {
        if let CoreInstantiation::Type(ty) = instantiation {
            let mut mentioned = BTreeSet::new();
            ty.free_ty_vars(&mut mentioned);
            if !mentioned.is_disjoint(self.generic) {
                self.nested = true;
            }
        }
        instantiation.clone()
    }
}

/// A rewrite that maps every row a function mentions: each type, signature
/// and instantiation, and nothing else.
struct RowMap<'a> {
    map: &'a dyn Fn(&EffRow) -> EffRow,
}

impl Rewrite for RowMap<'_> {
    type Ctx = ();

    fn core_type(&mut self, ty: &CoreType, _cx: &Self::Ctx) -> CoreType {
        map_rows_ty(ty, &self.map)
    }

    fn comp_sig(&mut self, sig: &CompSig, _cx: &Self::Ctx) -> CompSig {
        map_rows_sig(sig, &self.map)
    }

    fn fn_sig(&mut self, sig: &CoreFnSig, _cx: &Self::Ctx) -> CoreFnSig {
        map_rows_fun(sig, &self.map)
    }

    fn instantiation(
        &mut self,
        instantiation: &CoreInstantiation,
        _cx: &Self::Ctx,
    ) -> CoreInstantiation {
        match instantiation {
            CoreInstantiation::Row(row) => CoreInstantiation::Row((self.map)(row)),
            CoreInstantiation::Type(ty) => CoreInstantiation::Type(ty.map_rows(&self.map)),
        }
    }
}

/// A row-polymorphic member with the island's row spelled out under its tail.
///
/// The island's row is closed: the labels every member's direct code leaves
/// behind, at every instantiation. A member polymorphic in its row hides its
/// callers' share of those labels behind its tail variable, so the rows its
/// body declares, the resumptions of its handlers among them, name fewer
/// labels than the cells its handlers drive. Extending the tail with the
/// labels the member's own row lacks makes every row in the body admit the
/// cells; a caller's instantiation of the tail then merges per label.
pub(super) fn extend_tail(
    f: &TypedCoreFn,
    cells: &EffRow,
    ops: &BTreeSet<Sym>,
    env: &VerifyEnv,
) -> TypedCoreFn {
    let declared = f.sig().body().effects();
    let EffRow::Var(tail) = declared.tail() else {
        return f.clone();
    };
    let own = residual_row(declared, ops, env);
    let extra: Vec<Label> = cells
        .labels()
        .into_iter()
        .filter(|label| !own.labels().iter().any(|mine| mine.name == label.name))
        .cloned()
        .collect();
    if extra.is_empty() {
        return f.clone();
    }
    // A row in the body that names one of those labels itself already
    // admits it, and keeps one copy: the extension fills in what the row
    // lacks, and never doubles a label.
    let map = |row: &EffRow| {
        if !matches!(row.tail(), EffRow::Var(v) if v == tail) {
            return row.clone();
        }
        let named: Vec<Label> = row.labels().into_iter().cloned().collect();
        let added: Vec<Label> = extra
            .iter()
            .filter(|label| !named.iter().any(|mine| mine.name == label.name))
            .cloned()
            .collect();
        EffRow::canonical(named.into_iter().chain(added), EffRow::Var(*tail))
    };
    RowMap { map: &map }.function(f, &())
}

impl Resign<'_> {
    fn row(&self, row: &EffRow) -> EffRow {
        residual_row(row, self.reified, self.env)
    }

    /// A constructor's declaration is not rewritten, so a field it spells
    /// itself keeps naming the reified labels, and the binder matching it is
    /// typed from the declaration, as the verifier reads it. The arm then
    /// rebinds such a binder at the type the rest of the program reads it
    /// at, across the word bridge every cell boundary crosses: what the
    /// field holds is cells already, built where the labels were struck.
    fn arm(&mut self, pattern: &TypedPattern, body: &TypedComp) -> (TypedPattern, TypedComp) {
        let mut pattern = self.pattern(pattern, &());
        let mut body = self.comp(body, &());
        let TypedPattern::Ctor { fields, .. } = &mut pattern else {
            return (pattern, body);
        };
        for binder in fields.iter_mut().flatten() {
            let residual = map_rows_ty(binder.ty(), &|row| {
                residual_row(row, self.reified, self.env)
            });
            if residual == *binder.ty() {
                continue;
            }
            let spelled = Sym::from(names::lowered(binder.name().as_str(), self.fresh.bump()));
            let Some(bridged) =
                abi::try_word_bridge(var(spelled, binder.ty().clone()), residual.clone())
            else {
                continue;
            };
            let head = TypedComp::new(
                CompSig::new(residual.clone(), EffRow::Empty),
                TypedCompKind::Return(bridged),
            );
            body = TypedComp::new(
                body.sig().clone(),
                TypedCompKind::Bind(
                    Box::new(head),
                    TypedBinder::new(binder.name(), residual),
                    Box::new(body),
                ),
            );
            *binder = TypedBinder::new(spelled, binder.ty().clone());
        }
        (pattern, body)
    }
}

impl Rewrite for Resign<'_> {
    type Ctx = ();

    fn core_type(&mut self, ty: &CoreType, _cx: &Self::Ctx) -> CoreType {
        map_rows_ty(ty, &|row| self.row(row))
    }

    fn comp_sig(&mut self, sig: &CompSig, _cx: &Self::Ctx) -> CompSig {
        map_rows_sig(sig, &|row| self.row(row))
    }

    fn fn_sig(&mut self, sig: &CoreFnSig, _cx: &Self::Ctx) -> CoreFnSig {
        map_rows_fun(sig, &|row| self.row(row))
    }

    fn instantiation(
        &mut self,
        instantiation: &CoreInstantiation,
        _cx: &Self::Ctx,
    ) -> CoreInstantiation {
        match instantiation {
            CoreInstantiation::Row(row) => CoreInstantiation::Row(self.row(row)),
            CoreInstantiation::Type(ty) => {
                CoreInstantiation::Type(ty.map_rows(&|row| self.row(row)))
            }
        }
    }

    // Constructor field binders are typed from the declaration; see `arm`.
    fn pattern(&mut self, pattern: &TypedPattern, cx: &Self::Ctx) -> TypedPattern {
        let TypedPattern::Ctor {
            name,
            instantiation,
            fields,
        } = pattern
        else {
            return match pattern {
                TypedPattern::Wild => TypedPattern::Wild,
                TypedPattern::Var(binder) => TypedPattern::Var(self.binder(binder, cx)),
                TypedPattern::Tuple(fields) => TypedPattern::Tuple(
                    fields
                        .iter()
                        .map(|binder| binder.as_ref().map(|binder| self.binder(binder, cx)))
                        .collect(),
                ),
                TypedPattern::Ctor { .. } => unreachable!("matched above"),
            };
        };
        let instantiation = self.instantiations(instantiation, cx);
        let mono = self
            .env
            .constructor(*name)
            .and_then(|declared| instantiate_constructor(declared, &instantiation).ok());
        let fields = fields
            .iter()
            .enumerate()
            .map(|(index, binder)| {
                let binder = binder.as_ref()?;
                Some(
                    mono.as_ref()
                        .and_then(|mono| mono.fields.get(index))
                        .map_or_else(
                            || self.binder(binder, cx),
                            |ty| TypedBinder::new(binder.name(), ty.clone()),
                        ),
                )
            })
            .collect();
        TypedPattern::Ctor {
            name: *name,
            instantiation,
            fields,
        }
    }

    fn comp(&mut self, comp: &TypedComp, cx: &Self::Ctx) -> TypedComp {
        if let TypedCompKind::Case(scrutinee, arms) = comp.kind() {
            let scrutinee = self.value(scrutinee, cx);
            let arms = arms
                .iter()
                .map(|(pattern, body)| self.arm(pattern, body))
                .collect();
            return TypedComp::new(
                self.comp_sig(comp.sig(), cx),
                TypedCompKind::Case(scrutinee, arms),
            );
        }
        let rebuilt = self.descend_comp(comp, cx);
        let TypedCompKind::Call {
            callee,
            instantiation,
            ..
        } = rebuilt.kind()
        else {
            return rebuilt;
        };
        let Some(sig) = self.widened.get(callee) else {
            return rebuilt;
        };
        match instantiate_fn(sig, instantiation) {
            Ok(applied) => TypedComp::new(applied.body().clone(), rebuilt.kind().clone()),
            Err(_) => rebuilt,
        }
    }
}

#[cfg(test)]
mod tests {
    use prism_common::fresh::Fresh;

    use super::super::super::fixtures::{int, nullary_thunk};
    use super::super::super::flow::{Carriers, Sig};
    use super::super::super::latent::MaskOp;
    use super::super::tests::env_with;
    use super::*;

    const TICK: &str = "Tick.tick";

    /// The type of a suspended nullary computation over an open row.
    fn suspended(tail: &str) -> CoreType {
        let effects = EffRow::Var(Sym::new(tail));
        CoreType::Thunk(Box::new(CompSig::new(
            CoreType::Function(Box::new(CoreFnSig::new(
                Vec::new(),
                Vec::new(),
                CompSig::new(int(), effects),
            ))),
            EffRow::Empty,
        )))
    }

    fn returning(effects: EffRow) -> TypedComp {
        TypedComp::new(
            CompSig::new(int(), effects),
            TypedCompKind::Return(TypedValue::new(int(), TypedValueKind::Int(0))),
        )
    }

    /// `f` is quantified over `e` and `r`, takes one thunk typed over each
    /// and forces neither; `main` instantiates `e` at the reified effect and
    /// `r` at the empty row.
    fn program() -> Vec<TypedCoreFn> {
        let a = TypedBinder::new(Sym::new("a"), suspended("e"));
        let b = TypedBinder::new(Sym::new("b"), suspended("r"));
        let body = returning(EffRow::Var(Sym::new("e")));
        let sig = CoreFnSig::new(
            vec![
                CoreQuantifier::Row(Sym::new("e")),
                CoreQuantifier::Row(Sym::new("r")),
            ],
            vec![a.ty().clone(), b.ty().clone()],
            body.sig().clone(),
        );
        let f = TypedCoreFn::new(Sym::new("f"), vec![a, b], body, sig, 0);
        let ticking = EffRow::singleton("Tick");
        let performing = TypedComp::new(
            CompSig::new(int(), ticking.clone()),
            TypedCompKind::Do {
                operation: Sym::new(TICK),
                instantiation: Vec::new(),
                args: Vec::new(),
            },
        );
        let call = TypedComp::new(
            CompSig::new(int(), ticking.clone()),
            TypedCompKind::Call {
                callee: Sym::new("f"),
                instantiation: vec![
                    CoreInstantiation::Row(ticking.clone()),
                    CoreInstantiation::Row(EffRow::Empty),
                ],
                args: vec![
                    nullary_thunk(performing),
                    nullary_thunk(returning(EffRow::Empty)),
                ],
            },
        );
        let sig = CoreFnSig::new(Vec::new(), Vec::new(), CompSig::new(int(), ticking));
        let main = TypedCoreFn::new(Sym::new("main"), Vec::new(), call, sig, 0);
        vec![f, main]
    }

    /// The descriptors `enter` gives `f`'s parameters under a flow, once the
    /// instantiation fixpoint has made `e` reifying for it.
    fn descriptors_under(flow: &ThunkFlow) -> BTreeMap<Sym, Carrier> {
        let fns = program();
        let env = env_with(&[(TICK, "Tick", Type::Int)]);
        let cells = BTreeSet::from([Sym::new(TICK)]);
        let ids = OpIds::assign(&cells).expect("one operation");
        let quantified = reifying_quantifiers(&fns, &cells, &env);
        let own = BTreeSet::from([Sym::new("e")]);
        assert_eq!(quantified.get(&Sym::new("f")), Some(&own));
        let members = BTreeSet::from([Sym::new("f")]);
        let sigs: BTreeMap<Sym, CoreFnSig> =
            fns.iter().map(|f| (f.name(), f.sig().clone())).collect();
        let driven = BTreeMap::new();
        let extended = BTreeSet::new();
        let latent = Latent::new();
        let row = EffRow::singleton("Tick");
        let mut fresh = Fresh::new();
        let ambients = BTreeMap::new();
        let mut reifier = Reifier {
            row: row.clone(),
            island: row.clone(),
            home: row,
            ambients: &ambients,
            ambient: EffRow::Empty,
            reified: &cells,
            fused: &cells,
            members: &members,
            env: &env,
            ids: &ids,
            flow,
            driven: &driven,
            sigs: &sigs,
            extended: &extended,
            latent: &latent,
            open: false,
            answering: None,
            names: BTreeMap::new(),
            reifying_quantifiers: &quantified,
            reifying: BTreeSet::new(),
            drivers: Vec::new(),
            answer: None,
            quantifiers: Vec::new(),
            fresh: &mut fresh,
            why: None,
        };
        reifier.enter(&fns[0]).expect("the rows join");
        reifier.names
    }

    fn flow_with(param: BTreeMap<Sym, Vec<Sig>>) -> ThunkFlow {
        ThunkFlow {
            ret: BTreeMap::new(),
            param,
            carriers: Carriers::none(),
        }
    }

    // The parameter over the reifying quantifier that nothing reaches reads
    // direct, whatever row its type spells; the one over the quantifier no
    // caller instantiates at a reified effect has no descriptor.
    #[test]
    fn a_parameter_over_a_reifying_quantifier_nothing_reaches_reads_direct() {
        let names = descriptors_under(&flow_with(BTreeMap::new()));
        assert_eq!(
            names.get(&Sym::new("a")),
            Some(&Carrier::own(Reading::Direct))
        );
        assert_eq!(names.get(&Sym::new("b")), None);
    }

    // The same parameter reads cells once the flow says the reified
    // operation reaches it: the flow's answer wins over the type's.
    #[test]
    fn a_parameter_a_reified_operation_reaches_reads_cells() {
        let reaching = Sig::from([MaskOp {
            id: Sym::new(TICK),
            depth: 0,
        }]);
        let param = BTreeMap::from([(Sym::new("f"), vec![reaching, Sig::new()])]);
        let names = descriptors_under(&flow_with(param));
        assert_eq!(
            names.get(&Sym::new("a")),
            Some(&Carrier::own(Reading::Cells))
        );
        assert_eq!(names.get(&Sym::new("b")), None);
    }
}
