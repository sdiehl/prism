use marginalia::Span;

use super::defaulting::NumClass;
use crate::error::{ErrKind, TypeError};
use crate::sym::Sym;
use crate::syntax::ast::{self, BinOp, Core, Expr, NodeId, S};
use crate::types::ty::{Type, DIV_CLASS, EQ_CLASS, NUM_CLASS, ORD_CLASS};

use super::super::{Env, Tc, Wanted};

impl Tc<'_> {
    pub(super) fn lit_range(lit: &ast::IntLit, ty: &Type, span: Span) -> Result<(), TypeError> {
        let max = match ty {
            Type::I64 => ast::BigInt::from(i64::MAX),
            _ => ast::BigInt::from(u64::MAX),
        };
        if lit.value > max {
            return Err(ErrKind::IntLiteralOutOfRange { ty: ty.show() }.at(span));
        }
        Ok(())
    }

    // The numeric defaulting rule, in one place: an ambiguous operand defaults
    // to `Int`. `==`/`!=` invoke it for an unconstrained (existential) operand;
    // the ordered and arithmetic operators invoke it for any operand that is not
    // already a fixed-width integer. This is the only site the `Int` literal and
    // its `subtype` decision live, so Eq and Ord share one rule.
    pub(in crate::tc) fn default_numeric(
        &mut self,
        ty: &Type,
        span: Span,
    ) -> Result<Type, TypeError> {
        self.subtype(ty, &Type::Int).map_err(|e| {
            e.or(TypeError::TypeMismatch {
                span,
                expected: Type::Int.show(),
                found: ty.show(),
            })
        })?;
        Ok(Type::Int)
    }

    // The defer-or-fix ladder shared by every numeric/comparison operator, over
    // the already-applied left-operand type `t`. `Int` is the default lane and is
    // accepted as-is; a fixed-width lane pins `id` so later width inference agrees;
    // an unsolved existential defers to the `resolve_all` pass, where a still-later
    // use can pin its width before the `Int` default fires. Only the leftover case
    // differs per operator family (`NumClass`), and `blame` is the span the
    // numeric rejection points at. Callers own the operator's result type; this
    // only records the classification side effects.
    fn numeric_ladder(
        &mut self,
        class: NumClass,
        t: &Type,
        id: NodeId,
        span: Span,
        blame: Span,
    ) -> Result<(), TypeError> {
        match t {
            Type::Int => Ok(()),
            Type::I64 | Type::U64 => {
                self.fixed.insert(id, t.clone());
                Ok(())
            }
            Type::Exist(_) => {
                let deferred_class = match class {
                    NumClass::Eq => Some(EQ_CLASS),
                    NumClass::Ord => Some(ORD_CLASS),
                    NumClass::Arith => None,
                };
                self.num_default.push((id, span, t.clone(), deferred_class));
                Ok(())
            }
            _ => match class {
                NumClass::Eq => match t {
                    Type::Float | Type::Bool | Type::Str => {
                        self.fixed.insert(id, t.clone());
                        Ok(())
                    }
                    _ => {
                        self.wanted.push(Wanted {
                            id,
                            span,
                            items: vec![(EQ_CLASS.into(), t.clone(), None)],
                        });
                        Ok(())
                    }
                },
                NumClass::Ord => {
                    if matches!(t, Type::Float) {
                        self.fixed.insert(id, t.clone());
                    } else {
                        self.wanted.push(Wanted {
                            id,
                            span,
                            items: vec![(ORD_CLASS.into(), t.clone(), None)],
                        });
                    }
                    Ok(())
                }
                NumClass::Arith => match t {
                    // `Float` joined the arithmetic operators with the tower;
                    // record the lane for the elaborator like the fixed-width
                    // lanes. Anything else here is a non-numeric operand (a
                    // deferred existential that unified with, say, `String`), still
                    // rejected blaming the operand.
                    Type::Float => {
                        self.fixed.insert(id, t.clone());
                        Ok(())
                    }
                    _ => self.default_numeric(t, blame).map(|_| ()),
                },
            },
        }
    }

    // Which tower class an arithmetic operator dispatches through: `+`/`-`/`*`
    // carry `Num`, `/`/`%` carry `Div`. Only the arithmetic ops reach this (the
    // comparison and boolean ops are handled on their own `synth_bin` arms).
    const fn arith_class(op: BinOp) -> &'static str {
        match op {
            BinOp::Div | BinOp::Rem => DIV_CLASS,
            _ => NUM_CLASS,
        }
    }

    // Whether the rigid type variable `v` carries a `Num` constraint in the
    // current declaration's `given` clause. A signature variable is stored in the
    // constraint list verbatim (rigid, never an existential), so this is a direct
    // match with no zonking. Gates the polymorphic-literal `check` arm so a
    // literal only adopts a variable the signature actually promised is numeric.
    pub(super) fn num_var_in_scope(&self, v: Sym) -> bool {
        self.cur_self.as_ref().is_some_and(|s| {
            s.constraints
                .iter()
                .any(|(c, t)| c == NUM_CLASS && matches!(t, Type::Var(cv) if *cv == v))
        })
    }

    // The signed lanes unary minus is defined on, in one place so `synth_neg`,
    // `neg_lane`, and the `check` fast path agree.
    pub(in crate::tc) fn neg_unsigned(span: Span) -> TypeError {
        ErrKind::NegateUnsigned.at(span)
    }

    // A bare integer literal (no width suffix), the operand shape a leading minus
    // folds against so `-5` can take a fixed-width lane from its context exactly
    // as `5` does.
    pub(super) fn bare_int_lit(e: &S<Expr<Core>>) -> Option<&ast::IntLit> {
        match &e.node {
            Expr::Int(lit) if lit.suffix == ast::Suffix::None => Some(lit),
            _ => None,
        }
    }

    // Classify a unary-minus whose operand type is already applied. The lane is
    // recorded on the node for the elaborator (I64 wrap, Float sign flip); `Int`
    // is the default and needs no record; `U64` is rejected; an unsolved operand
    // defers to `resolve_all`.
    fn neg_lane(&mut self, t: &Type, id: NodeId, span: Span) -> Result<Type, TypeError> {
        match t {
            Type::Int => Ok(Type::Int),
            Type::I64 | Type::Float => {
                self.fixed.insert(id, t.clone());
                Ok(t.clone())
            }
            Type::U64 => Err(Self::neg_unsigned(span)),
            Type::Exist(_) => {
                self.neg_default.push((id, span, t.clone()));
                Ok(t.clone())
            }
            // A `given Num(a)` operand dispatches unary minus through the class's
            // `negated` method, exactly as the binary operators raise `Num`;
            // resolution finds the dictionary, or reports "no instance" for a
            // genuinely non-numeric operand.
            other => {
                self.wanted.push(Wanted {
                    id,
                    span,
                    items: vec![(NUM_CLASS.into(), other.clone(), None)],
                });
                Ok(other.clone())
            }
        }
    }

    // Unary minus. Defined on the signed lanes only: `Int` (exact bignum), `I64`
    // (two's-complement wrap), and `Float` (IEEE sign flip). A literal operand
    // folds the minus into its magnitude, so `-9223372036854775808i64` is the
    // I64 minimum (one past the positive max) while the bare positive literal is
    // out of range; the negated value is what gets range-checked.
    pub(super) fn synth_neg(
        &mut self,
        env: &Env,
        e: &S<Expr<Core>>,
        id: NodeId,
        span: Span,
    ) -> Result<Type, TypeError> {
        if let Expr::Int(lit) = &e.node {
            let ty = match lit.suffix {
                ast::Suffix::None => return Ok(Type::Int),
                ast::Suffix::I64 => Type::I64,
                ast::Suffix::U64 => return Err(Self::neg_unsigned(span)),
            };
            let negated = ast::IntLit {
                value: -lit.value.clone(),
                suffix: lit.suffix,
            };
            Self::lit_range(&negated, &ty, span)?;
            self.fixed.insert(id, ty.clone());
            return Ok(ty);
        }
        if matches!(&e.node, Expr::Float(_)) {
            return Ok(Type::Float);
        }
        let t = self.synth(env, e)?;
        let t = self.apply(&t);
        self.neg_lane(&t, id, span)
    }

    pub(super) fn synth_bin(
        &mut self,
        env: &Env,
        op: BinOp,
        a: &S<Expr<Core>>,
        b: &S<Expr<Core>>,
        id: NodeId,
        span: Span,
    ) -> Result<Type, TypeError> {
        match op {
            BinOp::And | BinOp::Or => {
                self.check(env, a, &Type::Bool)?;
                self.check(env, b, &Type::Bool)?;
                Ok(Type::Bool)
            }
            BinOp::Eq | BinOp::Ne => {
                let ta = self.synth(env, a)?;
                let ta = self.apply(&ta);
                let ta = self.instantiate_constrained(&ta, &[], id, span, None);
                self.check(env, b, &ta)?;
                let ta = self.apply(&ta);
                self.numeric_ladder(NumClass::Eq, &ta, id, span, a.span)?;
                Ok(Type::Bool)
            }
            BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                let ta = self.synth(env, a)?;
                let ta = self.apply(&ta);
                let ta = self.instantiate_constrained(&ta, &[], id, span, None);
                self.check(env, b, &ta)?;
                let ta = self.apply(&ta);
                self.numeric_ladder(NumClass::Ord, &ta, id, span, a.span)?;
                Ok(Type::Bool)
            }
            _ => {
                // The tower arithmetic operators `+`/`-`/`*` (dispatched through
                // `Num`) and `/`/`%` (through `Div`). A concrete lane drives the
                // operator directly: a fixed-width or `Float` lane fixes both sides
                // and keeps the direct primitive (byte-identical Core, no
                // dictionary). An unsolved existential left operand is not
                // defaulted to `Int` here; check the right operand against it (so
                // the right can pin the lane), and if both stay ambiguous defer to
                // one pass at `resolve_all` where a later use can still fix the
                // width. This lets `y + x` with `x : I64` type when `y` was left
                // open. Anything else (a `given Num(a)` rigid variable, or a
                // non-numeric operand) raises the class constraint exactly as
                // `==`/`<` raise `Eq`/`Ord`; resolution finds the dictionary or
                // reports "no instance", the honest error for a non-numeric lane.
                let ta = self.synth(env, a)?;
                let ta = self.apply(&ta);
                let t = match &ta {
                    Type::I64 | Type::U64 | Type::Float => {
                        self.check(env, b, &ta)?;
                        self.fixed.insert(id, ta.clone());
                        ta
                    }
                    Type::Int => {
                        self.check(env, b, &ta)?;
                        ta
                    }
                    Type::Exist(_) => {
                        self.check(env, b, &ta)?;
                        let t = self.apply(&ta);
                        self.numeric_ladder(NumClass::Arith, &t, id, span, b.span)?;
                        t
                    }
                    other => {
                        // Relate the right operand to the left only for a type that
                        // might carry an instance (a variable, or a nominal type). A
                        // concrete non-numeric primitive (`Bool`, `String`, ...)
                        // carries none, so raise the obligation on its own type and
                        // skip the operand check, whose "expected Bool, got Int"
                        // would misleadingly blame a literal right operand for the
                        // left operand not being numeric.
                        if matches!(other, Type::Var(_) | Type::Con(..) | Type::App(..)) {
                            self.check(env, b, &ta)?;
                        }
                        self.wanted.push(Wanted {
                            id,
                            span,
                            items: vec![(Self::arith_class(op).into(), ta.clone(), None)],
                        });
                        ta
                    }
                };
                Ok(t)
            }
        }
    }
}
