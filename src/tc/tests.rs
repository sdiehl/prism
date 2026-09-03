//! Whole-program checker tests: annotation acceptance, typed holes,
//! residual-operation accounting, and handler return-arm defaults.

mod data_annotation_tests {
    use crate::parse::parse;
    use crate::resolve::resolve;
    use crate::syntax::desugar::desugar;
    use crate::tc::check;

    #[test]
    fn unknown_constructor_field_type_is_rejected_during_checking() {
        let surface = parse("type Target = Plain | Wrapped(MissingType)")
            .expect("parse datatype fixture")
            .program;
        let resolved = resolve(surface).expect("resolve datatype fixture");
        let program = desugar(resolved).expect("desugar datatype fixture");

        let error = check(&program).expect_err("unknown field type must not reach elaboration");
        assert_eq!(error.code(), Some("E1001"), "{error}");
        assert!(error.to_string().contains("unknown type `MissingType`"));
    }
}

mod typed_hole_tests {
    use crate::parse::parse;
    use crate::resolve::resolve;
    use crate::syntax::desugar::desugar;
    use crate::tc::{check, check_allow_holes};

    fn core(src: &str) -> crate::syntax::ast::Program<crate::syntax::ast::Core> {
        let surface = parse(src).expect("parse typed-hole fixture").program;
        let resolved = resolve(surface).expect("resolve typed-hole fixture");
        desugar(resolved).expect("desugar typed-hole fixture")
    }

    #[test]
    fn report_is_structured_ranked_and_effect_aware() {
        let program = core("fn choose(x : Int, y : Bool) : Int ! {} = ?answer");
        let checked = check_allow_holes(&program).expect("holes are retained in allow mode");
        let [hole] = checked.reports.holes.as_slice() else {
            panic!("expected one hole report, got {:?}", checked.reports.holes);
        };
        assert_eq!(hole.name, "answer");
        assert_eq!(hole.expected, "Int");
        assert_eq!(hole.effects, "{}");
        assert!(hole.bindings.iter().any(|b| b.name == "x" && b.ty == "Int"));
        assert_eq!(hole.candidates.first().map(|c| c.name.as_str()), Some("x"));
        assert!(hole.candidates[0].exact);
        let json = serde_json::to_value(hole).expect("hole payload serializes");
        assert_eq!(json["expected"], "Int");
        assert_eq!(json["effects"], "{}");
    }

    #[test]
    fn ordinary_check_rejects_holes_with_the_dedicated_code() {
        let program = core("fn main() : Int = ?todo");
        let error = check(&program).expect_err("ordinary checking must reject holes");
        assert_eq!(error.code(), Some(crate::error::TYPED_HOLE.as_str()));
    }

    #[test]
    fn inferred_context_reports_an_open_effect_row() {
        let program = core("fn main() : Int = ?todo");
        let checked = check_allow_holes(&program).expect("allow mode");
        assert_eq!(checked.reports.holes[0].effects, "{| e0}");
    }

    #[test]
    fn annotated_lambda_reports_its_open_effect_permission() {
        let program = core(
            "fn main() : (() -> Int ! {Exn | e}) = \
             ((\\() -> ?todo) : () -> Int ! {Exn | e})",
        );
        let checked = check_allow_holes(&program).expect("allow mode");
        assert_eq!(checked.reports.holes[0].expected, "Int");
        assert_eq!(checked.reports.holes[0].effects, "{Exn | e0}");
    }

    #[test]
    fn polymorphic_candidates_are_ranked_by_real_subsumption() {
        let program = core(
            "fn identity(x) = x\n\
             fn main() : ((Int) -> Int) ! {} = ?answer",
        );
        let checked = check_allow_holes(&program).expect("allow mode");
        let identity = checked.reports.holes[0]
            .candidates
            .iter()
            .find(|candidate| candidate.name == "identity")
            .expect("polymorphic identity subsumes Int -> Int");
        assert!(
            !identity.exact,
            "instantiation is compatible, not identical"
        );
    }
}

mod residual_operation_tests {
    use crate::hir::{build, HandlerResidual};
    use crate::parse::parse;
    use crate::resolve::resolve;
    use crate::syntax::ast::{Core, Expr, NodeId, Program};
    use crate::syntax::desugar::desugar;
    use crate::tc::{check, Checked};

    fn core(src: &str) -> Program<Core> {
        let surface = parse(src).expect("parse residual fixture").program;
        let resolved = resolve(surface).expect("resolve residual fixture");
        desugar(resolved).expect("desugar residual fixture")
    }

    fn checked(src: &str) -> (Program<Core>, Checked) {
        let program = core(src);
        let checked = check(&program).expect("check residual fixture");
        (program, checked)
    }

    fn function_body(program: &Program<Core>, name: &str) -> NodeId {
        program
            .fns
            .iter()
            .find(|function| function.name == name)
            .expect("fixture function")
            .body
            .id
    }

    fn residual<'a>(
        program: &Program<Core>,
        checked: &'a Checked,
        function: &str,
    ) -> &'a HandlerResidual {
        build(checked)
            .handler_residual(function_body(program, function))
            .expect("handler residual fact")
    }

    fn names(symbols: &[crate::sym::Sym]) -> Vec<&'static str> {
        symbols.iter().map(|symbol| symbol.as_str()).collect()
    }

    const ADJACENT: &str = "
effect E
  one() : Int
  two() : Int

fn run() : Int ! {} =
  handle (handle one() + two() with partial {
    one() resume k => k(1),
    return r => r
  }) with partial {
    two() resume k => k(2),
    return r => r
  }
";

    #[test]
    fn adjacent_inline_partials_cancel_known_operation_subsets() {
        let (program, checked) = checked(ADJACENT);
        assert!(checked.defs.decls[0].effects.is_empty());
        let outer = residual(&program, &checked, "run");
        assert!(outer.forwarded_operations().is_empty());
        assert!(outer.residual_operations().is_empty());
        assert!(outer.forwarded_effects().is_empty());
        assert!(!outer.has_open_row());

        let run = program
            .fns
            .iter()
            .find(|function| function.name == "run")
            .expect("run");
        let Expr::Handle(inner, ..) = &run.body.node else {
            panic!("run body must be the outer handler");
        };
        let inner = build(&checked)
            .handler_residual(inner.id)
            .expect("inner residual");
        assert_eq!(names(inner.forwarded_operations()), ["two"]);
        assert_eq!(names(inner.residual_operations()), ["two"]);
    }

    #[test]
    fn signature_rows_remain_opaque_across_adjacent_partials() {
        let source = ADJACENT.replace(
            "fn run() : Int ! {} =\n  handle (handle one() + two()",
            "fn work() : Int ! {E} = one() + two()\n\nfn run() : Int ! {E} =\n  handle (handle work()",
        );
        let (program, checked) = checked(&source);
        let run = checked
            .defs
            .decls
            .iter()
            .find(|decl| decl.name == "run")
            .expect("run declaration");
        assert!(run.effects.iter().any(|effect| effect.as_str() == "E"));
        let outer = residual(&program, &checked, "run");
        assert_eq!(names(outer.forwarded_effects()), ["E"]);
        assert_eq!(names(outer.residual_effects()), ["E"]);

        let pure = source.replace("fn run() : Int ! {E}", "fn run() : Int ! {}");
        let program = core(&pure);
        check(&program).expect_err("an opaque signature row must not become locally pure");
    }

    #[test]
    fn handler_arm_uses_are_unioned_into_the_residual() {
        let (program, checked) = checked(
            r"effect E
  one() : Int
  two() : Int

fn run() : Int ! {E} =
  handle one() with partial {
    one() resume k => two(),
    return r => r
  }",
        );
        let fact = residual(&program, &checked, "run");
        assert!(fact.forwarded_operations().is_empty());
        assert_eq!(names(fact.residual_operations()), ["two"]);
    }

    #[test]
    fn mask_forces_the_skipped_effect_to_remain_opaque() {
        let (program, checked) = checked(
            r"effect E
  one() : Int
  two() : Int

fn run() : Int ! {E} =
  handle mask<E>(one()) with partial {
    one() resume k => k(1),
    return r => r
  }",
        );
        let fact = residual(&program, &checked, "run");
        assert_eq!(names(fact.forwarded_operations()), ["one"]);
        assert_eq!(names(fact.residual_operations()), ["one"]);
    }

    #[test]
    fn outer_partial_cancels_the_known_operation_masked_past_inner() {
        let (program, checked) = checked(
            r"effect E
  one() : Int
  two() : Int

fn run() : Int ! {} =
  handle (handle mask<E>(one()) with partial {
    one() resume k => k(1),
    return r => r
  }) with partial {
    one() resume k => k(1),
    return r => r
  }",
        );
        let fact = residual(&program, &checked, "run");
        assert!(fact.residual_operations().is_empty());
        assert!(fact.residual_effects().is_empty());
    }

    // A binder that shadows the continuation's name is a different binding, so
    // the continuation's exact summary must not answer for it. `helper`'s row is
    // the only place `other` appears, so borrowing the summary would drop it.
    #[test]
    fn a_binder_shadowing_the_continuation_loses_its_precision() {
        let (program, checked) = checked(
            r"effect E
  one() : Int

effect F
  other() : Int

fn helper() : Int ! {F} = other()

fn run() : Int ! {F} =
  handle one() with partial {
    one() resume k => (\(k) -> k())(helper),
    return r => r
  }",
        );
        let fact = residual(&program, &checked, "run");
        assert!(
            fact.residual_operations().is_empty(),
            "the shadowed continuation's `one` must not be attributed to the inner `k`"
        );
        assert!(
            fact.has_open_row(),
            "an unknown callee's row stays opaque, {fact:?}"
        );
    }

    #[test]
    fn pure_mask_does_not_borrow_prior_same_effect_precision() {
        let (program, checked) = checked(
            r"effect E
  one() : Int
  two() : Int

fn run() : Int ! {E} =
  handle (handle one() + mask<E>(5) with partial {
    one() resume k => k(1),
    return r => r
  }) with partial {
    one() resume k => k(1),
    return r => r
  }",
        );
        let fact = residual(&program, &checked, "run");
        assert_eq!(names(fact.forwarded_effects()), ["E"]);
        assert_eq!(names(fact.residual_effects()), ["E"]);
    }

    #[test]
    fn parametric_direct_operation_keeps_singleton_precision() {
        let (_, checked) = checked(
            r"effect Choice(a)
  first(a) : a
  second(a) : a

fn run() : Int ! {} =
  handle first(1) with partial {
    first(x) resume k => k(x),
    return r => r
  }",
        );
        assert!(checked.defs.decls[0].effects.is_empty());
    }

    #[test]
    fn thunk_operation_retains_its_latent_effect_row() {
        let (program, checked) = checked(
            r"effect Out
  out() : Int

effect Wrap
  wrap(() -> Int ! {Wrap | e}) : Int

fn run() : Int ! {Out, Wrap} =
  handle wrap(\() -> out()) with partial {
    wrap(th) resume k => k(0),
    return r => r
  }",
        );
        let run = checked
            .defs
            .decls
            .iter()
            .find(|decl| decl.name == "run")
            .expect("run declaration");
        assert!(run.effects.iter().any(|effect| effect.as_str() == "Out"));
        assert!(run.effects.iter().any(|effect| effect.as_str() == "Wrap"));
        let fact = residual(&program, &checked, "run");
        assert!(fact.residual_operations().is_empty());
        assert_eq!(names(fact.forwarded_effects()), ["Wrap"]);
        assert_eq!(names(fact.residual_effects()), ["Out", "Wrap"]);
        assert!(fact.has_open_row());
    }

    #[test]
    fn synthesized_lambda_keeps_latent_operations_out_of_handler_residual() {
        let (program, checked) = checked(
            r"effect E
  one() : Int
  two() : Int

fn make() : (() -> Int ! {E}) =
  handle (\() -> two()) with partial {
    one() resume k => k(1),
    return f => f
  }",
        );
        let make = checked
            .defs
            .decls
            .iter()
            .find(|decl| decl.name == "make")
            .expect("make declaration");
        assert!(make.effects.is_empty());
        let fact = residual(&program, &checked, "make");
        assert!(fact.residual_operations().is_empty());
        assert!(fact.residual_effects().is_empty());
    }

    #[test]
    fn builtin_opaque_residual_is_valid_checked_hir() {
        let (program, checked) = checked(
            r"effect E
  one() : Int

fn run() : Unit ! {IO} =
  handle one() with partial {
    one() resume k => let _ = k(1) in mask<IO>(()),
    return r => ()
  }",
        );
        let fact = residual(&program, &checked, "run");
        assert_eq!(names(fact.residual_effects()), ["IO"]);
    }

    #[test]
    fn operation_precision_does_not_cross_declaration_boundaries() {
        let (program, checked) = checked(
            r"effect Out
  out() : Int

effect Wrap
  wrap(() -> Int ! {Wrap | e}) : Int

effect E
  one() : Int
  two() : Int

fn leaves_open() : Int ! {Out, Wrap} = wrap(\() -> out())

fn clean() : Int ! {} =
  handle one() with partial {
    one() resume k => k(1),
    return r => r
  }",
        );
        let fact = residual(&program, &checked, "clean");
        assert!(fact.residual_operations().is_empty());
        assert!(fact.residual_effects().is_empty());
        assert!(!fact.has_open_row());
    }
}

mod handler_return_tests {
    use crate::parse::parse;
    use crate::resolve::resolve;
    use crate::syntax::ast::{Core, Program};
    use crate::syntax::desugar::desugar;
    use crate::tc::check;

    fn core(src: &str) -> Program<Core> {
        let surface = parse(src).expect("parse handler fixture").program;
        let resolved = resolve(surface).expect("resolve handler fixture");
        desugar(resolved).expect("desugar handler fixture")
    }

    const NO_RETURN_ARM: &str = "
effect Box
  take() : Int
  put(Int) : Unit

fn passes_through() =
  handle put(1) with
    take() resume k => k(0)
    put(v) resume w => w(())
";

    #[test]
    fn handler_without_return_arm_answers_at_the_body_type() {
        let program = core(NO_RETURN_ARM);
        let checked = check(&program).expect("check handler fixture");
        let decl = checked
            .defs
            .decls
            .iter()
            .find(|decl| decl.name == "passes_through")
            .expect("fixture declaration");
        assert_eq!(decl.ty.show(), "() -> Unit");
    }

    #[test]
    fn concrete_use_of_the_implicit_answer_fails_at_the_use_site() {
        let src = format!("{NO_RETURN_ARM}\nfn uses_it() : Int = passes_through()\n");
        let program = core(&src);
        let error = check(&program).expect_err("Unit answer used at Int must be a type error");
        assert_eq!(error.code(), Some("E1022"), "{error}");
    }
}
