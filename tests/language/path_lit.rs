// A path literal is a spelling for a pair of functions, not a new kind of
// value. `#path a.b` names the same getter and setter a reader would write by
// hand and hands them to the ordinary lens constructor, so nothing downstream of
// the parser learns that the literal exists: no new node, no new type, no
// special case in the checker or in lowering. These tests pin that the expansion
// really is the ordinary call, because the moment it is not, the literal stops
// being sugar and becomes a construct with its own semantics to maintain.
//
// The rejection is the other half of the contract. A path literal focuses
// exactly one place, which is what makes the setter total; the forms that focus
// zero or many places are refused at the parser rather than accepted into a
// shape whose setter would have to invent a meaning for "no target".

use prism::parse::parse;
use prism::syntax::ast::{Expr, Ty};

const ONE_STEP: &str = "fn f() =\n  let a = #path hp\n  a\n";

const TWO_STEPS: &str = "fn f() =\n  let a = #path pos.x\n  a\n";

// Pull the single `let`'s bound value out of the only function in `src`.
fn bound_value(src: &str) -> Expr {
    let program = parse(src).expect("must parse").program;
    let Expr::Let(_, value, _) = &program.fns[0].body.node else {
        panic!("expected the body to start with a binding");
    };
    value.node.clone()
}

#[test]
fn the_literal_expands_to_an_ordinary_lens_call() {
    let Expr::Call(head, args) = bound_value(ONE_STEP) else {
        panic!("the literal must expand to a call");
    };
    assert!(
        matches!(&head.node, Expr::Var(name) if name == "lens"),
        "the callee must be the lens constructor, got: {head:?}"
    );
    let [getter, setter] = args.as_slice() else {
        panic!(
            "expected a getter and a setter, got {} arguments",
            args.len()
        );
    };
    let Expr::Lam(get_params, _) = &getter.node else {
        panic!("the getter must be a function");
    };
    let Expr::Lam(set_params, _) = &setter.node else {
        panic!("the setter must be a function");
    };
    assert_eq!(get_params.len(), 1, "the getter takes the whole");
    assert_eq!(
        set_params.len(),
        2,
        "the setter takes the whole and the part"
    );
}

// Each step is one field access on the result of the last, so a two-step
// literal reads through the nested record exactly as the written chain does.
#[test]
fn steps_nest_left_to_right() {
    let Expr::Call(_, args) = bound_value(TWO_STEPS) else {
        panic!("the literal must expand to a call");
    };
    let Expr::Lam(_, body) = &args[0].node else {
        panic!("the getter must be a function");
    };
    let Expr::FieldAccess(inner, outer_field) = &body.node else {
        panic!("the getter body must be a field access, got: {body:?}");
    };
    assert_eq!(outer_field, "x", "the last step is the outermost access");
    assert!(
        matches!(&inner.node, Expr::FieldAccess(_, f) if f == "pos"),
        "the first step must be the inner access, got: {inner:?}"
    );
}

// The binders the expansion introduces are deliberately unspellable, so no
// program can name them and no expansion can capture a user's binding of the
// same name. That is also what lets the formatter recognize its own expansion
// without threading a flag through the printer.
#[test]
fn the_expansion_binds_names_no_program_can_write() {
    let Expr::Call(_, args) = bound_value(ONE_STEP) else {
        panic!("the literal must expand to a call");
    };
    let Expr::Lam(params, _) = &args[1].node else {
        panic!("the setter must be a function");
    };
    for param in params {
        assert!(
            !param.name.chars().all(|c| c.is_alphanumeric() || c == '_'),
            "`{}` is a name a program could write",
            param.name
        );
    }
    assert!(
        parse(&ONE_STEP.replace("#path hp", &params[0].name)).is_err(),
        "the expansion's binder must not be a writable expression"
    );
}

// A path literal is not a pattern position: the steps are field names being
// projected, not names being bound, so nothing about the form should suggest
// otherwise to a reader who meets it first in a `match`.
#[test]
fn a_literal_is_an_expression_not_a_pattern() {
    let src = "fn f(o : Option(Int)) : Int =\n  match o of\n    #path hp => 1\n    _ => 0\n";
    assert!(
        parse(src).is_err(),
        "a path literal must not parse where a pattern is expected"
    );
}

// An anchored literal (`#path Type.a.b`) is the same expansion with the root
// type carried onto both `whole@` binders as an ordinary annotation. The
// anchor is what lets the literal sit inline where nothing else names the
// whole type; these tests pin that it is an annotation and nothing more.
#[test]
fn an_anchored_literal_annotates_both_whole_binders() {
    let src = "fn f() =\n  let a = #path Solver.metas.next\n  a\n";
    let Expr::Call(_, args) = bound_value(src) else {
        panic!("the literal must expand to a call");
    };
    let (Expr::Lam(gp, _), Expr::Lam(stp, _)) = (&args[0].node, &args[1].node) else {
        panic!("both halves must be functions");
    };
    for whole in [&gp[0], &stp[0]] {
        let Some(Ty::Con(name, tail)) = &whole.ty else {
            panic!("the whole binder must carry the anchor type");
        };
        assert_eq!(name, "Solver", "the anchor is the uppercase head");
        assert!(tail.is_empty(), "the anchor is a bare type name");
    }
    assert!(stp[1].ty.is_none(), "the part binder stays unannotated");
}

// A bare anchor names a whole but no focus, so there is nothing for the
// literal to denote and it is refused at the parser.
#[test]
fn an_anchor_without_a_field_is_refused() {
    let src = "fn f() =\n  let a = #path Solver\n  a\n";
    assert!(
        parse(src).is_err(),
        "an anchored literal needs at least one field"
    );
}
