use crate::syntax::ast::{PathStep, Phase};

pub(super) fn field_prefix<P: Phase>(short: &[PathStep<P>], long: &[PathStep<P>]) -> bool {
    short.len() <= long.len()
        && short
            .iter()
            .zip(long)
            .all(|(left, right)| match (left, right) {
                (PathStep::Field(x), PathStep::Field(y)) => x == y,
                _ => false,
            })
}

pub(super) fn show_path<P: Phase>(steps: &[PathStep<P>]) -> String {
    steps
        .iter()
        .map(|step| match step {
            PathStep::Field(field) => field.clone(),
            PathStep::Each => crate::kw::EACH.into(),
            PathStep::Case(ctor) => format!("{}{ctor}", crate::kw::QUESTION),
            PathStep::Index(_) => "[..]".into(),
            PathStep::Where(_) => crate::kw::WHERE.into(),
        })
        .collect::<Vec<_>>()
        .join(".")
}
