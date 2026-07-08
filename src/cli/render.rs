//! Shared human-output helpers: the `exec steps` ruler table and its previews.

// Rendering caps for the step ruler table: previews longer than this truncate
// with an ellipsis so one long read cannot wreck the table.
const STEP_PREVIEW_MAX: usize = 60;
const STEP_PREVIEW_ELLIPSIS: &str = "...";

fn step_preview(preview: &str) -> String {
    if preview.chars().count() <= STEP_PREVIEW_MAX {
        return preview.to_string();
    }
    let cut: String = preview.chars().take(STEP_PREVIEW_MAX).collect();
    format!("{cut}{STEP_PREVIEW_ELLIPSIS}")
}

// The text rendering of `prism exec steps`: one line per observation, step
// right-aligned to the total's width, preview quoted so control characters
// cannot break the table.
pub fn print_step_ruler(ruler: &crate::StepRuler) {
    let w = ruler.total_steps.to_string().len();
    let opw = ruler.rows.iter().map(|r| r.op.len()).max().unwrap_or(0);
    for r in &ruler.rows {
        if r.preview.is_empty() {
            println!("step {:>w$}  {}", r.step, r.op);
        } else {
            println!(
                "step {:>w$}  {:<opw$}  {:?}",
                r.step,
                r.op,
                step_preview(&r.preview)
            );
        }
    }
    println!(
        "total {} steps, {} observations",
        ruler.total_steps,
        ruler.rows.len()
    );
}

// The suspend cut report's timeline clause: where the pause fell relative to
// the observations the prefix performed.
pub fn cut_position(cut: &crate::SuspendCut) -> String {
    cut.last.as_ref().map_or_else(
        || "no observations before the cut".to_string(),
        |last| {
            format!(
                "{} observation(s) before the cut, last at step {} ({})",
                cut.observations, last.step, last.op
            )
        },
    )
}
