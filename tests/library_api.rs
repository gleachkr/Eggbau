use eggbau::{EggbauOptions, EggbauSession, GoalSpec, OutputMode};

const E2E: &str = include_str!("fixtures/cli_e2e.mm0");

#[test]
fn downstream_crate_can_import_session_and_prove_theorem() {
    let mut session = EggbauSession::from_mm0(E2E).unwrap();

    let result = session.prove_theorem("target").unwrap();

    assert_eq!(result.theorem, "target");
    assert!(result.auf_block.contains("target\n------"));
    assert!(result.egglog_program.as_deref().unwrap().contains("f_id"));
    assert!(!result.certificate.steps.is_empty());
}

#[test]
fn callers_can_prove_to_certificate_and_render_later() {
    let mut session = EggbauSession::from_mm0(E2E).unwrap();

    let cert = session.prove_to_cert("target").unwrap();
    let rendered = session.render_auf(&cert).unwrap();

    assert!(rendered.contains("target\n------"));
    assert!(rendered.contains("by f_id"));
}

#[test]
fn downstream_generated_goal_does_not_need_public_theorem() {
    let mut session = EggbauSession::from_mm0(E2E).unwrap();
    let goal = GoalSpec::generated_theorem("downstream_target (x: s): $ eq (f x) x $");

    let result = session.prove_goal(goal).unwrap();

    assert_eq!(result.theorem, "downstream_target");
    assert!(result.auf_block.contains("downstream_target\n"));
    assert!(result.auf_block.contains("by f_id"));
}

#[test]
fn library_options_can_disable_egglog_program_capture() {
    let options = EggbauOptions {
        output_mode: OutputMode::Fragment,
        include_egglog_program: false,
        ..EggbauOptions::default()
    };
    let mut session = EggbauSession::from_mm0_with_options(E2E, options).unwrap();

    let result = session.prove_theorem("target").unwrap();

    assert!(result.egglog_program.is_none());
    assert!(!result.certificate.steps.is_empty());
}

#[test]
fn cli_and_session_render_the_same_single_theorem_block() {
    let cli_output = eggbau::cli::run([
        "eggbau",
        "prove",
        "tests/fixtures/cli_e2e.mm0",
        "--theorem",
        "target",
    ])
    .unwrap();
    let mut session = EggbauSession::from_mm0(E2E).unwrap();
    let result = session.prove_theorem("target").unwrap();

    assert_eq!(cli_output, result.auf_block);
}
