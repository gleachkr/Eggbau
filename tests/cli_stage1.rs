use std::process::Command;

#[test]
fn help_output_shows_new_public_command_tree() {
    let output = Command::new(env!("CARGO_BIN_EXE_eggbau"))
        .arg("--help")
        .output()
        .unwrap();

    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("eggbau prove INPUT.mm0 [OPTIONS]"));
    assert!(stdout.contains("eggbau list INPUT.mm0"));
    assert!(stdout.contains("eggbau script emit INPUT.mm0 [OPTIONS]"));
    assert!(stdout.contains("eggbau script prove INPUT.mm0 [OPTIONS]"));
    assert!(stdout.contains("eggbau script check INPUT.mm0 [OPTIONS]"));
    assert!(stdout.contains("--format FORMAT"));
    assert!(!stdout.contains("dump-env"));
    assert!(!stdout.contains("emit-egglog"));
    assert!(!stdout.contains("prove-egglog"));
    assert!(!stdout.contains("emit-auf"));
}

#[test]
fn unknown_command_is_a_usage_error() {
    let output = Command::new(env!("CARGO_BIN_EXE_eggbau"))
        .arg("nonesuch")
        .output()
        .unwrap();

    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("unsupported command: nonesuch"));
}

#[test]
fn old_top_level_command_names_are_rejected() {
    for command in ["dump-env", "emit-egglog", "prove-egglog", "emit-auf"] {
        let output = Command::new(env!("CARGO_BIN_EXE_eggbau"))
            .arg(command)
            .output()
            .unwrap();

        assert!(!output.status.success(), "{command} unexpectedly succeeded");
        let stderr = String::from_utf8(output.stderr).unwrap();
        assert!(stderr.contains(&format!("unsupported command: {command}")));
    }
}

#[test]
fn version_output_is_unchanged_by_cli_tree_update() {
    let output = Command::new(env!("CARGO_BIN_EXE_eggbau"))
        .arg("--version")
        .output()
        .unwrap();

    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("eggbau 0.1.0"));
    assert!(stdout.contains("egglog 2.0.0"));
}

#[test]
fn prove_accepts_explicit_and_implicit_format_options() {
    for format in ["explicit", "implicit"] {
        let output = eggbau::cli::run([
            "eggbau".to_owned(),
            "prove".to_owned(),
            "tests/fixtures/stage4_conversion.mm0".to_owned(),
            "--theorem".to_owned(),
            "target".to_owned(),
            "--format".to_owned(),
            format.to_owned(),
        ])
        .unwrap();

        assert!(output.contains("target\n------\n"));
        assert!(output.contains("by f_id"));
    }
}
