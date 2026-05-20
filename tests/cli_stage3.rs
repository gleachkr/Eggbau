use std::path::PathBuf;
use std::process::Command;

const FIXTURE: &str = "tests/fixtures/cli_multi.mm0";

#[test]
fn two_public_theorem_targets_are_proved_in_one_command() {
    let output = eggbau::cli::run([
        "eggbau",
        "prove",
        FIXTURE,
        "--theorem",
        "first",
        "--theorem",
        "second",
    ])
    .unwrap();

    assert!(output.contains("first\n-----\n"));
    assert!(output.contains("second\n------\n"));
    assert!(output.matches("by f_id").count() >= 2);
}

#[test]
fn public_theorem_output_uses_mm0_declaration_order() {
    let output = eggbau::cli::run([
        "eggbau",
        "prove",
        FIXTURE,
        "--theorem",
        "second",
        "--theorem",
        "first",
    ])
    .unwrap();

    let first_pos = output.find("first\n-----\n").unwrap();
    let second_pos = output.find("second\n------\n").unwrap();
    assert!(
        first_pos < second_pos,
        "output was not in declaration order"
    );
}

#[test]
fn out_of_order_command_line_targets_are_accepted() {
    let output =
        eggbau::cli::run(["eggbau", "prove", FIXTURE, "-t", "second", "-t", "first"]).unwrap();

    assert!(output.contains("first\n-----\n"));
    assert!(output.contains("second\n------\n"));
}

#[test]
fn later_theorem_by_itself_warns_about_stream_order() {
    let output = Command::new(env!("CARGO_BIN_EXE_eggbau"))
        .args(["prove", FIXTURE, "--theorem", "third"])
        .output()
        .unwrap();

    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("third\n-----\n"));
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("warning: emitted `third`"));
    assert!(stderr.contains("earlier public obligations"));
    assert!(stderr.contains("may not compile as a standalone stream"));
}

#[test]
fn prove_writes_to_stdout_when_out_is_omitted() {
    let output = Command::new(env!("CARGO_BIN_EXE_eggbau"))
        .args(["prove", FIXTURE, "--theorem", "first"])
        .output()
        .unwrap();

    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("first\n-----\n"));
}

#[test]
fn prove_writes_to_file_when_out_is_supplied() {
    let out = temp_path("multi_out.auf");
    let output = Command::new(env!("CARGO_BIN_EXE_eggbau"))
        .args([
            "prove",
            FIXTURE,
            "--theorem",
            "first",
            "--out",
            out.to_str().unwrap(),
        ])
        .output()
        .unwrap();

    assert!(output.status.success());
    assert!(output.stdout.is_empty());
    assert!(output.stderr.is_empty());
    let text = std::fs::read_to_string(out).unwrap();
    assert!(text.contains("first\n-----\n"));
}

fn temp_path(name: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/cli_stage3");
    std::fs::create_dir_all(&dir).unwrap();
    dir.join(format!("{}_{}", std::process::id(), name))
}
