use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Stdio};

use eggbau::cli::{TargetSpec, parse_target_lines};

const FIXTURE: &str = "tests/fixtures/stage4_conversion.mm0";
const MULTI_FIXTURE: &str = "tests/fixtures/cli_multi.mm0";

#[test]
fn repeated_theorem_targets_are_parsed_for_multi_prove() {
    let output = eggbau::cli::run([
        "eggbau",
        "prove",
        MULTI_FIXTURE,
        "--theorem",
        "first",
        "--theorem",
        "second",
    ])
    .unwrap();

    assert!(output.contains("first\n-----\n"));
    assert!(output.contains("second\n------\n"));
}

#[test]
fn duplicate_theorem_targets_are_rejected() {
    let err = eggbau::cli::run([
        "eggbau",
        "prove",
        FIXTURE,
        "--theorem",
        "target",
        "--theorem",
        "target",
    ])
    .unwrap_err();

    assert!(err.to_string().contains("duplicate proof target: target"));
}

#[test]
fn lemma_targets_are_parsed_and_named() {
    let output = eggbau::cli::run([
        "eggbau",
        "prove",
        FIXTURE,
        "--lemma",
        "local_target (x: s): $ eq (f x) x $",
    ])
    .unwrap();

    assert!(output.contains("lemma local_target (x: s): $ eq (f x) x $\n"));
    assert!(output.contains("by f_id"));
}

#[test]
fn target_file_with_blank_lines_and_comments_can_drive_single_prove() {
    let path = write_temp_file(
        "targets_file",
        "\n-- this is a target-file comment\n\ntheorem target\n",
    );

    let output = eggbau::cli::run([
        "eggbau".to_owned(),
        "prove".to_owned(),
        FIXTURE.to_owned(),
        "--targets".to_owned(),
        path.display().to_string(),
    ])
    .unwrap();

    assert!(output.contains("target\n------\n"));
    assert!(output.contains("by f_id"));
}

#[test]
fn stdin_target_file_can_drive_single_prove() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_eggbau"))
        .args(["prove", FIXTURE, "--targets", "-"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();

    child
        .stdin
        .as_mut()
        .unwrap()
        .write_all(b"-- from stdin\n\ntheorem target\n")
        .unwrap();

    let output = child.wait_with_output().unwrap();

    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("target\n------\n"));
    assert!(stdout.contains("by f_id"));
}

#[test]
fn target_line_parser_accepts_theorems_lemmas_comments_and_blanks() {
    let targets = parse_target_lines(
        "targets.txt",
        "\n-- comment\ntheorem target\nlemma local (x: s): $ eq x x $\n",
    )
    .unwrap();

    assert_eq!(targets.len(), 2);
    assert_eq!(targets[0], TargetSpec::theorem("target"));
    assert_eq!(targets[1].name(), "local");
}

#[test]
fn malformed_target_lines_are_rejected_with_line_numbers() {
    let err = parse_target_lines("targets.txt", "theorem target extra\n").unwrap_err();

    assert!(err.to_string().contains("targets.txt:1"));
    assert!(err.to_string().contains("invalid theorem target name"));
}

#[test]
fn duplicate_target_file_entries_are_rejected() {
    let err = parse_target_lines("targets.txt", "theorem target\ntheorem target\n").unwrap_err();

    assert!(err.to_string().contains("duplicate proof target: target"));
}

fn write_temp_file(name: &str, contents: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/cli_stage2");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{name}_{}.txt", std::process::id()));
    std::fs::write(&path, contents).unwrap();
    path
}
