use std::path::PathBuf;
use std::process::Command;

const FIXTURE: &str = "tests/fixtures/cli_multi.mm0";

#[test]
fn base_splice_replaces_existing_public_theorem_block() {
    let base = temp_path("replace_base.auf");
    std::fs::write(
        &base,
        "-- keep this comment\n\
         first\n\
         -----\n\
         old_first: $ old first $\n",
    )
    .unwrap();

    let output = eggbau::cli::run([
        "eggbau",
        "prove",
        FIXTURE,
        "--base",
        base.to_str().unwrap(),
        "--theorem",
        "first",
    ])
    .unwrap();

    assert!(output.contains("-- keep this comment"));
    assert!(output.contains("first\n-----\n"));
    assert!(output.contains("by f_id"));
    assert!(!output.contains("old_first"));
}

#[test]
fn base_splice_inserts_new_public_theorem_in_declaration_order() {
    let base = temp_path("insert_base.auf");
    std::fs::write(
        &base,
        "first\n\
         -----\n\
         old_first: $ old first $\n\n\
         third\n\
         -----\n\
         old_third: $ old third $\n",
    )
    .unwrap();

    let output = eggbau::cli::run([
        "eggbau",
        "prove",
        FIXTURE,
        "--base",
        base.to_str().unwrap(),
        "--theorem",
        "second",
    ])
    .unwrap();

    let first_pos = output.find("first\n-----\n").unwrap();
    let second_pos = output.find("second\n------\n").unwrap();
    let third_pos = output.find("third\n-----\n").unwrap();
    assert!(first_pos < second_pos);
    assert!(second_pos < third_pos);
    assert!(output.contains("old_first"));
    assert!(output.contains("old_third"));
}

#[test]
fn base_splice_preserves_unrelated_blocks_and_comments() {
    let base = temp_path("preserve_base.auf");
    std::fs::write(
        &base,
        "-- prologue\n\
         lemma local_note (x: s): $ eq x x $\n\
         ----------------------------------\n\
         local_line: $ eq x x $ by eq_refl [x := $ x $]\n\n\
         -- before second\n\
         second\n\
         ------\n\
         old_second: $ old second $\n",
    )
    .unwrap();

    let output = eggbau::cli::run([
        "eggbau",
        "prove",
        FIXTURE,
        "--base",
        base.to_str().unwrap(),
        "--theorem",
        "first",
    ])
    .unwrap();

    assert!(output.contains("-- prologue"));
    assert!(output.contains("lemma local_note"));
    assert!(output.contains("-- before second"));
    assert!(output.contains("old_second"));
    assert!(output.contains("first\n-----\n"));
    let first_pos = output.find("first\n-----\n").unwrap();
    let comment_pos = output.find("-- before second").unwrap();
    let second_pos = output.find("second\n------\n").unwrap();
    assert!(first_pos < comment_pos);
    assert!(comment_pos < second_pos);
}

#[test]
fn base_splice_warns_for_remaining_missing_earlier_obligations() {
    let base = temp_path("warning_base.auf");
    std::fs::write(
        &base,
        "first\n\
         -----\n\
         old_first: $ old first $\n",
    )
    .unwrap();

    let output = Command::new(env!("CARGO_BIN_EXE_eggbau"))
        .args([
            "prove",
            FIXTURE,
            "--base",
            base.to_str().unwrap(),
            "--theorem",
            "third",
        ])
        .output()
        .unwrap();

    assert!(output.status.success());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("warning: emitted `third`"));
    assert!(stderr.contains("second"));
    assert!(!stderr.contains("first, second"));
}

#[test]
fn base_splice_rejects_duplicate_public_theorem_blocks() {
    let base = temp_path("duplicate_base.auf");
    std::fs::write(
        &base,
        "first\n\
         -----\n\
         old_first: $ old first $\n\n\
         first\n\
         -----\n\
         other_first: $ old first $\n",
    )
    .unwrap();

    let err = eggbau::cli::run([
        "eggbau",
        "prove",
        FIXTURE,
        "--base",
        base.to_str().unwrap(),
        "--theorem",
        "first",
    ])
    .unwrap_err();

    assert!(err.to_string().contains("duplicate public theorem block"));
    assert!(err.to_string().contains("first"));
}

#[test]
fn base_splice_rejects_public_theorem_order_contradictions() {
    let base = temp_path("contradiction_base.auf");
    std::fs::write(
        &base,
        "second\n\
         ------\n\
         old_second: $ old second $\n\n\
         first\n\
         -----\n\
         old_first: $ old first $\n",
    )
    .unwrap();

    let err = eggbau::cli::run([
        "eggbau",
        "prove",
        FIXTURE,
        "--base",
        base.to_str().unwrap(),
        "--theorem",
        "third",
    ])
    .unwrap_err();

    assert!(err.to_string().contains("contradict MM0 declaration order"));
    assert!(err.to_string().contains("second"));
    assert!(err.to_string().contains("first"));
}

#[test]
fn base_splice_reports_parse_errors_for_malformed_public_blocks() {
    let base = temp_path("malformed_base.auf");
    std::fs::write(
        &base,
        "first\n\
         not a dashed underline\n",
    )
    .unwrap();

    let err = eggbau::cli::run([
        "eggbau",
        "prove",
        FIXTURE,
        "--base",
        base.to_str().unwrap(),
        "--theorem",
        "first",
    ])
    .unwrap_err();

    assert!(err.to_string().contains("base .auf parse error"));
    assert!(err.to_string().contains("missing its dashed underline"));
}

fn temp_path(name: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/cli_stage9");
    std::fs::create_dir_all(&dir).unwrap();
    dir.join(format!("{}_{}", std::process::id(), name))
}
