use std::path::PathBuf;
use std::process::Command;

const FIXTURE: &str = "tests/fixtures/cli_multi.mm0";
const ABC_FIXTURE: &str = "tests/fixtures/cli_local.mm0";

#[test]
fn one_local_lemma_target_is_emitted_as_lemma_block() {
    let output = eggbau::cli::run([
        "eggbau",
        "prove",
        FIXTURE,
        "--lemma",
        "local_id (x: s): $ eq (f x) x $",
    ])
    .unwrap();

    assert!(output.starts_with("lemma local_id (x: s): $ eq (f x) x $\n"));
    assert!(output.contains("by f_id"));
    assert!(!output.contains("first\n-----\n"));
}

#[test]
fn local_lemma_is_emitted_before_later_public_theorem() {
    let output = eggbau::cli::run([
        "eggbau",
        "prove",
        FIXTURE,
        "--theorem",
        "third",
        "--lemma",
        "local_id (x: s): $ eq (f x) x $",
    ])
    .unwrap();

    let lemma_pos = output.find("lemma local_id").unwrap();
    let theorem_pos = output.find("third\n-----\n").unwrap();
    assert!(lemma_pos < theorem_pos);
}

#[test]
fn duplicate_local_lemma_name_is_rejected() {
    let err = eggbau::cli::run([
        "eggbau",
        "prove",
        FIXTURE,
        "--lemma",
        "local_id (x: s): $ eq (f x) x $",
        "--lemma",
        "local_id (x: s): $ eq (f x) x $",
    ])
    .unwrap_err();

    assert!(err.to_string().contains("duplicate proof target: local_id"));
}

#[test]
fn local_lemma_colliding_with_public_assertion_is_rejected() {
    let err = eggbau::cli::run([
        "eggbau",
        "prove",
        FIXTURE,
        "--lemma",
        "first (x: s): $ eq (f x) x $",
    ])
    .unwrap_err();

    assert!(
        err.to_string()
            .contains("local lemma target collides with public assertion: first")
    );
}

#[test]
fn unsupported_local_lemma_syntax_is_rejected() {
    let err = eggbau::cli::run([
        "eggbau",
        "prove",
        FIXTURE,
        "--lemma",
        "bad {x: s}: $ eq x x $",
    ])
    .unwrap_err();

    assert!(err.to_string().contains("unsupported syntax"));
}

#[test]
fn generated_local_lemma_block_compiles_with_abc_when_available() {
    if !tool_available("abc") {
        eprintln!("skipping local lemma abc check: abc is not on PATH");
        return;
    }

    let mm0 = std::fs::read_to_string(ABC_FIXTURE).unwrap();
    let auf = eggbau::cli::run([
        "eggbau",
        "prove",
        ABC_FIXTURE,
        "--lemma",
        "local_id (x: s): $ eq (f x) x $",
        "--theorem",
        "target",
    ])
    .unwrap();

    let dir = temp_dir("cli_local_lemmas_local_lemma");
    std::fs::create_dir_all(&dir).unwrap();
    let mm0_path = dir.join("input.mm0");
    let auf_path = dir.join("generated.auf");
    let mmb_path = dir.join("generated.mmb");
    std::fs::write(&mm0_path, mm0).unwrap();
    std::fs::write(&auf_path, auf).unwrap();

    let abc = Command::new("abc")
        .arg("compile")
        .arg(&mm0_path)
        .arg(&auf_path)
        .arg(&mmb_path)
        .output()
        .unwrap();

    assert!(
        abc.status.success(),
        "abc failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&abc.stdout),
        String::from_utf8_lossy(&abc.stderr)
    );
}

fn tool_available(name: &str) -> bool {
    Command::new(name)
        .arg("--help")
        .output()
        .map(|_| true)
        .unwrap_or(false)
}

fn temp_dir(name: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!("eggbau_{}_{}", name, std::process::id()));
    path
}
