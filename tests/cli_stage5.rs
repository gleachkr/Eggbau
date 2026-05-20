use std::path::PathBuf;

const MULTI_FIXTURE: &str = "tests/fixtures/cli_multi.mm0";

#[test]
fn list_prints_public_theorems_in_declaration_order() {
    let output = eggbau::cli::run(["eggbau", "list", MULTI_FIXTURE]).unwrap();

    assert_eq!(output, "theorem first\ntheorem second\ntheorem third\n");
}

#[test]
fn list_omits_axioms_and_unsupported_public_theorems() {
    let path = write_temp_mm0(
        "unsupported",
        r#"
sort s;
provable sort wff;
term p (x: s): wff;
axiom helper: $ p x $;
theorem supported (x: s): $ p x $;
theorem unsupported {x: s}: $ p x $;
"#,
    );

    let output = eggbau::cli::run([
        "eggbau".to_owned(),
        "list".to_owned(),
        path.display().to_string(),
    ])
    .unwrap();

    assert_eq!(output, "theorem supported\n");
}

#[test]
fn list_output_can_be_used_as_a_targets_file() {
    let targets = eggbau::cli::run(["eggbau", "list", MULTI_FIXTURE]).unwrap();
    let targets_path = write_temp_file("listed_targets", &targets);

    let output = eggbau::cli::run([
        "eggbau".to_owned(),
        "prove".to_owned(),
        MULTI_FIXTURE.to_owned(),
        "--targets".to_owned(),
        targets_path.display().to_string(),
    ])
    .unwrap();

    assert!(output.contains("first\n-----\n"));
    assert!(output.contains("second\n------\n"));
    assert!(output.contains("third\n-----\n"));
}

fn write_temp_mm0(name: &str, contents: &str) -> PathBuf {
    write_temp_file(name, contents)
}

fn write_temp_file(name: &str, contents: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/cli_stage5");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{name}_{}.txt", std::process::id()));
    std::fs::write(&path, contents).unwrap();
    path
}
