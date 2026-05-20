use std::fs;
use std::path::PathBuf;
use std::process::Command;

use eggbau::{EggbauConfig, OutputMode};

const AXIOMS: &str = r#"
delimiter $ ( ) $;
sort R;
provable sort wff;
term eq (x y: R): wff;
term zero: R;
term one: R;
term add (x y: R): R;
term mul (x y: R): R;
term neg (x: R): R;
term sub (x y: R): R;

--| @relation R eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: R): $ eq x x $;
axiom eq_trans (x y z: R): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: R): $ eq x y $ > $ eq y x $;

--| @congr
axiom add_congr (a b c d: R):
  $ eq a b $ > $ eq c d $ > $ eq (add a c) (add b d) $;
--| @congr
axiom mul_congr (a b c d: R):
  $ eq a b $ > $ eq c d $ > $ eq (mul a c) (mul b d) $;
--| @congr
axiom neg_congr (a b: R): $ eq a b $ > $ eq (neg a) (neg b) $;
--| @congr
axiom sub_congr (a b c d: R):
  $ eq a b $ > $ eq c d $ > $ eq (sub a c) (sub b d) $;

--| @saturation ltr
axiom add_zero (x: R): $ eq (add x zero) x $;
--| @saturation ltr
axiom zero_add (x: R): $ eq (add zero x) x $;
--| @saturation ltr
axiom add_comm (x y: R): $ eq (add x y) (add y x) $;
--| @saturation ltr
axiom add_assoc (x y z: R):
  $ eq (add (add x y) z) (add x (add y z)) $;
--| @saturation ltr
axiom add_neg (x: R): $ eq (add x (neg x)) zero $;
--| @saturation ltr
axiom neg_neg (x: R): $ eq (neg (neg x)) x $;
--| @saturation ltr
axiom neg_zero: $ eq (neg zero) zero $;

--| @saturation ltr
axiom mul_one (x: R): $ eq (mul x one) x $;
--| @saturation ltr
axiom one_mul (x: R): $ eq (mul one x) x $;
--| @saturation ltr
axiom mul_zero (x: R): $ eq (mul x zero) zero $;
--| @saturation ltr
axiom zero_mul (x: R): $ eq (mul zero x) zero $;
--| @saturation ltr
axiom mul_comm (x y: R): $ eq (mul x y) (mul y x) $;
--| @saturation ltr
axiom mul_assoc (x y z: R):
  $ eq (mul (mul x y) z) (mul x (mul y z)) $;

--| @saturation both
axiom factor_l (x y z: R):
  $ eq (add (mul x y) (mul x z)) (mul x (add y z)) $;
--| @saturation both
axiom factor_r (x y z: R):
  $ eq (add (mul x z) (mul y z)) (mul (add x y) z) $;

--| @saturation ltr
axiom neg_mul_l (x y: R): $ eq (mul (neg x) y) (neg (mul x y)) $;
--| @saturation ltr
axiom neg_mul_r (x y: R): $ eq (mul x (neg y)) (neg (mul x y)) $;

--| @saturation ltr
axiom sub_def (x y: R): $ eq (sub x y) (add x (neg y)) $;
"#;

fn prove_auf(theorem_decl: &str) -> String {
    let input = format!("{AXIOMS}{theorem_decl}");
    eggbau::prove_theorem(
        &input,
        EggbauConfig {
            theorem: Some("target".to_owned()),
            output_mode: OutputMode::Fragment,
            allow_synthetic_discovery: false,
        },
    )
    .unwrap()
    .auf
}

fn prove_implicit_auf(name: &str, theorem_decl: &str) -> String {
    let dir = temp_test_dir(&format!("{name}_emit"));
    fs::create_dir_all(&dir).unwrap();
    let mm0_path = dir.join("input.mm0");
    fs::write(&mm0_path, format!("{AXIOMS}{theorem_decl}")).unwrap();

    eggbau::cli::run([
        "eggbau".to_owned(),
        "emit-auf".to_owned(),
        mm0_path.display().to_string(),
        "--theorem".to_owned(),
        "target".to_owned(),
        "--format".to_owned(),
        "implicit".to_owned(),
    ])
    .unwrap()
}

fn verify(name: &str, theorem_decl: &str, auf: &str) {
    let mm0 = format!("{AXIOMS}{theorem_decl}");
    verify_with_external_tools(name, &mm0, auf);
}

#[test]
fn proves_sub_self_is_zero() {
    let decl = "\ntheorem target (x: R): $ eq (sub x x) zero $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by sub_def"));
    assert!(auf.contains("by add_neg"));
    verify("stage8_ring_sub_self", decl, &auf);
}

#[test]
fn proves_sub_zero() {
    let decl = "\ntheorem target (x: R): $ eq (sub x zero) x $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by sub_def"));
    assert!(auf.contains("by neg_zero"));
    assert!(auf.contains("by add_zero"));
    verify("stage8_ring_sub_zero", decl, &auf);
}

#[test]
fn proves_zero_sub_is_neg() {
    let decl = "\ntheorem target (x: R): $ eq (sub zero x) (neg x) $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by sub_def"));
    assert!(auf.contains("by zero_add"));
    verify("stage8_ring_zero_sub", decl, &auf);
}

#[test]
fn proves_mul_neg_one_is_neg() {
    // (-1) * x = -x  via neg_mul_{l,r} + one_mul.
    // eggbau may route through `neg_mul_r` after mul_comm, so accept either.
    let decl = "\ntheorem target (x: R): $ eq (mul (neg one) x) (neg x) $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by neg_mul_l") || auf.contains("by neg_mul_r"));
    assert!(auf.contains("by one_mul") || auf.contains("by mul_one"));
    verify("stage8_ring_mul_neg_one", decl, &auf);
}

#[test]
fn proves_neg_mul_neg_is_mul() {
    // (-x) * (-y) = x * y  via neg_mul_l + neg_mul_r + neg_neg
    let decl = "\ntheorem target (x y: R): $ eq (mul (neg x) (neg y)) (mul x y) $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by neg_mul_l") || auf.contains("by neg_mul_r"));
    assert!(auf.contains("by neg_neg"));
    verify("stage8_ring_neg_mul_neg", decl, &auf);
}

#[test]
fn proves_add_sub_cancel() {
    let decl = "\ntheorem target (x y: R): $ eq (add x (sub y x)) y $;\n";
    let auf = prove_auf(decl);
    assert!(auf.contains("by sub_def"));
    verify("stage8_ring_add_sub_cancel", decl, &auf);
}

#[test]
fn proves_distrib_over_sub() {
    // x * (y - z) = x*y - x*z
    let decl = concat!(
        "\ntheorem target (x y z: R):\n",
        "  $ eq (mul x (sub y z)) (sub (mul x y) (mul x z)) $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by sub_def"));
    assert!(auf.contains("by factor_l") || auf.contains("by neg_mul_r"));
    verify("stage8_ring_distrib_sub", decl, &auf);
}

#[test]
fn proves_difference_of_squares() {
    // (a + b)(a - b) = a*a - b*b
    let decl = concat!(
        "\ntheorem target (a b: R):\n",
        "  $ eq (mul (add a b) (sub a b))\n",
        "       (sub (mul a a) (mul b b)) $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by sub_def"));
    assert!(auf.contains("by factor_l") || auf.contains("by factor_r"));
    verify("stage8_ring_difference_of_squares", decl, &auf);
}

#[test]
fn verifies_implicit_difference_of_squares() {
    let decl = concat!(
        "\ntheorem target (a b: R):\n",
        "  $ eq (mul (add a b) (sub a b))\n",
        "       (sub (mul a a) (mul b b)) $;\n",
    );
    let auf = prove_implicit_auf("stage8_ring_implicit_difference", decl);
    assert!(auf.contains("by sub_def"));
    assert!(auf.contains("by factor_l") || auf.contains("by factor_r"));
    assert!(!auf.contains(":="));
    verify("stage8_ring_implicit_difference", decl, &auf);
}

#[test]
fn proves_factor_two() {
    // x + x = (1 + 1) * x  via one_mul + factor_r
    let decl = concat!(
        "\ntheorem target (x: R):\n",
        "  $ eq (add x x) (mul (add one one) x) $;\n",
    );
    let auf = prove_auf(decl);
    assert!(auf.contains("by one_mul") || auf.contains("by factor_r"));
    verify("stage8_ring_factor_two", decl, &auf);
}

#[test]
fn fixture_file_axioms_match_embedded_axioms() {
    let fixture = include_str!("fixtures/stage8_ring.mm0");
    for axiom_name in [
        "add_neg",
        "neg_neg",
        "sub_def",
        "mul_zero",
        "factor_l",
        "factor_r",
        "neg_mul_l",
        "neg_mul_r",
    ] {
        assert!(
            fixture.contains(axiom_name) && AXIOMS.contains(axiom_name),
            "expected fixture and embedded axioms to both mention {axiom_name}"
        );
    }
}

fn verify_with_external_tools(name: &str, mm0: &str, auf: &str) {
    if !tool_available("abc") || !tool_available("mm0-zig") {
        eprintln!("skipping {name}: abc or mm0-zig is not on PATH");
        return;
    }

    let dir = temp_test_dir(name);
    fs::create_dir_all(&dir).unwrap();
    let mm0_path = dir.join("input.mm0");
    let auf_path = dir.join("generated.auf");
    let mmb_path = dir.join("generated.mmb");
    fs::write(&mm0_path, mm0).unwrap();
    fs::write(&auf_path, auf).unwrap();

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

    let mm0_zig = Command::new("mm0-zig")
        .arg(&mmb_path)
        .stdin(fs::File::open(&mm0_path).unwrap())
        .output()
        .unwrap();
    assert!(
        mm0_zig.status.success(),
        "mm0-zig failed\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&mm0_zig.stdout),
        String::from_utf8_lossy(&mm0_zig.stderr)
    );
}

fn tool_available(name: &str) -> bool {
    Command::new(name)
        .arg("--help")
        .output()
        .map(|_| true)
        .unwrap_or(false)
}

fn temp_test_dir(name: &str) -> PathBuf {
    let mut path = std::env::temp_dir();
    path.push(format!(
        "eggbau_{}_{}_{}",
        name,
        std::process::id(),
        std::thread::current().name().unwrap_or("test")
    ));
    path
}
