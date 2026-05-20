use std::fs;
use std::path::PathBuf;
use std::process::Command;

use eggbau::{EggbauConfig, OutputMode};

const CONGR_INPUT: &str = r#"
delimiter $ ( ) $;
sort s;
provable sort wff;
term f (x: s): s;
term h (x: s): s;
term eq (x y: s): wff;
--| @relation s eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: s): $ eq x x $;
axiom eq_trans (x y z: s): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: s): $ eq x y $ > $ eq y x $;
--| @congr
axiom h_congr (x y: s): $ eq x y $ > $ eq (h x) (h y) $;
--| @saturation ltr
axiom f_id (x: s): $ eq (f x) x $;
theorem target (x: s): $ eq (h (f x)) (h x) $;
"#;

const HORN_MOD_EQ_INPUT: &str = r#"
delimiter $ ( ) $;
sort s;
provable sort wff;
term eq (x y: s): wff;
term bi (x y: wff): wff;
term p (x: s): wff;
term q (x: s): wff;
--| @relation s eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: s): $ eq x x $;
axiom eq_trans (x y z: s): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: s): $ eq x y $ > $ eq y x $;
--| @relation wff bi bi_refl bi_trans bi_sym bi_mp
axiom bi_refl (x: wff): $ bi x x $;
axiom bi_trans (x y z: wff): $ bi x y $ > $ bi y z $ > $ bi x z $;
axiom bi_sym (x y: wff): $ bi x y $ > $ bi y x $;
axiom bi_mp (x y: wff): $ bi x y $ > $ x $ > $ y $;
--| @congr
axiom p_congr (x y: s): $ eq x y $ > $ bi (p x) (p y) $;
--| @congr
axiom q_congr (x y: s): $ eq x y $ > $ bi (q x) (q y) $;
--| @saturation horn
axiom p_from_q (x: s): $ q x $ > $ p x $;
theorem target (x y: s): $ eq x y $ > $ q y $ > $ p x $;
"#;

const GROUP_INVERSE_INPUT: &str = r#"
delimiter $ ( ) $;
sort g;
provable sort wff;
term inv (x: g): g;
term eq (x y: g): wff;
--| @relation g eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: g): $ eq x x $;
axiom eq_trans (x y z: g): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: g): $ eq x y $ > $ eq y x $;
--| @congr
axiom inv_congr (x y: g): $ eq x y $ > $ eq (inv x) (inv y) $;
--| @saturation ltr
axiom inv_inv (x: g): $ eq (inv (inv x)) x $;
theorem target (x: g): $ eq (inv (inv (inv (inv x)))) x $;
"#;

const PROPOSITIONAL_INPUT: &str = r#"
delimiter $ ( ) $;
provable sort wff;
term not (x: wff): wff;
term iff (x y: wff): wff;
--| @relation wff iff iff_refl iff_trans iff_sym iff_mp
axiom iff_refl (x: wff): $ iff x x $;
axiom iff_trans (x y z: wff): $ iff x y $ > $ iff y z $ > $ iff x z $;
axiom iff_sym (x y: wff): $ iff x y $ > $ iff y x $;
axiom iff_mp (x y: wff): $ iff x y $ > $ x $ > $ y $;
--| @congr
axiom not_congr (x y: wff): $ iff x y $ > $ iff (not x) (not y) $;
--| @saturation ltr
axiom double_neg (x: wff): $ iff (not (not x)) x $;
theorem target (p: wff): $ iff (not (not (not (not p)))) p $;
"#;

const LINARITH_NORMALIZATION_INPUT: &str = r#"
delimiter $ ( ) $;
sort int;
provable sort wff;
term add0 (x: int): int;
term eq (x y: int): wff;
--| @relation int eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: int): $ eq x x $;
axiom eq_trans (x y z: int): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: int): $ eq x y $ > $ eq y x $;
--| @congr
axiom add0_congr (x y: int): $ eq x y $ > $ eq (add0 x) (add0 y) $;
--| @saturation ltr
axiom add_zero (x: int): $ eq (add0 x) x $;
theorem target (x: int): $ eq (add0 (add0 x)) x $;
"#;

const BINARY_CONGR_LEFT_INPUT: &str = r#"
delimiter $ ( ) $;
sort s;
provable sort wff;
term f (x: s): s;
term pair (x y: s): s;
term eq (x y: s): wff;
--| @relation s eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: s): $ eq x x $;
axiom eq_trans (x y z: s): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: s): $ eq x y $ > $ eq y x $;
--| @congr
axiom pair_congr (x y z w: s):
  $ eq x y $ > $ eq z w $ > $ eq (pair x z) (pair y w) $;
--| @saturation ltr
axiom f_id (x: s): $ eq (f x) x $;
theorem target (x y: s): $ eq (pair (f x) y) (pair x y) $;
"#;

const BINARY_CONGR_RIGHT_INPUT: &str = r#"
delimiter $ ( ) $;
sort s;
provable sort wff;
term f (x: s): s;
term pair (x y: s): s;
term eq (x y: s): wff;
--| @relation s eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: s): $ eq x x $;
axiom eq_trans (x y z: s): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: s): $ eq x y $ > $ eq y x $;
--| @congr
axiom pair_congr (x y z w: s):
  $ eq x y $ > $ eq z w $ > $ eq (pair x z) (pair y w) $;
--| @saturation ltr
axiom f_id (x: s): $ eq (f x) x $;
theorem target (x y: s): $ eq (pair y (f x)) (pair y x) $;
"#;

const CROSS_SORT_FACT_CONGR_INPUT: &str = r#"
delimiter $ ( ) $;
sort int;
provable sort wff;
term add0 (x: int): int;
term eq (x y: int): wff;
term bi (x y: wff): wff;
term le (x y: int): wff;
--| @relation int eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: int): $ eq x x $;
axiom eq_trans (x y z: int): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: int): $ eq x y $ > $ eq y x $;
--| @relation wff bi bi_refl bi_trans bi_sym bi_mp
axiom bi_refl (x: wff): $ bi x x $;
axiom bi_trans (x y z: wff): $ bi x y $ > $ bi y z $ > $ bi x z $;
axiom bi_sym (x y: wff): $ bi x y $ > $ bi y x $;
axiom bi_mp (x y: wff): $ bi x y $ > $ x $ > $ y $;
--| @congr
axiom le_congr (x y z w: int):
  $ eq x y $ > $ eq z w $ > $ bi (le x z) (le y w) $;
--| @saturation ltr
axiom add_zero (x: int): $ eq (add0 x) x $;
theorem target (x y: int): $ le x y $ > $ le (add0 x) y $;
"#;

const CROSS_SORT_TERM_CONGR_INPUT: &str = r#"
delimiter $ ( ) $;
sort vec;
sort nat;
provable sort wff;
term normalize (x: vec): vec;
term len (x: vec): nat;
term veq (x y: vec): wff;
term neq (x y: nat): wff;
--| @relation vec veq veq_refl veq_trans veq_sym _
axiom veq_refl (x: vec): $ veq x x $;
axiom veq_trans (x y z: vec): $ veq x y $ > $ veq y z $ > $ veq x z $;
axiom veq_sym (x y: vec): $ veq x y $ > $ veq y x $;
--| @relation nat neq neq_refl neq_trans neq_sym _
axiom neq_refl (x: nat): $ neq x x $;
axiom neq_trans (x y z: nat): $ neq x y $ > $ neq y z $ > $ neq x z $;
axiom neq_sym (x y: nat): $ neq x y $ > $ neq y x $;
--| @congr
axiom len_congr (x y: vec): $ veq x y $ > $ neq (len x) (len y) $;
--| @saturation ltr
axiom normalize_id (x: vec): $ veq (normalize x) x $;
theorem target (x: vec): $ neq (len (normalize x)) (len x) $;
"#;

fn prove_auf(input: &str) -> String {
    eggbau::prove_theorem(
        input,
        EggbauConfig {
            theorem: Some("target".to_owned()),
            output_mode: OutputMode::Fragment,
            allow_synthetic_discovery: false,
        },
    )
    .unwrap()
    .auf
}

#[test]
fn cli_prove_implicit_format_omits_binder_assignments() {
    let dir = temp_test_dir("stage8_implicit_format");
    fs::create_dir_all(&dir).unwrap();
    let mm0_path = dir.join("input.mm0");
    fs::write(&mm0_path, CONGR_INPUT).unwrap();

    let auf = eggbau::cli::run([
        "eggbau".to_owned(),
        "prove".to_owned(),
        mm0_path.display().to_string(),
        "--theorem".to_owned(),
        "target".to_owned(),
        "--format".to_owned(),
        "implicit".to_owned(),
    ])
    .unwrap();

    assert!(auf.contains("by f_id ["));
    assert!(auf.contains("by h_congr [rule_2]"));
    assert!(!auf.contains(":="));
    verify_with_external_tools("stage8_implicit_format", CONGR_INPUT, &auf);
}

#[test]
fn renders_congruence_certificate_as_auf_fragment() {
    let auf = prove_auf(CONGR_INPUT);

    assert!(auf.starts_with("target\n------\n"));
    assert!(auf.contains("eq_refl_1: $ eq (h (f x)) (h (f x)) $"));
    assert!(auf.contains("rule_2: $ eq (f x) x $ by f_id"));
    assert!(auf.contains("eq_congr_3: $ eq (h (f x)) (h x) $"));
    assert!(auf.contains("by h_congr (x := $ f x $, y := $ x $) [rule_2]"));
}

#[test]
fn renders_horn_modulo_equality_with_transport_refs() {
    let auf = prove_auf(HORN_MOD_EQ_INPUT);

    assert!(auf.contains("eq_sym_3: $ eq y x $ by eq_sym"));
    assert!(auf.contains("fact_congr_4: $ bi (q y) (q x) $ by q_congr"));
    assert!(auf.contains("transport_5: $ q x $ by bi_mp"));
    assert!(auf.contains("horn_6: $ p x $ by p_from_q"));
    assert!(auf.contains("[fact_congr_4, #2]"));
}

#[test]
fn rejects_non_fragment_modes_with_stream_order_diagnostic() {
    let err = eggbau::prove_theorem(
        CONGR_INPUT,
        EggbauConfig {
            theorem: Some("target".to_owned()),
            output_mode: OutputMode::FullStream,
            allow_synthetic_discovery: false,
        },
    )
    .unwrap_err();

    assert!(err.to_string().contains("stream-order proof obligation"));
}

#[test]
fn generated_congruence_fragment_verifies_when_tools_are_available() {
    verify_with_external_tools("stage8_congr", CONGR_INPUT, &prove_auf(CONGR_INPUT));
}

#[test]
fn generated_horn_modulo_equality_fragment_verifies_when_tools_are_available() {
    verify_with_external_tools(
        "stage8_horn_mod_eq",
        HORN_MOD_EQ_INPUT,
        &prove_auf(HORN_MOD_EQ_INPUT),
    );
}

#[test]
fn verifies_group_inverse_algebra_fragment() {
    let auf = prove_auf(GROUP_INVERSE_INPUT);

    assert!(auf.contains("by inv_inv"));
    assert!(auf.contains("by inv_congr"));
    assert_eq!(auf, prove_auf(GROUP_INVERSE_INPUT));
    verify_with_external_tools("stage8_group_inverse", GROUP_INVERSE_INPUT, &auf);
}

#[test]
fn verifies_propositional_double_negation_fragment() {
    let auf = prove_auf(PROPOSITIONAL_INPUT);

    assert!(auf.contains("by double_neg"));
    assert!(auf.contains("by not_congr"));
    assert!(auf.contains("by iff_trans"));
    verify_with_external_tools("stage8_prop_double_neg", PROPOSITIONAL_INPUT, &auf);
}

#[test]
fn verifies_linarith_style_normalization_fragment() {
    let auf = prove_auf(LINARITH_NORMALIZATION_INPUT);

    assert!(auf.contains("by add_zero"));
    assert!(auf.contains("by add0_congr"));
    assert!(auf.contains("$ eq (add0 (add0 x)) x $"));
    verify_with_external_tools(
        "stage8_linarith_normalization",
        LINARITH_NORMALIZATION_INPUT,
        &auf,
    );
}

#[test]
fn verifies_binary_congruence_with_synthesized_reflexivity() {
    let auf = prove_auf(BINARY_CONGR_LEFT_INPUT);

    assert!(auf.contains("by pair_congr"));
    assert!(auf.contains("by eq_refl (x := $ y $)"));
    assert!(auf.contains("[rule_2, eq_congr_3__refl_1]"));
    verify_with_external_tools("stage8_binary_congr_left", BINARY_CONGR_LEFT_INPUT, &auf);
}

#[test]
fn verifies_binary_congruence_when_second_argument_changes() {
    let auf = prove_auf(BINARY_CONGR_RIGHT_INPUT);

    assert!(auf.contains("by pair_congr"));
    assert!(auf.contains("by eq_refl (x := $ y $)"));
    assert!(auf.contains("[eq_congr_3__refl_0, rule_2]"));
    verify_with_external_tools("stage8_binary_congr_right", BINARY_CONGR_RIGHT_INPUT, &auf);
}

#[test]
fn verifies_cross_sort_binary_fact_congruence() {
    let auf = prove_auf(CROSS_SORT_FACT_CONGR_INPUT);

    assert!(auf.contains("by le_congr"));
    assert!(auf.contains("by eq_refl (x := $ y $)"));
    assert!(auf.contains("by bi_mp"));
    verify_with_external_tools(
        "stage8_cross_sort_fact_congr",
        CROSS_SORT_FACT_CONGR_INPUT,
        &auf,
    );
}

#[test]
fn verifies_cross_sort_term_congruence() {
    let auf = prove_auf(CROSS_SORT_TERM_CONGR_INPUT);

    assert!(auf.contains("by normalize_id"));
    assert!(auf.contains("by len_congr"));
    assert!(auf.contains("$ neq (len (normalize x)) (len x) $"));
    verify_with_external_tools(
        "stage8_cross_sort_term_congr",
        CROSS_SORT_TERM_CONGR_INPUT,
        &auf,
    );
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
