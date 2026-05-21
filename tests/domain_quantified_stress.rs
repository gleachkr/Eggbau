use std::fs;
use std::path::PathBuf;
use std::process::Command;

use eggbau::auf::{AufRenderOptions, render_certificate};
use eggbau::cert::CertStep;
use eggbau::egg::TheoremProof;
use eggbau::export::ExportEnv;
use eggbau::mm0::parse_env;

const QUANTIFIED_BOOL: &str = r#"
delimiter $ ( ) $;
sort obj;
sort bool;
sort wff;
provable sort jdg;
term iff (p q: wff): jdg;
term eqb (x y: bool): jdg;
term all {i: obj} (p: wff i): wff;
term beq (x y: bool): wff;
term top: bool;
term bot: bool;
term and (x y: bool): bool;
term or (x y: bool): bool;
term not (x: bool): bool;

--| @relation bool eqb eqb_refl eqb_trans eqb_sym _
axiom eqb_refl (x: bool): $ eqb x x $;
axiom eqb_trans (x y z: bool):
  $ eqb x y $ > $ eqb y z $ > $ eqb x z $;
axiom eqb_sym (x y: bool): $ eqb x y $ > $ eqb y x $;

--| @relation wff iff iff_refl iff_trans iff_sym _
axiom iff_refl (p: wff): $ iff p p $;
axiom iff_trans (p q r: wff):
  $ iff p q $ > $ iff q r $ > $ iff p r $;
axiom iff_sym (p q: wff): $ iff p q $ > $ iff q p $;

--| @congr
axiom all_congr {i: obj} (p q: wff i):
  $ iff p q $ > $ iff (all i p) (all i q) $;
--| @congr
axiom beq_congr (a b c d: bool):
  $ eqb a b $ > $ eqb c d $ > $ iff (beq a c) (beq b d) $;
--| @congr
axiom and_congr (a b c d: bool):
  $ eqb a b $ > $ eqb c d $ > $ eqb (and a c) (and b d) $;
--| @congr
axiom or_congr (a b c d: bool):
  $ eqb a b $ > $ eqb c d $ > $ eqb (or a c) (or b d) $;
--| @congr
axiom not_congr (a b: bool): $ eqb a b $ > $ eqb (not a) (not b) $;

--| @saturation ltr
axiom and_comm (x y: bool): $ eqb (and x y) (and y x) $;
--| @saturation ltr
axiom and_assoc (x y z: bool):
  $ eqb (and (and x y) z) (and x (and y z)) $;
--| @saturation ltr
axiom and_idem (x: bool): $ eqb (and x x) x $;
--| @saturation ltr
axiom and_top (x: bool): $ eqb (and top x) x $;
--| @saturation ltr
axiom and_bot (x: bool): $ eqb (and bot x) bot $;
--| @saturation ltr
axiom or_comm (x y: bool): $ eqb (or x y) (or y x) $;
--| @saturation ltr
axiom or_assoc (x y z: bool):
  $ eqb (or (or x y) z) (or x (or y z)) $;
--| @saturation ltr
axiom or_idem (x: bool): $ eqb (or x x) x $;
--| @saturation ltr
axiom or_bot (x: bool): $ eqb (or bot x) x $;
--| @saturation ltr
axiom or_top (x: bool): $ eqb (or top x) top $;
--| @saturation ltr
axiom and_absorb (x y: bool): $ eqb (and x (or x y)) x $;
--| @saturation ltr
axiom or_absorb (x y: bool): $ eqb (or x (and x y)) x $;
--| @saturation ltr
axiom and_compl (x: bool): $ eqb (and x (not x)) bot $;
--| @saturation ltr
axiom or_compl (x: bool): $ eqb (or x (not x)) top $;
--| @saturation ltr
axiom not_not (x: bool): $ eqb (not (not x)) x $;
--| @saturation ltr
axiom demorgan_and (x y: bool):
  $ eqb (not (and x y)) (or (not x) (not y)) $;
--| @saturation ltr
axiom demorgan_or (x y: bool):
  $ eqb (not (or x y)) (and (not x) (not y)) $;
--| @saturation ltr
axiom or_factor (x y z: bool):
  $ eqb (or (and x y) (and x z)) (and x (or y z)) $;
--| @saturation ltr
axiom and_factor (x y z: bool):
  $ eqb (and (or x y) (or x z)) (or x (and y z)) $;
"#;

const QUANTIFIED_LIST: &str = r#"
delimiter $ ( ) $;
sort obj;
sort elem;
sort list;
sort nat;
sort wff;
provable sort jdg;
term iff (p q: wff): jdg;
term list_eq (xs ys: list): jdg;
term nat_eq (n m: nat): jdg;
term all {i: obj} (p: wff i): wff;
term list_prop (xs ys: list): wff;
term nat_prop (n m: nat): wff;
term nil: list;
term cons (h: elem) (t: list): list;
term app (xs ys: list): list;
term rev (xs: list): list;
term length (xs: list): nat;
term zero_nat: nat;
term succ (n: nat): nat;
term nat_add (n m: nat): nat;

--| @relation list list_eq list_refl list_trans list_sym _
axiom list_refl (xs: list): $ list_eq xs xs $;
axiom list_trans (xs ys zs: list):
  $ list_eq xs ys $ > $ list_eq ys zs $ > $ list_eq xs zs $;
axiom list_sym (xs ys: list): $ list_eq xs ys $ > $ list_eq ys xs $;

--| @relation nat nat_eq nat_refl nat_trans nat_sym _
axiom nat_refl (n: nat): $ nat_eq n n $;
axiom nat_trans (n m p: nat):
  $ nat_eq n m $ > $ nat_eq m p $ > $ nat_eq n p $;
axiom nat_sym (n m: nat): $ nat_eq n m $ > $ nat_eq m n $;

--| @relation wff iff iff_refl iff_trans iff_sym _
axiom iff_refl (p: wff): $ iff p p $;
axiom iff_trans (p q r: wff):
  $ iff p q $ > $ iff q r $ > $ iff p r $;
axiom iff_sym (p q: wff): $ iff p q $ > $ iff q p $;

--| @congr
axiom all_congr {i: obj} (p q: wff i):
  $ iff p q $ > $ iff (all i p) (all i q) $;
--| @congr
axiom list_prop_congr (a b c d: list):
  $ list_eq a b $ > $ list_eq c d $ > $ iff (list_prop a c) (list_prop b d) $;
--| @congr
axiom nat_prop_congr (a b c d: nat):
  $ nat_eq a b $ > $ nat_eq c d $ > $ iff (nat_prop a c) (nat_prop b d) $;
--| @congr
axiom app_congr (a b c d: list):
  $ list_eq a b $ > $ list_eq c d $ > $ list_eq (app a c) (app b d) $;
--| @congr
axiom rev_congr (a b: list):
  $ list_eq a b $ > $ list_eq (rev a) (rev b) $;
--| @congr
axiom length_congr (a b: list):
  $ list_eq a b $ > $ nat_eq (length a) (length b) $;
--| @congr
axiom succ_congr (n m: nat): $ nat_eq n m $ > $ nat_eq (succ n) (succ m) $;
--| @congr
axiom nat_add_congr (a b c d: nat):
  $ nat_eq a b $ > $ nat_eq c d $ > $ nat_eq (nat_add a c) (nat_add b d) $;

--| @saturation ltr
axiom app_nil_l (xs: list): $ list_eq (app nil xs) xs $;
--| @saturation ltr
axiom app_nil_r (xs: list): $ list_eq (app xs nil) xs $;
--| @saturation ltr
axiom app_assoc (xs ys zs: list):
  $ list_eq (app (app xs ys) zs) (app xs (app ys zs)) $;
--| @saturation ltr
axiom rev_nil: $ list_eq (rev nil) nil $;
--| @saturation ltr
axiom rev_rev (xs: list): $ list_eq (rev (rev xs)) xs $;
--| @saturation ltr
axiom rev_app (xs ys: list):
  $ list_eq (rev (app xs ys)) (app (rev ys) (rev xs)) $;
--| @saturation ltr
axiom length_nil: $ nat_eq (length nil) zero_nat $;
--| @saturation ltr
axiom length_cons (h: elem) (xs: list):
  $ nat_eq (length (cons h xs)) (succ (length xs)) $;
--| @saturation ltr
axiom length_app (xs ys: list):
  $ nat_eq (length (app xs ys)) (nat_add (length xs) (length ys)) $;
--| @saturation ltr
axiom length_rev (xs: list): $ nat_eq (length (rev xs)) (length xs) $;
--| @saturation ltr
axiom nat_add_zero_l (n: nat): $ nat_eq (nat_add zero_nat n) n $;
--| @saturation ltr
axiom nat_add_zero_r (n: nat): $ nat_eq (nat_add n zero_nat) n $;
--| @saturation ltr
axiom nat_add_comm (n m: nat): $ nat_eq (nat_add n m) (nat_add m n) $;
--| @saturation ltr
axiom nat_add_assoc (n m p: nat):
  $ nat_eq (nat_add (nat_add n m) p) (nat_add n (nat_add m p)) $;
"#;

fn prove_and_render(input: &str) -> (TheoremProof, String) {
    let env = parse_env(input).unwrap();
    let export = ExportEnv::from_mm0(&env).unwrap();
    let proof = eggbau::egg::prove_theorem(&env, &export, "target").unwrap();
    let cert = proof.certificate.as_ref().unwrap();
    let rendered =
        render_certificate(&env, &export, "target", cert, AufRenderOptions::default()).unwrap();

    (proof, rendered.text)
}

fn assert_uses_rule(proof: &TheoremProof, name: &str) {
    let cert = proof.certificate.as_ref().unwrap();
    let by_rule = cert
        .steps
        .iter()
        .any(|step| matches!(step, CertStep::RuleApply { mm0_rule, .. } if mm0_rule == name));
    let by_congr = cert.steps.iter().any(|step| {
        matches!(step, CertStep::EqCongr { mm0_congr_rule, .. }
            if mm0_congr_rule == name)
    });

    assert!(by_rule || by_congr, "certificate did not use {name}");
}

#[test]
fn proves_common_rewrite_under_universal_quantifier() {
    let input = format!(
        "{QUANTIFIED_BOOL}\ntheorem target {{i: obj}} (x: bool i):\n  \
         $ iff (all i (beq (and x top) x)) (all i (beq x x)) $;\n"
    );
    let (proof, auf) = prove_and_render(&input);

    assert_uses_rule(&proof, "and_comm");
    assert_uses_rule(&proof, "and_top");
    assert_uses_rule(&proof, "all_congr");
    assert!(proof.proof_summary.congr > 0);
    verify_with_external_tools("quantified_bool_common", &input, &auf);
}

#[test]
fn proves_nested_common_rewrite_under_two_universals() {
    let input = format!(
        "{QUANTIFIED_BOOL}\ntheorem target {{i j: obj}} (x: bool i j):\n  \
         $ iff (all i (all j (beq (not (not x)) x))) \
         (all i (all j (beq x x))) $;\n"
    );
    let (proof, auf) = prove_and_render(&input);

    assert_uses_rule(&proof, "not_not");
    assert_uses_rule(&proof, "all_congr");
    assert!(proof.proof_summary.congr >= 2);
    verify_with_external_tools("quantified_bool_nested", &input, &auf);
}

#[test]
fn stress_boolean_domain_with_quantified_axioms_and_all_congr() {
    let input = format!(
        "{QUANTIFIED_BOOL}\ntheorem target {{i: obj}} (x y: bool i):\n  \
         $ iff (all i (beq (or (and x y) (and x (not y))) x)) \
         (all i (beq x x)) $;\n"
    );
    let (proof, auf) = prove_and_render(&input);

    assert_uses_rule(&proof, "or_factor");
    assert_uses_rule(&proof, "or_compl");
    assert_uses_rule(&proof, "and_top");
    assert_uses_rule(&proof, "all_congr");
    verify_with_external_tools("quantified_bool_stress", &input, &auf);
}

#[test]
fn stress_list_domain_with_quantified_axioms_and_all_congr() {
    let input = format!(
        "{QUANTIFIED_LIST}\ntheorem target {{i: obj}} (xs ys: list i):\n  \
         $ iff (all i (list_prop (rev (app xs ys)) \
         (app (rev ys) (rev xs)))) \
         (all i (list_prop (app (rev ys) (rev xs)) \
         (app (rev ys) (rev xs)))) $;\n"
    );
    let (proof, auf) = prove_and_render(&input);

    assert_uses_rule(&proof, "rev_app");
    assert_uses_rule(&proof, "list_prop_congr");
    assert_uses_rule(&proof, "all_congr");
    verify_with_external_tools("quantified_list_stress", &input, &auf);
}

#[test]
fn stress_cross_sort_quantified_rewrite_through_length() {
    let input = format!(
        "{QUANTIFIED_LIST}\ntheorem target {{i: obj}} (xs: list i):\n  \
         $ iff (all i (nat_prop (length (app xs nil)) (length xs))) \
         (all i (nat_prop (length xs) (length xs))) $;\n"
    );
    let (proof, auf) = prove_and_render(&input);

    assert_uses_rule(&proof, "app_nil_r");
    assert_uses_rule(&proof, "length_congr");
    assert_uses_rule(&proof, "nat_prop_congr");
    assert_uses_rule(&proof, "all_congr");
    verify_with_external_tools("quantified_cross_sort", &input, &auf);
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
        "abc failed
stdout:
{}
stderr:
{}",
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
        "mm0-zig failed
stdout:
{}
stderr:
{}",
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
