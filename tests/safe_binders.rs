use std::path::Path;
use std::process::Command;

use eggbau::auf::{AufRenderOptions, render_certificate};
use eggbau::cert::{CertStep, Certificate, Formula as CertFormula, Label, Term};
use eggbau::export::{ExportEnv, render_egglog};
use eggbau::mm0::{BinderKind, parse_env};

const SAFE_BASE: &str = r#"
delimiter $ ( ) $;
sort obj;
sort wff;
provable sort jdg;
term iff (p q: wff): jdg;
term all {x: obj} (p: wff x): wff;
term disj {x: obj} (p q: wff x): wff;
term valid {x: obj} (p: wff x): jdg;
--| @relation wff iff iff_refl iff_trans iff_sym _
axiom iff_refl (p: wff): $ iff p p $;
axiom iff_trans (p q r: wff): $ iff p q $ > $ iff q r $ > $ iff p r $;
axiom iff_sym (p q: wff): $ iff p q $ > $ iff q p $;
--| @congr
axiom all_congr {x: obj} (p q: wff x):
  $ iff p q $ > $ iff (all x p) (all x q) $;
--| @saturation ltr
axiom all_or {x: obj} (p q: wff x):
  $ iff (disj x (all x p) (all x q)) (all x (disj x p q)) $;
--| @saturation horn
axiom valid_all_or {x: obj} (p q: wff x):
  $ valid x (disj x p q) $ > $ valid x (all x (disj x p q)) $;
"#;

#[test]
fn parses_safe_term_and_assertion_binders() {
    let env = parse_env(SAFE_BASE).unwrap();
    let all = env.terms.iter().find(|term| term.name == "all").unwrap();

    assert_eq!(all.binders[0].kind, BinderKind::Bound);
    assert_eq!(all.binders[1].kind, BinderKind::Regular);
    assert_eq!(all.binders[1].deps, ["x"]);

    let all_congr = env.theorem("all_congr").unwrap();
    assert!(all_congr.unsupported_reason.is_none());
    assert_eq!(all_congr.binders.len(), 3);
    assert_eq!(all_congr.binders[1].deps, ["x"]);
}

#[test]
fn parses_multiple_bound_binders_with_full_dependencies() {
    let env = parse_env(
        r#"
sort obj;
provable sort wff;
term iff (p q: wff): wff;
axiom safe2 {x y: obj} (p q: wff x y): $ iff p q $;
"#,
    )
    .unwrap();
    let theorem = env.theorem("safe2").unwrap();

    assert_eq!(theorem.binders[0].kind, BinderKind::Bound);
    assert_eq!(theorem.binders[1].kind, BinderKind::Bound);
    assert_eq!(theorem.binders[2].deps, ["x", "y"]);
    assert!(theorem.unsupported_reason.is_none());
}

#[test]
fn malformed_binder_group_has_stable_diagnostic() {
    let err = parse_env("sort s; term f (x s): s;").unwrap_err();

    assert!(err.message.contains("binder group is missing ':'"));
}

#[test]
fn export_accepts_safe_congruence_and_saturation_rules() {
    let env = parse_env(SAFE_BASE).unwrap();
    let export = ExportEnv::from_mm0(&env).unwrap();

    assert!(export.congruences.contains_key("all"));
    assert_eq!(export.saturation_conversions[0].theorem, "all_or");
    assert_eq!(export.saturation_horn_rules[0].theorem, "valid_all_or");
}

#[test]
fn generated_egglog_for_safe_binders_is_deterministic() {
    let env = parse_env(SAFE_BASE).unwrap();
    let export = ExportEnv::from_mm0(&env).unwrap();
    let egglog = render_egglog(&export);

    assert!(egglog.contains("(constructor All (Obj Wff) Wff)"));
    assert!(egglog.contains("(relation valid (Obj Wff))"));
    assert!(egglog.contains(":name \"all_or\""));
    assert!(egglog.contains(":name \"valid_all_or\""));
    assert!(egglog.contains("v_x"));
    assert!(egglog.contains("v_p"));
    assert!(egglog.contains("v_q"));
}

#[test]
fn rejects_regular_binder_before_later_bound_binder() {
    let err = export_error(
        r#"
--| @saturation ltr
axiom bad (p: wff) {x: obj}: $ iff p p $;
"#,
    );

    assert!(err.contains("misordered"));
    assert!(err.contains("x"));
}

#[test]
fn rejects_regular_binder_missing_bound_dependency() {
    let err = export_error(
        r#"
--| @saturation ltr
axiom bad {x y: obj} (p: wff x): $ iff p p $;
"#,
    );

    assert!(err.contains("p"));
    assert!(err.contains("missing dependency y"));
}

#[test]
fn rejects_unknown_or_later_dependency() {
    let err = export_error(
        r#"
--| @saturation ltr
axiom bad {x: obj} (p: wff y): $ iff p p $;
"#,
    );

    assert!(err.contains("p"));
    assert!(err.contains("unknown or later bound binder y"));
}

#[test]
fn rejects_duplicate_binder_names() {
    let err = export_error(
        r#"
--| @saturation ltr
axiom bad {x: obj} (x: wff x): $ iff x x $;
"#,
    );

    assert!(err.contains("duplicate binder x"));
}

#[test]
fn rejects_vacuous_bound_binder_that_cannot_be_recovered() {
    let err = export_error(
        r#"
--| @saturation ltr
axiom bad {x: obj} (p: wff x): $ iff p p $;
"#,
    );

    assert!(err.contains("bound binder x"));
    assert!(err.contains("cannot be recovered"));
}

#[test]
fn rejects_hidden_dummy_binders() {
    let err = export_error(
        r#"
--| @saturation ltr
axiom bad {.x: obj} (p: wff x): $ iff p p $;
"#,
    );

    assert!(err.contains("hidden dummy"));
}

#[test]
fn safe_bound_binder_horn_rule_proves_and_renders_explicit_bindings() {
    let input = format!(
        "{SAFE_BASE}\ntheorem target {{x: obj}} (p q: wff x): \
         $ valid x (disj x p q) $ > \
         $ valid x (all x (disj x p q)) $;\n"
    );
    let env = parse_env(&input).unwrap();
    let export = ExportEnv::from_mm0(&env).unwrap();
    let proof = eggbau::egg::prove_theorem(&env, &export, "target").unwrap();
    let cert = proof.certificate.unwrap();

    assert!(cert.steps.iter().any(|step| {
        matches!(step, CertStep::RuleApply { mm0_rule, .. }
            if mm0_rule == "valid_all_or")
    }));

    let rendered =
        render_certificate(&env, &export, "target", &cert, AufRenderOptions::default()).unwrap();

    assert!(rendered.text.contains("by valid_all_or"));
    assert!(rendered.text.contains("x := $ x $"));
    assert!(rendered.text.contains("p := $ p $"));
    assert!(rendered.text.contains("q := $ q $"));
}

#[test]
fn renderer_rejects_duplicate_bound_binder_instantiation() {
    let env = parse_env(
        r#"
sort obj;
provable sort jdg;
term eq (x y: obj): jdg;
--| @relation obj eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: obj): $ eq x x $;
axiom eq_trans (x y z: obj): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: obj): $ eq x y $ > $ eq y x $;
--| @saturation ltr
axiom bad {x y: obj}: $ eq x y $;
theorem target {z: obj}: $ eq z z $;
"#,
    )
    .unwrap();
    let export = ExportEnv::from_mm0(&env).unwrap();
    let cert = Certificate::new(vec![CertStep::RuleApply {
        label: Label::from("l1"),
        formula: CertFormula::rel("eq", Term::var("z"), Term::var("z")),
        mm0_rule: "bad".to_owned(),
        bindings: Vec::new(),
        refs: Vec::new(),
    }]);

    let err = render_certificate(&env, &export, "target", &cert, AufRenderOptions::default())
        .unwrap_err()
        .to_string();

    assert!(err.contains("duplicate"));
    assert!(err.contains("variable `z`"));
}

#[test]
fn safe_bound_binder_fragment_verifies_end_to_end_when_tools_exist() {
    if !tool_available("abc") || !tool_available("mm0-zig") {
        eprintln!("skipping safe-binder e2e: abc or mm0-zig is not on PATH");
        return;
    }

    let input = format!(
        "{SAFE_BASE}\ntheorem target {{x: obj}} (p q: wff x): \
         $ valid x (disj x p q) $ > \
         $ valid x (all x (disj x p q)) $;\n"
    );
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("target/safe_binders_e2e");
    std::fs::create_dir_all(&dir).unwrap();
    let mm0_path = dir.join("input.mm0");
    let auf_path = dir.join("generated.auf");
    let mmb_path = dir.join("generated.mmb");
    std::fs::write(&mm0_path, input).unwrap();

    let prove = Command::new(env!("CARGO_BIN_EXE_eggbau"))
        .args([
            "prove",
            mm0_path.to_str().unwrap(),
            "--theorem",
            "target",
            "--out",
            auf_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        prove.status.success(),
        "{}",
        String::from_utf8_lossy(&prove.stderr)
    );

    let compile = Command::new("abc")
        .args([
            "compile",
            mm0_path.to_str().unwrap(),
            auf_path.to_str().unwrap(),
            mmb_path.to_str().unwrap(),
        ])
        .output()
        .unwrap();
    assert!(
        compile.status.success(),
        "{}",
        String::from_utf8_lossy(&compile.stderr)
    );

    let input_file = std::fs::File::open(&mm0_path).unwrap();
    let verify = Command::new("mm0-zig")
        .arg(&mmb_path)
        .stdin(input_file)
        .output()
        .unwrap();
    assert!(
        verify.status.success(),
        "{}",
        String::from_utf8_lossy(&verify.stderr)
    );
}

fn export_error(extra: &str) -> String {
    let input = format!(
        r#"
sort obj;
sort wff;
provable sort jdg;
term iff (p q: wff): jdg;
--| @relation wff iff iff_refl iff_trans iff_sym _
axiom iff_refl (p: wff): $ iff p p $;
axiom iff_trans (p q r: wff): $ iff p q $ > $ iff q r $ > $ iff p r $;
axiom iff_sym (p q: wff): $ iff p q $ > $ iff q p $;
{extra}
"#
    );
    let env = parse_env(&input).unwrap();

    ExportEnv::from_mm0(&env).unwrap_err().to_string()
}

fn tool_available(name: &str) -> bool {
    Command::new(name)
        .arg("--help")
        .output()
        .map(|_| true)
        .unwrap_or(false)
}
