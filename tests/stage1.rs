use std::process::Command;

mod common;

use eggbau::export::ExportEnv;
use eggbau::mm0::{MathExpr, NotationKind, SaturationMode, parse_env};

const STAGE1_INPUT: &str = include_str!("fixtures/stage1/input.mm0");

#[test]
fn parses_declarations_and_metadata() {
    let env = parse_env(STAGE1_INPUT).unwrap();

    assert_eq!(
        env.sorts
            .iter()
            .map(|sort| sort.name.as_str())
            .collect::<Vec<_>>(),
        ["bv64", "wff"]
    );
    assert_eq!(env.terms.len(), 4);
    assert!(env.theorem("bv_add_zero").is_some());
    assert!(env.theorem("writable_from_eq").is_some());

    let add_zero = env.theorem("bv_add_zero").unwrap();
    assert_eq!(add_zero.binders[0].name, "x");
    assert_eq!(add_zero.conclusion.source, "bv_eq (bv_add x bv0) x");
    assert_eq!(add_zero.conclusion.head(), Some("bv_eq"));

    assert_eq!(env.metadata.relations.len(), 1);
    assert_eq!(env.metadata.relations[0].relation, "bv_eq");
    assert_eq!(env.metadata.congruences[0].theorem, "bv_add_congr");
    assert_eq!(env.metadata.saturations[0].theorem, "bv_add_zero");
    assert_eq!(env.metadata.saturations[0].mode, SaturationMode::Ltr);
    assert_eq!(env.metadata.saturations[1].theorem, "writable_from_eq");
    assert_eq!(env.metadata.saturations[1].mode, SaturationMode::Horn);

    let export = ExportEnv::from_mm0(&env).unwrap();
    assert_eq!(export.assertions.len(), 6);
}

#[test]
fn dump_env_snapshot_is_deterministic() {
    let binary = env!("CARGO_BIN_EXE_eggbau");
    let file = "tests/fixtures/stage1/input.mm0";

    let output = Command::new(binary)
        .args(["dump-env", file])
        .output()
        .unwrap();

    assert!(output.status.success());
    assert!(output.stderr.is_empty());
    insta::assert_snapshot!(String::from_utf8(output.stdout).unwrap());
}

#[test]
fn dump_env_can_print_a_designated_theorem() {
    let binary = env!("CARGO_BIN_EXE_eggbau");
    let file = "tests/fixtures/stage1/input.mm0";

    let output = Command::new(binary)
        .args(["dump-env", file, "--theorem", "bv_add_zero"])
        .output()
        .unwrap();

    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(stdout.contains("\"name\": \"bv_add_zero\""));
    assert!(stdout.contains("\"source\": \"bv_eq (bv_add x bv0) x\""));
}

#[test]
fn duplicate_term_declaration_is_a_clear_error() {
    let err = parse_env("sort s; term z: s; term z: s;").unwrap_err();

    assert!(err.message.contains("duplicate declaration name: z"));
}

#[test]
fn sort_and_term_names_can_overlap_like_upstream_mm0() {
    let env = parse_env("sort s; term s: s;").unwrap();

    assert_eq!(env.sorts[0].name, "s");
    assert_eq!(env.terms[0].name, "s");
}

#[test]
fn notation_directives_are_stored_for_formula_parsing() {
    let env = parse_env("sort s; term z: s; prefix z: $0$ prec max;").unwrap();

    assert!(env.diagnostics.is_empty());
    assert_eq!(env.notations.len(), 1);
    assert_eq!(env.notations[0].term.as_deref(), Some("z"));
    assert_eq!(env.notations[0].tokens, ["0"]);
}

#[test]
fn unknown_saturation_argument_is_a_clear_error() {
    let err = parse_env(
        r#"
sort s;
--| @saturation sideways
theorem t: $ s $;
"#,
    )
    .unwrap_err();

    assert!(err.message.contains("unknown @saturation argument"));
}

#[test]
fn annotated_dependency_heavy_theorems_parse_but_remain_unsupported() {
    let env = parse_env(
        r#"
sort nat;
sort wff;
term p (x: nat): wff;
--| @saturation ltr
theorem dep {x: nat} (q: wff x): $ p x $;
"#,
    )
    .unwrap();

    assert_eq!(env.metadata.saturations[0].theorem, "dep");
    assert!(
        env.theorem("dep")
            .unwrap()
            .unsupported_reason
            .as_deref()
            .is_some_and(|reason| reason.contains("bound binders"))
    );
}

#[test]
fn export_validation_ignores_unannotated_unsupported_theorems() {
    let env = parse_env(
        r#"
        sort nat;
        sort wff;
        term eq (x y: nat): wff;
        term p (x: nat): wff;
        --| @relation nat eq eq_refl eq_trans eq_sym _
        axiom eq_refl (x: nat): $ eq x x $;
        axiom eq_trans (x y z: nat):
          $ eq x y $ > $ eq y z $ > $ eq x z $;
        axiom eq_sym (x y: nat): $ eq x y $ > $ eq y x $;
        theorem dep {x: nat} (q: wff x): $ p x $;
        --| @saturation ltr
        theorem safe (x: nat): $ eq x x $;
        "#,
    )
    .unwrap();

    let export = ExportEnv::from_mm0(&env).unwrap();

    assert_eq!(export.assertions.len(), 4);
    assert!(
        export
            .assertions
            .iter()
            .any(|assertion| assertion.theorem == "safe")
    );
}

#[test]
fn export_validation_rejects_annotated_unsupported_theorems() {
    let env = parse_env(
        r#"
        sort nat;
        sort wff;
        term p (x: nat): wff;
        --| @saturation ltr
        theorem dep {x: nat} (q: wff x): $ p x $;
        "#,
    )
    .unwrap();

    let err = ExportEnv::from_mm0(&env).unwrap_err();

    assert_eq!(err.theorem, "dep");
    assert!(err.reason.contains("bound binders"));
}

#[test]
fn saturation_on_term_is_a_clear_error() {
    let err = parse_env(
        r#"
--| @saturation ltr
term z: s;
"#,
    )
    .unwrap_err();

    assert!(err.message.contains("cannot attach to a term declaration"));
}

#[test]
fn parses_copied_third_party_fixture_inventory() {
    for fixture in common::TOP_LEVEL_THIRD_PARTY_FIXTURES {
        let env = parse_env(fixture.input).unwrap_or_else(|err| {
            panic!(
                "copied third-party fixture {} did not parse: {err}",
                fixture.name
            )
        });

        assert_eq!(
            env.sorts.len(),
            fixture.expected.sorts,
            "sort count for {}",
            fixture.name
        );
        assert_eq!(
            env.terms.len(),
            fixture.expected.terms,
            "term count for {}",
            fixture.name
        );
        assert_eq!(
            env.theorems.len(),
            fixture.expected.theorems,
            "theorem count for {}",
            fixture.name
        );
        assert_eq!(
            env.notations.len(),
            fixture.expected.notations,
            "notation count for {}",
            fixture.name
        );
    }
}

#[test]
fn parses_copied_third_party_stress_suite() {
    let paths = common::stress_fixture_paths();

    let mut totals = StressTotals::default();
    for path in &paths {
        let input = std::fs::read_to_string(path).unwrap();
        let env = parse_env(&input)
            .unwrap_or_else(|err| panic!("stress fixture {} did not parse: {err}", path.display()));

        totals.sorts += env.sorts.len();
        totals.terms += env.terms.len();
        totals.theorems += env.theorems.len();
        totals.notations += env.notations.len();
        totals.diagnostics += env.diagnostics.len();
        totals.unsupported_terms += env
            .terms
            .iter()
            .filter(|term| term.unsupported_reason.is_some())
            .count();
        totals.unsupported_theorems += env
            .theorems
            .iter()
            .filter(|theorem| theorem.unsupported_reason.is_some())
            .count();
    }

    assert_eq!(paths.len(), 43);
    assert_eq!(totals.sorts, 107);
    assert_eq!(totals.terms, 510);
    assert_eq!(totals.theorems, 1618);
    assert_eq!(totals.notations, 447);
    assert_eq!(totals.diagnostics, 3);
    assert_eq!(totals.unsupported_terms, 94);
    assert_eq!(totals.unsupported_theorems, 523);
}

#[derive(Default)]
struct StressTotals {
    sorts: usize,
    terms: usize,
    theorems: usize,
    notations: usize,
    diagnostics: usize,
    unsupported_terms: usize,
    unsupported_theorems: usize,
}

#[test]
fn parses_mm0_hello_sort_modifiers_arrow_types_and_defs() {
    let env = parse_env(common::MM0_HELLO).unwrap();

    assert_eq!(
        env.sorts
            .iter()
            .map(|sort| sort.name.as_str())
            .collect::<Vec<_>>(),
        ["hex", "char", "string"]
    );

    let ch = env.terms.iter().find(|term| term.name == "ch").unwrap();
    assert_eq!(ch.input_sorts, ["hex", "hex"]);
    assert_eq!(ch.result_sort, "char");

    let sadd = env.terms.iter().find(|term| term.name == "sadd").unwrap();
    assert_eq!(sadd.input_sorts, ["string", "string"]);
    assert_eq!(sadd.result_sort, "string");

    let bang = env.terms.iter().find(|term| term.name == "bang").unwrap();
    assert_eq!(bang.result_sort, "string");
    assert!(env.diagnostics.iter().any(|diagnostic| {
        diagnostic.message.contains("unsupported MM0 statement")
            && diagnostic.message.contains("output string")
    }));
}

#[test]
fn parses_aufbau_relation_congruence_and_ignored_rewrites() {
    let env = parse_env(common::AUFBAU_PASS_NORMALIZE_IDENTITY).unwrap();

    assert_eq!(env.sorts[0].name, "wff");
    assert_eq!(env.metadata.relations.len(), 1);
    assert_eq!(env.metadata.relations[0].relation, "bi");
    assert_eq!(env.metadata.relations[0].transport.as_deref(), Some("mpbi"));
    assert_eq!(env.metadata.congruences.len(), 1);
    assert_eq!(env.metadata.congruences[0].theorem, "im_congr");
    assert!(env.metadata.saturations.is_empty());

    let theorem = env.theorem("test_single_step").unwrap();
    assert_eq!(theorem.conclusion.source, "Q");
    assert_eq!(theorem.conclusion.head(), Some("Q"));

    let sb_p = env.theorem("sb_P").unwrap();
    assert_eq!(sb_p.conclusion.source, "sb a P <-> a");
    assert_eq!(sb_p.conclusion.head(), Some("bi"));
    assert!(sb_p.conclusion.unsupported_reason.is_none());
}

#[test]
fn desugars_prefix_infix_and_constant_notation_to_kernel_terms() {
    let env = parse_env(common::AUFBAU_PASS_NORMALIZE_IDENTITY).unwrap();

    let biid = env.theorem("biid").unwrap();
    assert_eq!(biid.conclusion.head(), Some("bi"));
    let MathExpr::App { head, args } = biid.conclusion.expr.as_ref().unwrap() else {
        panic!("biid conclusion should be an application");
    };
    assert_eq!(head, "bi");
    assert_eq!(args.len(), 2);

    let im_congr = env.theorem("im_congr").unwrap();
    let MathExpr::App { head, args } = im_congr.conclusion.expr.as_ref().unwrap() else {
        panic!("im_congr conclusion should be an application");
    };
    assert_eq!(head, "bi");
    assert_eq!(args[0].head(), "im");
    assert_eq!(args[1].head(), "im");
}

#[test]
fn desugars_general_prefix_notation_without_fixture_assumptions() {
    let env = parse_env(
        r#"
sort s;
term wrap (x y: s): s;
notation wrap (x y: s): s = ($<$:60) x ($:$:40) y ($>$:0);
theorem t (a b: s): $ < a : b > $;
"#,
    )
    .unwrap();

    let theorem = env.theorem("t").unwrap();
    let MathExpr::App { head, args } = theorem.conclusion.expr.as_ref().unwrap() else {
        panic!("general prefix notation should parse as an application");
    };
    assert_eq!(head, "wrap");
    assert_eq!(args.len(), 2);
    assert_eq!(args[0].head(), "a");
    assert_eq!(args[1].head(), "b");
}

#[test]
fn desugars_general_infix_notation_without_fixture_assumptions() {
    let env = parse_env(
        r#"
sort s;
term triple (x y z: s): s;
notation triple (x y z: s): s = x ($<+>$:30) y ($//$:30) z : 30 lassoc;
theorem t (a b c: s): $ a <+> b // c $;
"#,
    )
    .unwrap();

    let theorem = env.theorem("t").unwrap();
    let MathExpr::App { head, args } = theorem.conclusion.expr.as_ref().unwrap() else {
        panic!("general infix notation should parse as an application");
    };
    assert_eq!(head, "triple");
    assert_eq!(args.len(), 3);
    assert_eq!(args[0].head(), "a");
    assert_eq!(args[1].head(), "b");
    assert_eq!(args[2].head(), "c");
}

#[test]
fn desugars_simple_general_notation_to_kernel_terms() {
    let env = parse_env(common::MM0_PEANO).unwrap();
    let elab = env.theorem("elab").unwrap();

    assert_eq!(elab.conclusion.source, "a e. {x | p} <-> [ a / x ] p");
    assert_eq!(elab.conclusion.head(), Some("iff"));
    assert!(elab.conclusion.unsupported_reason.is_none());

    let MathExpr::App { head, args } = elab.conclusion.expr.as_ref().unwrap() else {
        panic!("elab conclusion should be an application");
    };
    assert_eq!(head, "iff");
    assert_eq!(args[0].head(), "el");
    assert_eq!(args[1].head(), "sb");
}

#[test]
fn parses_mm0_peano_without_rejecting_unsupported_binders() {
    let env = parse_env(common::MM0_PEANO).unwrap();

    assert!(env.diagnostics.is_empty());
    assert!(env.notations.iter().any(|notation| {
        notation.term.as_deref() == Some("ns") && notation.kind == NotationKind::Coercion
    }));

    assert_eq!(
        env.sorts
            .iter()
            .map(|sort| sort.name.as_str())
            .collect::<Vec<_>>(),
        ["wff", "nat", "set"]
    );

    let ax_mp = env.theorem("ax_mp").unwrap();
    assert_eq!(
        ax_mp
            .hypotheses
            .iter()
            .map(|formula| formula.source.as_str())
            .collect::<Vec<_>>(),
        ["a -> b", "a"]
    );
    assert_eq!(ax_mp.conclusion.source, "b");
    assert!(ax_mp.unsupported_reason.is_none());

    let al = env.terms.iter().find(|term| term.name == "al").unwrap();
    assert!(
        al.unsupported_reason
            .as_deref()
            .is_some_and(|reason| reason.contains("bound binders"))
    );

    let sb = env.terms.iter().find(|term| term.name == "sb").unwrap();
    assert!(
        sb.unsupported_reason
            .as_deref()
            .is_some_and(|reason| reason.contains("hidden dummy"))
    );

    let nat = env.terms.iter().find(|term| term.name == "nat").unwrap();
    assert_eq!(nat.result_sort, "nat");
}
