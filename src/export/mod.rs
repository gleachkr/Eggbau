use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::Write as _;

use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::discover::{MetadataKind, validate_metadata};
use crate::mm0::{BinderDecl, Formula, MathExpr, Mm0Env, SaturationMode, TermDecl, TheoremDecl};

/// Validated export environment for annotated MM0 assertions.
#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct ExportEnv {
    pub sorts: Vec<ExportSort>,
    pub terms: Vec<ExportTerm>,
    pub relations: BTreeMap<String, RelationBundle>,
    pub saturation_conversions: Vec<SaturationConversionLaw>,
    pub saturation_horn_rules: Vec<SaturationHornLaw>,
    pub congruences: BTreeMap<String, CongruenceLaw>,
    pub assertions: Vec<ExportAssertion>,
}

impl ExportEnv {
    pub fn from_mm0(env: &Mm0Env) -> Result<Self, ExportValidationError> {
        if let Some(error) = validate_metadata(env).into_iter().next() {
            return Err(ExportValidationError {
                theorem: error.theorem,
                use_kind: export_use_for_metadata(error.metadata_kind),
                reason: error.message,
            });
        }

        let term_index = TermIndex::new(env);
        let mut assertions = Vec::new();
        let mut relations = BTreeMap::new();
        let mut relation_by_term = HashMap::new();

        for relation in &env.metadata.relations {
            validate_named_assertion(env, &relation.reflexivity, ExportUse::Relation)?;
            assertions.push(ExportAssertion::relation(&relation.reflexivity));
            validate_named_assertion(env, &relation.transitivity, ExportUse::Relation)?;
            assertions.push(ExportAssertion::relation(&relation.transitivity));
            validate_named_assertion(env, &relation.symmetry, ExportUse::Relation)?;
            assertions.push(ExportAssertion::relation(&relation.symmetry));
            if let Some(transport) = &relation.transport {
                validate_named_assertion(env, transport, ExportUse::Relation)?;
                assertions.push(ExportAssertion::relation(transport));
            }

            let bundle = RelationBundle {
                sort: relation.sort.clone(),
                relation: relation.relation.clone(),
                reflexivity: relation.reflexivity.clone(),
                transitivity: relation.transitivity.clone(),
                symmetry: relation.symmetry.clone(),
                transport: relation.transport.clone(),
            };
            relation_by_term.insert(relation.relation.clone(), relation.sort.clone());
            relations.insert(relation.sort.clone(), bundle);
        }

        let sorts = env
            .sorts
            .iter()
            .map(|sort| ExportSort {
                source_name: sort.name.clone(),
                egglog_name: egglog_sort_name(&sort.name),
                provable: env.sort_is_provable(&sort.name),
            })
            .collect::<Vec<_>>();

        let terms = env
            .terms
            .iter()
            .map(|term| {
                let kind = export_term_kind(env, term, &relation_by_term);
                ExportTerm {
                    source_name: term.name.clone(),
                    egglog_name: egglog_term_name(term, kind),
                    input_sorts: term_input_sorts(term),
                    result_sort: term.result_sort.clone(),
                    kind,
                }
            })
            .collect::<Vec<_>>();

        let mut congruences = BTreeMap::new();
        for congruence in &env.metadata.congruences {
            let theorem = validated_theorem(env, &congruence.theorem, ExportUse::Congruence)?;
            validate_theorem_terms(env, theorem, ExportUse::Congruence)?;
            let shape = relation_formula(&theorem.conclusion, &relation_by_term)
                .expect("metadata validation checked congruence conclusion");
            let term = shape.lhs.head().to_owned();
            congruences.insert(
                term.clone(),
                CongruenceLaw {
                    theorem: congruence.theorem.clone(),
                    term,
                    relation: shape.relation.to_owned(),
                    relation_sort: shape.sort.to_owned(),
                },
            );
            assertions.push(ExportAssertion::congruence(&congruence.theorem));
        }

        let mut saturation_conversions = Vec::new();
        let mut saturation_horn_rules = Vec::new();
        let mut rule_names = BTreeSet::new();
        for saturation in &env.metadata.saturations {
            let theorem = validated_theorem(env, &saturation.theorem, ExportUse::Saturation)?;
            validate_theorem_terms(env, theorem, ExportUse::Saturation)?;
            assertions.push(ExportAssertion::saturation(
                &saturation.theorem,
                saturation.mode,
            ));

            match saturation.mode {
                SaturationMode::Ltr | SaturationMode::Rtl | SaturationMode::Both => {
                    let law = build_conversion_law(
                        theorem,
                        saturation.mode,
                        &term_index,
                        &relation_by_term,
                        &mut rule_names,
                    )?;
                    saturation_conversions.push(law);
                }
                SaturationMode::Horn => {
                    let law =
                        build_horn_law(theorem, &term_index, &relation_by_term, &mut rule_names)?;
                    saturation_horn_rules.push(law);
                }
            }
        }

        let export = Self {
            sorts,
            terms,
            relations,
            saturation_conversions,
            saturation_horn_rules,
            congruences,
            assertions,
        };
        validate_generated_name_collisions(&export)?;
        Ok(export)
    }

    pub fn term(&self, name: &str) -> Option<&ExportTerm> {
        self.terms.iter().find(|term| term.source_name == name)
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct ExportSort {
    pub source_name: String,
    pub egglog_name: String,
    #[serde(default, skip_serializing_if = "is_false")]
    pub provable: bool,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct ExportTerm {
    pub source_name: String,
    pub egglog_name: String,
    pub input_sorts: Vec<String>,
    pub result_sort: String,
    pub kind: ExportTermKind,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ExportTermKind {
    Constructor,
    FactRelation,
    RelationSymbol,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct RelationBundle {
    pub sort: String,
    pub relation: String,
    pub reflexivity: String,
    pub transitivity: String,
    pub symmetry: String,
    pub transport: Option<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct SaturationConversionLaw {
    pub theorem: String,
    pub relation: String,
    pub relation_sort: String,
    pub lhs: String,
    pub rhs: String,
    pub mode: SaturationMode,
    pub rules: Vec<ConversionRule>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct ConversionRule {
    pub rule_name: String,
    pub direction: ConversionDirection,
    pub source_egglog: String,
    pub target_egglog: String,
    pub needs_symmetry_for_mm0: bool,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ConversionDirection {
    Ltr,
    Rtl,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct SaturationHornLaw {
    pub theorem: String,
    pub hypotheses: Vec<HornPremise>,
    pub conclusion: FactPattern,
    pub rule_name: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum HornPremise {
    Fact(FactPattern),
    Equality(EqualityPattern),
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct EqualityPattern {
    pub relation: String,
    pub relation_sort: String,
    pub lhs: String,
    pub rhs: String,
    pub lhs_egglog: String,
    pub rhs_egglog: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct FactPattern {
    pub relation: String,
    pub egglog_relation: String,
    pub arguments: Vec<String>,
    pub egglog_arguments: Vec<String>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct CongruenceLaw {
    pub theorem: String,
    pub term: String,
    pub relation: String,
    pub relation_sort: String,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct ExportAssertion {
    pub theorem: String,
    pub use_kind: ExportUse,
    pub saturation_mode: Option<SaturationMode>,
}

impl ExportAssertion {
    fn relation(theorem: &str) -> Self {
        Self {
            theorem: theorem.to_owned(),
            use_kind: ExportUse::Relation,
            saturation_mode: None,
        }
    }

    fn congruence(theorem: &str) -> Self {
        Self {
            theorem: theorem.to_owned(),
            use_kind: ExportUse::Congruence,
            saturation_mode: None,
        }
    }

    fn saturation(theorem: &str, mode: SaturationMode) -> Self {
        Self {
            theorem: theorem.to_owned(),
            use_kind: ExportUse::Saturation,
            saturation_mode: Some(mode),
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ExportUse {
    Relation,
    Congruence,
    Saturation,
}

#[derive(Debug, Error, Eq, PartialEq)]
#[error("cannot export {theorem} as {use_kind}: {reason}")]
pub struct ExportValidationError {
    pub theorem: String,
    pub use_kind: ExportUse,
    pub reason: String,
}

fn export_use_for_metadata(kind: MetadataKind) -> ExportUse {
    match kind {
        MetadataKind::Relation => ExportUse::Relation,
        MetadataKind::Congruence => ExportUse::Congruence,
        MetadataKind::Saturation => ExportUse::Saturation,
    }
}

fn is_false(value: &bool) -> bool {
    !*value
}

impl std::fmt::Display for ExportUse {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Relation => f.write_str("relation metadata"),
            Self::Congruence => f.write_str("congruence metadata"),
            Self::Saturation => f.write_str("saturation rule"),
        }
    }
}

fn validated_theorem<'a>(
    env: &'a Mm0Env,
    theorem: &str,
    use_kind: ExportUse,
) -> Result<&'a TheoremDecl, ExportValidationError> {
    let theorem_decl = env.theorem(theorem).ok_or_else(|| ExportValidationError {
        theorem: theorem.to_owned(),
        use_kind,
        reason: "referenced theorem was not declared".to_owned(),
    })?;
    validate_theorem(theorem_decl, use_kind)?;
    Ok(theorem_decl)
}

fn validate_named_assertion(
    env: &Mm0Env,
    theorem: &str,
    use_kind: ExportUse,
) -> Result<(), ExportValidationError> {
    validated_theorem(env, theorem, use_kind).map(|_| ())
}

fn validate_theorem(
    theorem: &TheoremDecl,
    use_kind: ExportUse,
) -> Result<(), ExportValidationError> {
    if let Some(reason) = &theorem.unsupported_reason {
        return Err(ExportValidationError {
            theorem: theorem.name.clone(),
            use_kind,
            reason: reason.clone(),
        });
    }

    for formula in theorem
        .hypotheses
        .iter()
        .chain(std::iter::once(&theorem.conclusion))
    {
        validate_formula(&theorem.name, formula, use_kind)?;
    }

    Ok(())
}

fn validate_formula(
    theorem: &str,
    formula: &Formula,
    use_kind: ExportUse,
) -> Result<(), ExportValidationError> {
    if let Some(reason) = &formula.unsupported_reason {
        return Err(ExportValidationError {
            theorem: theorem.to_owned(),
            use_kind,
            reason: reason.clone(),
        });
    }
    if formula.expr.is_none() {
        return Err(ExportValidationError {
            theorem: theorem.to_owned(),
            use_kind,
            reason: "formula did not parse to a kernel expression".to_owned(),
        });
    }
    Ok(())
}

fn validate_theorem_terms(
    env: &Mm0Env,
    theorem: &TheoremDecl,
    use_kind: ExportUse,
) -> Result<(), ExportValidationError> {
    let terms = env
        .terms
        .iter()
        .map(|term| (term.name.as_str(), term))
        .collect::<HashMap<_, _>>();
    let binders = theorem
        .binders
        .iter()
        .map(|binder| binder.name.as_str())
        .collect::<BTreeSet<_>>();

    for formula in theorem
        .hypotheses
        .iter()
        .chain(std::iter::once(&theorem.conclusion))
    {
        let expr = formula.expr.as_ref().expect("validated formula expr");
        validate_expr_terms(expr, theorem, use_kind, &terms, &binders)?;
    }
    Ok(())
}

fn validate_expr_terms(
    expr: &MathExpr,
    theorem: &TheoremDecl,
    use_kind: ExportUse,
    terms: &HashMap<&str, &TermDecl>,
    binders: &BTreeSet<&str>,
) -> Result<(), ExportValidationError> {
    match expr {
        MathExpr::Atom { name } => {
            if binders.contains(name.as_str()) {
                return Ok(());
            }
            let Some(term) = terms.get(name.as_str()) else {
                return Err(ExportValidationError {
                    theorem: theorem.name.clone(),
                    use_kind,
                    reason: format!("formula references undeclared atom: {name}"),
                });
            };
            if !term_input_sorts(term).is_empty() {
                return Err(ExportValidationError {
                    theorem: theorem.name.clone(),
                    use_kind,
                    reason: format!("term {name} is missing arguments"),
                });
            }
            if let Some(reason) = &term.unsupported_reason {
                return Err(ExportValidationError {
                    theorem: theorem.name.clone(),
                    use_kind,
                    reason: format!("term {name} is unsupported: {reason}"),
                });
            }
        }
        MathExpr::App { head, args } => {
            let Some(term) = terms.get(head.as_str()) else {
                return Err(ExportValidationError {
                    theorem: theorem.name.clone(),
                    use_kind,
                    reason: format!("formula references undeclared term: {head}"),
                });
            };
            if let Some(reason) = &term.unsupported_reason {
                return Err(ExportValidationError {
                    theorem: theorem.name.clone(),
                    use_kind,
                    reason: format!("term {head} is unsupported: {reason}"),
                });
            }
            let expected = term_input_sorts(term).len();
            if args.len() != expected {
                return Err(ExportValidationError {
                    theorem: theorem.name.clone(),
                    use_kind,
                    reason: format!(
                        "term {head} has arity {expected}, but formula uses {}",
                        args.len()
                    ),
                });
            }
            for arg in args {
                validate_expr_terms(arg, theorem, use_kind, terms, binders)?;
            }
        }
    }
    Ok(())
}

struct TermIndex<'a> {
    terms: HashMap<&'a str, &'a TermDecl>,
    provable_sorts: BTreeSet<String>,
}

impl<'a> TermIndex<'a> {
    fn new(env: &'a Mm0Env) -> Self {
        Self {
            terms: env
                .terms
                .iter()
                .map(|term| (term.name.as_str(), term))
                .collect(),
            provable_sorts: env
                .sorts
                .iter()
                .filter(|sort| env.sort_is_provable(&sort.name))
                .map(|sort| sort.name.clone())
                .collect(),
        }
    }

    fn get(&self, name: &str) -> Option<&'a TermDecl> {
        self.terms.get(name).copied()
    }

    fn sort_is_provable(&self, sort: &str) -> bool {
        self.provable_sorts.contains(sort)
    }

    fn egglog_term_name(&self, term: &TermDecl) -> String {
        let inputs = term_input_sorts(term);
        if self.sort_is_provable(&term.result_sort)
            && !inputs.iter().any(|sort| self.sort_is_provable(sort))
        {
            egglog_relation_name(&term.name)
        } else {
            pascal_ident(&term.name)
        }
    }
}

fn build_conversion_law(
    theorem: &TheoremDecl,
    mode: SaturationMode,
    term_index: &TermIndex<'_>,
    relation_by_term: &HashMap<String, String>,
    rule_names: &mut BTreeSet<String>,
) -> Result<SaturationConversionLaw, ExportValidationError> {
    let shape = relation_formula(&theorem.conclusion, relation_by_term)
        .expect("metadata validation checked conversion conclusion");
    let lhs = render_math_expr(shape.lhs);
    let rhs = render_math_expr(shape.rhs);
    let lhs_egglog = render_egglog_term(shape.lhs, theorem, term_index)?;
    let rhs_egglog = render_egglog_term(shape.rhs, theorem, term_index)?;

    let rules = match mode {
        SaturationMode::Ltr => vec![conversion_rule(
            &theorem.name,
            ConversionDirection::Ltr,
            &lhs_egglog,
            &rhs_egglog,
            false,
            rule_names,
        )?],
        SaturationMode::Rtl => vec![conversion_rule(
            &theorem.name,
            ConversionDirection::Rtl,
            &rhs_egglog,
            &lhs_egglog,
            true,
            rule_names,
        )?],
        SaturationMode::Both => vec![
            conversion_rule(
                &format!("{}__sat_ltr", theorem.name),
                ConversionDirection::Ltr,
                &lhs_egglog,
                &rhs_egglog,
                false,
                rule_names,
            )?,
            conversion_rule(
                &format!("{}__sat_rtl", theorem.name),
                ConversionDirection::Rtl,
                &rhs_egglog,
                &lhs_egglog,
                true,
                rule_names,
            )?,
        ],
        SaturationMode::Horn => unreachable!("caller split saturation kinds"),
    };

    Ok(SaturationConversionLaw {
        theorem: theorem.name.clone(),
        relation: shape.relation.to_owned(),
        relation_sort: shape.sort.to_owned(),
        lhs,
        rhs,
        mode,
        rules,
    })
}

fn conversion_rule(
    rule_name: &str,
    direction: ConversionDirection,
    source_egglog: &str,
    target_egglog: &str,
    needs_symmetry_for_mm0: bool,
    rule_names: &mut BTreeSet<String>,
) -> Result<ConversionRule, ExportValidationError> {
    ensure_rule_name_fresh(rule_name, ExportUse::Saturation, rule_names)?;
    Ok(ConversionRule {
        rule_name: rule_name.to_owned(),
        direction,
        source_egglog: source_egglog.to_owned(),
        target_egglog: target_egglog.to_owned(),
        needs_symmetry_for_mm0,
    })
}

fn build_horn_law(
    theorem: &TheoremDecl,
    term_index: &TermIndex<'_>,
    relation_by_term: &HashMap<String, String>,
    rule_names: &mut BTreeSet<String>,
) -> Result<SaturationHornLaw, ExportValidationError> {
    ensure_rule_name_fresh(&theorem.name, ExportUse::Saturation, rule_names)?;
    if theorem.hypotheses.is_empty() {
        return Err(ExportValidationError {
            theorem: theorem.name.clone(),
            use_kind: ExportUse::Saturation,
            reason: "horn rules require at least one premise".to_owned(),
        });
    }
    let hypotheses = theorem
        .hypotheses
        .iter()
        .map(|formula| horn_premise(formula, theorem, term_index, relation_by_term))
        .collect::<Result<Vec<_>, _>>()?;
    let conclusion = fact_pattern(&theorem.conclusion, theorem, term_index, relation_by_term)?;

    Ok(SaturationHornLaw {
        theorem: theorem.name.clone(),
        hypotheses,
        conclusion,
        rule_name: theorem.name.clone(),
    })
}

fn ensure_rule_name_fresh(
    rule_name: &str,
    use_kind: ExportUse,
    rule_names: &mut BTreeSet<String>,
) -> Result<(), ExportValidationError> {
    if rule_names.insert(rule_name.to_owned()) {
        Ok(())
    } else {
        Err(ExportValidationError {
            theorem: rule_name.to_owned(),
            use_kind,
            reason: "generated egglog rule name collision".to_owned(),
        })
    }
}

fn horn_premise(
    formula: &Formula,
    theorem: &TheoremDecl,
    term_index: &TermIndex<'_>,
    relation_by_term: &HashMap<String, String>,
) -> Result<HornPremise, ExportValidationError> {
    if let Some(equality) = equality_pattern(formula, theorem, term_index, relation_by_term)? {
        return Ok(HornPremise::Equality(equality));
    }
    fact_pattern(formula, theorem, term_index, relation_by_term).map(HornPremise::Fact)
}

fn equality_pattern(
    formula: &Formula,
    theorem: &TheoremDecl,
    term_index: &TermIndex<'_>,
    relation_by_term: &HashMap<String, String>,
) -> Result<Option<EqualityPattern>, ExportValidationError> {
    let Some(shape) = relation_formula(formula, relation_by_term) else {
        return Ok(None);
    };
    Ok(Some(EqualityPattern {
        relation: shape.relation.to_owned(),
        relation_sort: shape.sort.to_owned(),
        lhs: render_math_expr(shape.lhs),
        rhs: render_math_expr(shape.rhs),
        lhs_egglog: render_egglog_term(shape.lhs, theorem, term_index)?,
        rhs_egglog: render_egglog_term(shape.rhs, theorem, term_index)?,
    }))
}

fn fact_pattern(
    formula: &Formula,
    theorem: &TheoremDecl,
    term_index: &TermIndex<'_>,
    relation_by_term: &HashMap<String, String>,
) -> Result<FactPattern, ExportValidationError> {
    let expr = formula.expr.as_ref().expect("validated formula expr");
    let head = expr.head();
    if relation_by_term.contains_key(head) {
        return Err(ExportValidationError {
            theorem: theorem.name.clone(),
            use_kind: ExportUse::Saturation,
            reason: format!("horn conclusion uses equality relation: {head}"),
        });
    }
    let term = term_index.get(head).ok_or_else(|| ExportValidationError {
        theorem: theorem.name.clone(),
        use_kind: ExportUse::Saturation,
        reason: format!("horn formula references undeclared predicate: {head}"),
    })?;
    if !term_index.sort_is_provable(&term.result_sort) {
        return Err(ExportValidationError {
            theorem: theorem.name.clone(),
            use_kind: ExportUse::Saturation,
            reason: format!("horn formula head does not have a provable sort: {head}"),
        });
    }

    let args: &[MathExpr] = match expr {
        MathExpr::Atom { .. } => &[],
        MathExpr::App { args, .. } => args.as_slice(),
    };
    Ok(FactPattern {
        relation: head.to_owned(),
        egglog_relation: egglog_relation_name(head),
        arguments: args.iter().map(render_math_expr).collect(),
        egglog_arguments: args
            .iter()
            .map(|arg| render_egglog_term(arg, theorem, term_index))
            .collect::<Result<Vec<_>, _>>()?,
    })
}

struct RelationShape<'a> {
    relation: &'a str,
    sort: &'a str,
    lhs: &'a MathExpr,
    rhs: &'a MathExpr,
}

fn relation_formula<'a>(
    formula: &'a Formula,
    relation_by_term: &'a HashMap<String, String>,
) -> Option<RelationShape<'a>> {
    match formula.expr.as_ref()? {
        MathExpr::App { head, args } if args.len() == 2 => {
            relation_by_term.get(head).map(|sort| RelationShape {
                relation: head.as_str(),
                sort: sort.as_str(),
                lhs: &args[0],
                rhs: &args[1],
            })
        }
        _ => None,
    }
}

fn validate_generated_name_collisions(env: &ExportEnv) -> Result<(), ExportValidationError> {
    let mut names = BTreeMap::<String, String>::new();
    insert_generated_name(&mut names, "Goal", "sort Goal")?;
    for sort in &env.sorts {
        insert_generated_name(
            &mut names,
            &sort.egglog_name,
            &format!("sort {}", sort.source_name),
        )?;
    }
    for term in &env.terms {
        if term.kind != ExportTermKind::RelationSymbol {
            insert_generated_name(
                &mut names,
                &term.egglog_name,
                &format!("term {}", term.source_name),
            )?;
        }
    }
    Ok(())
}

fn insert_generated_name(
    names: &mut BTreeMap<String, String>,
    name: &str,
    source: &str,
) -> Result<(), ExportValidationError> {
    if let Some(previous) = names.insert(name.to_owned(), source.to_owned()) {
        return Err(ExportValidationError {
            theorem: name.to_owned(),
            use_kind: ExportUse::Saturation,
            reason: format!("generated egglog name collision between {previous} and {source}"),
        });
    }
    Ok(())
}

pub fn render_egglog(env: &ExportEnv) -> String {
    let mut out = String::new();
    writeln!(out, ";; generated by eggbau; proof search is untrusted").expect("write to string");
    writeln!(out, ";; final MM0/MMB verification remains external").expect("write to string");
    writeln!(out).expect("write to string");

    for sort in &env.sorts {
        writeln!(out, "(sort {})", sort.egglog_name).expect("write to string");
    }
    writeln!(out).expect("write to string");

    for term in &env.terms {
        match term.kind {
            ExportTermKind::Constructor => {
                let inputs = term
                    .input_sorts
                    .iter()
                    .map(|sort| egglog_sort_name(sort))
                    .collect::<Vec<_>>()
                    .join(" ");
                writeln!(
                    out,
                    "(constructor {} ({}) {})",
                    term.egglog_name,
                    inputs,
                    egglog_sort_name(&term.result_sort)
                )
                .expect("write to string");
            }
            ExportTermKind::FactRelation => {
                let inputs = term
                    .input_sorts
                    .iter()
                    .map(|sort| egglog_sort_name(sort))
                    .collect::<Vec<_>>()
                    .join(" ");
                writeln!(out, "(relation {} ({}))", term.egglog_name, inputs)
                    .expect("write to string");
            }
            ExportTermKind::RelationSymbol => {}
        }
    }
    writeln!(out).expect("write to string");

    writeln!(out, "(ruleset saturation)").expect("write to string");
    writeln!(out).expect("write to string");

    for law in &env.saturation_conversions {
        for rule in &law.rules {
            writeln!(
                out,
                "(rule ((= eggbau_lhs {})) ((union eggbau_lhs {})) \
                 :ruleset saturation :name \"{}\")",
                rule.source_egglog, rule.target_egglog, rule.rule_name
            )
            .expect("write to string");
        }
    }
    for law in &env.saturation_horn_rules {
        let body = law
            .hypotheses
            .iter()
            .map(render_horn_premise)
            .collect::<Vec<_>>()
            .join(" ");
        let head = render_fact_pattern(&law.conclusion);
        writeln!(
            out,
            "(rule ({}) ({}) :ruleset saturation :name \"{}\")",
            body, head, law.rule_name
        )
        .expect("write to string");
    }
    out
}

pub fn render_egglog_with_schedule(env: &ExportEnv) -> String {
    let mut out = render_egglog(env);
    writeln!(out).expect("write to string");
    writeln!(out, "(run-schedule (saturate (run saturation)))").expect("write to string");
    out
}

pub fn render_empty_egglog(_env: &ExportEnv) -> String {
    String::new()
}

fn render_horn_premise(premise: &HornPremise) -> String {
    match premise {
        HornPremise::Fact(pattern) => render_fact_pattern(pattern),
        HornPremise::Equality(pattern) => {
            format!("(= {} {})", pattern.lhs_egglog, pattern.rhs_egglog)
        }
    }
}

fn render_fact_pattern(pattern: &FactPattern) -> String {
    render_call(&pattern.egglog_relation, &pattern.egglog_arguments)
}

fn render_call(head: &str, args: &[String]) -> String {
    if args.is_empty() {
        format!("({head})")
    } else {
        format!("({head} {})", args.join(" "))
    }
}

fn render_egglog_term(
    expr: &MathExpr,
    theorem: &TheoremDecl,
    term_index: &TermIndex<'_>,
) -> Result<String, ExportValidationError> {
    let binders = theorem
        .binders
        .iter()
        .map(|binder| binder.name.as_str())
        .collect::<BTreeSet<_>>();
    render_egglog_term_inner(expr, theorem, term_index, &binders)
}

fn render_egglog_term_inner(
    expr: &MathExpr,
    theorem: &TheoremDecl,
    term_index: &TermIndex<'_>,
    binders: &BTreeSet<&str>,
) -> Result<String, ExportValidationError> {
    match expr {
        MathExpr::Atom { name } if binders.contains(name.as_str()) => Ok(variable_name(name)),
        MathExpr::Atom { name } => {
            let term = term_index.get(name).ok_or_else(|| ExportValidationError {
                theorem: theorem.name.clone(),
                use_kind: ExportUse::Saturation,
                reason: format!("formula references undeclared atom: {name}"),
            })?;
            Ok(render_call(&term_index.egglog_term_name(term), &[]))
        }
        MathExpr::App { head, args } => {
            let term = term_index.get(head).ok_or_else(|| ExportValidationError {
                theorem: theorem.name.clone(),
                use_kind: ExportUse::Saturation,
                reason: format!("formula references undeclared term: {head}"),
            })?;
            let rendered_args = args
                .iter()
                .map(|arg| render_egglog_term_inner(arg, theorem, term_index, binders))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(render_call(
                &term_index.egglog_term_name(term),
                &rendered_args,
            ))
        }
    }
}

fn render_math_expr(expr: &MathExpr) -> String {
    match expr {
        MathExpr::Atom { name } => name.clone(),
        MathExpr::App { head, args } => {
            let args = args.iter().map(render_math_expr).collect::<Vec<_>>();
            format!("{} {}", head, args.join(" "))
        }
    }
}

fn export_term_kind(
    env: &Mm0Env,
    term: &TermDecl,
    relation_by_term: &HashMap<String, String>,
) -> ExportTermKind {
    if relation_by_term.contains_key(&term.name) {
        return ExportTermKind::RelationSymbol;
    }

    let inputs = term_input_sorts(term);
    if env.sort_is_provable(&term.result_sort)
        && !inputs.iter().any(|sort| env.sort_is_provable(sort))
    {
        ExportTermKind::FactRelation
    } else {
        ExportTermKind::Constructor
    }
}

fn term_input_sorts(term: &TermDecl) -> Vec<String> {
    if term.input_sorts.is_empty() {
        term.binders
            .iter()
            .map(|binder: &BinderDecl| binder.sort.clone())
            .collect()
    } else {
        term.input_sorts.clone()
    }
}

fn egglog_sort_name(name: &str) -> String {
    pascal_ident(name)
}

fn egglog_term_name(term: &TermDecl, kind: ExportTermKind) -> String {
    if kind == ExportTermKind::FactRelation {
        egglog_relation_name(&term.name)
    } else {
        pascal_ident(&term.name)
    }
}

fn egglog_relation_name(name: &str) -> String {
    snake_ident(name)
}

fn pascal_ident(name: &str) -> String {
    let mut out = String::new();
    for part in name.split('_').filter(|part| !part.is_empty()) {
        let mut chars = part.chars();
        if let Some(first) = chars.next() {
            out.extend(first.to_uppercase());
            out.push_str(chars.as_str());
        }
    }
    if out.is_empty() {
        "Generated".to_owned()
    } else {
        out
    }
}

fn snake_ident(name: &str) -> String {
    let mut out = String::new();
    for (idx, ch) in name.chars().enumerate() {
        if ch.is_ascii_alphanumeric() || ch == '_' {
            if idx == 0 && ch.is_ascii_digit() {
                out.push('_');
            }
            out.push(ch.to_ascii_lowercase());
        } else {
            out.push('_');
        }
    }
    if out.is_empty() { "_".to_owned() } else { out }
}

fn variable_name(name: &str) -> String {
    format!("v_{}", snake_ident(name))
}

#[cfg(test)]
mod tests {
    use super::{ExportEnv, render_egglog};
    use crate::mm0::parse_env;

    #[test]
    fn renders_smoke_program() {
        let env = parse_env(
            r#"
sort s;
provable sort wff;
term z: s;
term f (x: s): s;
term eq (x y: s): wff;
--| @relation s eq eq_refl eq_trans eq_sym _
axiom eq_refl (x: s): $ eq x x $;
axiom eq_trans (x y z: s): $ eq x y $ > $ eq y z $ > $ eq x z $;
axiom eq_sym (x y: s): $ eq x y $ > $ eq y x $;
--| @saturation ltr
axiom f_id (x: s): $ eq (f x) x $;
"#,
        )
        .unwrap();
        let export = ExportEnv::from_mm0(&env).unwrap();
        let egglog = render_egglog(&export);

        assert!(egglog.contains("(constructor F (S) S)"));
        assert!(egglog.contains(":name \"f_id\""));
        assert!(!egglog.contains("Goal"));
        assert!(!egglog.contains("ruleset goals"));
    }
}
