use std::{
    collections::{HashMap, HashSet},
    io::Read,
    path::Path,
};

use crate::{
    EggbauError, OutputMode, ProofTarget,
    auf::{AufMathFormat, AufRenderCompaction, AufRenderExplicitness, AufRenderFormat},
    discover, export, mm0, version_report,
};

/// Run the eggbau command line using the provided argument iterator.
pub fn run<I, S>(args: I) -> Result<String, EggbauError>
where
    I: IntoIterator<Item = S>,
    S: Into<String>,
{
    let mut args = args.into_iter().map(Into::into);
    let _program = args.next();

    match args.next().as_deref() {
        None | Some("--help") | Some("-h") | Some("help") => Ok(help_text()),
        Some("--version") | Some("-V") | Some("version") => Ok(version_report()),
        Some("discover") => run_discover(args),
        Some("list") => run_list(args),
        Some("lint") => run_lint(args),
        Some("prove") => run_prove(args),
        Some("script") => run_script(args),
        Some(other) => Err(EggbauError::UnsupportedCommand(other.to_owned())),
    }
}

fn run_discover(mut args: impl Iterator<Item = String>) -> Result<String, EggbauError> {
    let file = args.next().ok_or_else(|| {
        EggbauError::UnsupportedCommand("discover requires an MM0 input path".to_owned())
    })?;
    let mut suggest_annotations = false;
    for arg in args {
        match arg.as_str() {
            "--suggest-annotations" => suggest_annotations = true,
            other => return Err(EggbauError::UnsupportedCommand(other.to_owned())),
        }
    }
    let mm0 = read_mm0(&file)?;

    discover::render_discovery(Path::new(&file), &mm0, suggest_annotations)
}

fn run_list(mut args: impl Iterator<Item = String>) -> Result<String, EggbauError> {
    let file = args.next().ok_or_else(|| {
        EggbauError::UnsupportedCommand("list requires an MM0 input path".to_owned())
    })?;
    reject_extra_args(args)?;

    let input = read_mm0(&file)?;
    let env = mm0::parse_env(&input)?;
    let mut output = String::new();
    for theorem in &env.theorems {
        if is_listable_public_theorem(theorem) {
            output.push_str("theorem ");
            output.push_str(&theorem.name);
            output.push('\n');
        }
    }
    Ok(output)
}

fn is_listable_public_theorem(theorem: &mm0::TheoremDecl) -> bool {
    theorem.kind == mm0::AssertionKind::Theorem && theorem.unsupported_reason.is_none()
}

fn run_lint(mut args: impl Iterator<Item = String>) -> Result<String, EggbauError> {
    let file = args.next().ok_or_else(|| {
        EggbauError::UnsupportedCommand("lint requires an MM0 input path".to_owned())
    })?;
    reject_extra_args(args)?;

    let input = read_mm0(&file)?;
    let env = mm0::parse_env(&input)?;
    let report = discover::DiscoveryReport::from_env(&env);
    if !report.metadata_errors.is_empty() {
        let mut out = String::new();
        out.push_str("metadata lint failed\n");
        for error in report.metadata_errors {
            out.push_str(&format!(
                "{} ({}): {}\n",
                error.theorem, error.metadata_kind, error.message
            ));
        }
        return Err(EggbauError::UnsupportedCommand(out));
    }
    export::ExportEnv::from_mm0(&env)?;
    Ok("metadata lint ok\n".to_owned())
}

fn run_prove(args: impl Iterator<Item = String>) -> Result<String, EggbauError> {
    let options = parse_prove_options(args)?;
    let proof_targets = to_proof_targets(&options.targets);
    let input = read_mm0(&options.input)?;
    let result = crate::prove_targets_with_auf_format(
        &input,
        &proof_targets,
        OutputMode::Fragment,
        options.format,
    )?;

    let mut output = result.auf;
    let mut diagnostics = result.diagnostics;
    if let Some(base) = &options.base {
        let env = mm0::parse_env(&input)?;
        let public_targets = public_target_names(&proof_targets)?;
        let base_text = read_base_text(base)?;
        let spliced = splice_public_theorem_blocks(&env, &base_text, &output, &public_targets)?;
        output = spliced.text;
        diagnostics.retain(|diagnostic| !is_stream_order_diagnostic(diagnostic));
        diagnostics.extend(spliced.diagnostics);
    }

    emit_cli_diagnostics(&diagnostics);
    write_or_return(options.out.as_deref(), output)
}

fn run_script(mut args: impl Iterator<Item = String>) -> Result<String, EggbauError> {
    match args.next().as_deref() {
        Some("emit") => run_script_emit(args),
        Some("check") => run_script_check(args),
        Some("prove") => run_script_prove(args),
        Some(other) => Err(EggbauError::UnsupportedCommand(format!("script {other}"))),
        None => Err(EggbauError::UnsupportedCommand(
            "script requires a subcommand: emit, prove, or check".to_owned(),
        )),
    }
}

fn run_script_emit(args: impl Iterator<Item = String>) -> Result<String, EggbauError> {
    let options = parse_script_emit_options(args)?;
    let input = read_mm0(&options.input)?;
    let env = mm0::parse_env(&input)?;
    let export_env = export::ExportEnv::from_mm0(&env)?;

    if let Some(theorem) = options.theorem {
        return crate::egg::render_theorem_script(&env, &export_env, &theorem);
    }

    let body = if options.scheduled {
        export::render_egglog_with_schedule(&export_env)
    } else {
        export::render_egglog(&export_env)
    };
    Ok(render_script_emit_header(&options.input, None, "environment") + &body)
}

#[derive(Clone, Debug)]
struct ScriptEmitOptions {
    input: String,
    theorem: Option<String>,
    scheduled: bool,
}

fn parse_script_emit_options(
    mut args: impl Iterator<Item = String>,
) -> Result<ScriptEmitOptions, EggbauError> {
    let input = args.next().ok_or_else(|| {
        EggbauError::UnsupportedCommand("script emit requires an MM0 input path".to_owned())
    })?;
    let mut theorem = None;
    let mut scheduled = false;

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--scheduled" => scheduled = true,
            "--theorem" | "-t" => {
                let value = args.next().ok_or_else(|| {
                    EggbauError::UnsupportedCommand(
                        "script emit --theorem requires a theorem name".to_owned(),
                    )
                })?;
                if theorem.replace(value).is_some() {
                    return Err(EggbauError::UnsupportedCommand(
                        "script emit --theorem may only be supplied once".to_owned(),
                    ));
                }
            }
            other => return Err(EggbauError::UnsupportedCommand(other.to_owned())),
        }
    }

    Ok(ScriptEmitOptions {
        input,
        theorem,
        scheduled,
    })
}

fn render_script_emit_header(input: &str, theorem: Option<&str>, kind: &str) -> String {
    let mut out = String::new();
    out.push_str(&format!(
        ";; generated by eggbau {}\n",
        env!("CARGO_PKG_VERSION")
    ));
    out.push_str(&format!(";; input: {input}\n"));
    if let Some(theorem) = theorem {
        out.push_str(&format!(";; theorem: {theorem}\n"));
    }
    out.push_str(&format!(";; script kind: {kind}\n"));
    out.push_str(";; rule names are part of the reconstruction interface\n\n");
    out
}

fn run_script_check(args: impl Iterator<Item = String>) -> Result<String, EggbauError> {
    let options = parse_script_check_options(args)?;
    let input = read_mm0(&options.input)?;
    let script = read_script_text(&options.script)?;
    let env = mm0::parse_env(&input)?;
    let export_env = export::ExportEnv::from_mm0(&env)?;
    let proof = crate::egg::check_theorem_script(&env, &export_env, &options.theorem, &script)?;
    Ok(serde_json::to_string_pretty(&proof).expect("proof JSON should render") + "\n")
}

fn run_script_prove(args: impl Iterator<Item = String>) -> Result<String, EggbauError> {
    let options = parse_script_prove_options(args)?;
    let input = read_mm0(&options.input)?;
    let script = read_script_text(&options.script)?;
    let env = mm0::parse_env(&input)?;
    let export_env = export::ExportEnv::from_mm0(&env)?;
    let proof = crate::egg::check_theorem_script(&env, &export_env, &options.theorem, &script)?;
    let certificate = proof.certificate.ok_or_else(|| {
        EggbauError::Egglog("script proof did not produce a certificate".to_owned())
    })?;
    let certificate = if options.format.compact_enabled() {
        crate::cert::compact_certificate_for_theorem(
            &certificate,
            &env,
            &export_env,
            &options.theorem,
        )?
        .0
    } else {
        certificate
    };
    let rendered = crate::auf::render_certificate(
        &env,
        &export_env,
        &options.theorem,
        &certificate,
        crate::auf::AufRenderOptions {
            output_mode: OutputMode::Fragment,
            format: options.format,
        },
    )?;
    write_or_return(options.out.as_deref(), rendered.text)
}

#[derive(Clone, Debug)]
struct ScriptCheckOptions {
    input: String,
    theorem: String,
    script: String,
}

#[derive(Clone, Debug)]
struct ScriptProveOptions {
    input: String,
    theorem: String,
    script: String,
    out: Option<String>,
    format: AufRenderFormat,
}

fn parse_script_check_options(
    mut args: impl Iterator<Item = String>,
) -> Result<ScriptCheckOptions, EggbauError> {
    let input = args.next().ok_or_else(|| {
        EggbauError::UnsupportedCommand("script check requires an MM0 input path".to_owned())
    })?;
    let mut theorem = None;
    let mut script = None;

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--theorem" | "-t" => {
                let value = args.next().ok_or_else(|| {
                    EggbauError::UnsupportedCommand(
                        "script check --theorem requires a theorem name".to_owned(),
                    )
                })?;
                if theorem.replace(value).is_some() {
                    return Err(EggbauError::UnsupportedCommand(
                        "script check --theorem may only be supplied once".to_owned(),
                    ));
                }
            }
            "--script" => {
                let value = args.next().ok_or_else(|| {
                    EggbauError::UnsupportedCommand(
                        "script check --script requires a file path".to_owned(),
                    )
                })?;
                if script.replace(value).is_some() {
                    return Err(EggbauError::UnsupportedCommand(
                        "script check --script may only be supplied once".to_owned(),
                    ));
                }
            }
            other => return Err(EggbauError::UnsupportedCommand(other.to_owned())),
        }
    }

    let theorem = theorem.ok_or_else(|| {
        EggbauError::UnsupportedCommand("script check --theorem is required".to_owned())
    })?;
    let script = script.ok_or_else(|| {
        EggbauError::UnsupportedCommand("script check --script is required".to_owned())
    })?;

    Ok(ScriptCheckOptions {
        input,
        theorem,
        script,
    })
}

fn parse_script_prove_options(
    mut args: impl Iterator<Item = String>,
) -> Result<ScriptProveOptions, EggbauError> {
    let input = args.next().ok_or_else(|| {
        EggbauError::UnsupportedCommand("script prove requires an MM0 input path".to_owned())
    })?;
    let mut theorem = None;
    let mut script = None;
    let mut out = None;
    let mut format = AufRenderFormat::explicit();

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--theorem" | "-t" => {
                let value = args.next().ok_or_else(|| {
                    EggbauError::UnsupportedCommand(
                        "script prove --theorem requires a theorem name".to_owned(),
                    )
                })?;
                if theorem.replace(value).is_some() {
                    return Err(EggbauError::UnsupportedCommand(
                        "script prove --theorem may only be supplied once".to_owned(),
                    ));
                }
            }
            "--script" => {
                let value = args.next().ok_or_else(|| {
                    EggbauError::UnsupportedCommand(
                        "script prove --script requires a file path".to_owned(),
                    )
                })?;
                if script.replace(value).is_some() {
                    return Err(EggbauError::UnsupportedCommand(
                        "script prove --script may only be supplied once".to_owned(),
                    ));
                }
            }
            "--out" | "-o" => {
                let value = args.next().ok_or_else(|| {
                    EggbauError::UnsupportedCommand(
                        "script prove --out requires a file path".to_owned(),
                    )
                })?;
                if out.replace(value).is_some() {
                    return Err(EggbauError::UnsupportedCommand(
                        "script prove --out may only be supplied once".to_owned(),
                    ));
                }
            }
            "--format" | "--proof-style" => {
                let value = args.next().ok_or_else(|| {
                    EggbauError::UnsupportedCommand(
                        "script prove --format requires explicit, implicit, compact, \
                         nocompact, kernel, or notation"
                            .to_owned(),
                    )
                })?;
                format = apply_auf_format_value(format, &value)?;
            }
            other => return Err(EggbauError::UnsupportedCommand(other.to_owned())),
        }
    }

    let theorem = theorem.ok_or_else(|| {
        EggbauError::UnsupportedCommand("script prove --theorem is required".to_owned())
    })?;
    let script = script.ok_or_else(|| {
        EggbauError::UnsupportedCommand("script prove --script is required".to_owned())
    })?;

    Ok(ScriptProveOptions {
        input,
        theorem,
        script,
        out,
        format,
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TargetSpec {
    Theorem { name: String },
    Lemma { name: String, header: String },
}

impl TargetSpec {
    pub fn name(&self) -> &str {
        match self {
            Self::Theorem { name } | Self::Lemma { name, .. } => name,
        }
    }

    pub fn theorem(name: impl Into<String>) -> Self {
        Self::Theorem { name: name.into() }
    }

    pub fn lemma(header: impl Into<String>) -> Result<Self, EggbauError> {
        let header = header.into();
        parse_lemma_target(&header, "lemma target")
    }
}

#[derive(Clone, Debug)]
struct ProveOptions {
    input: String,
    targets: Vec<TargetSpec>,
    out: Option<String>,
    base: Option<String>,
    format: AufRenderFormat,
}

fn parse_prove_options(
    mut args: impl Iterator<Item = String>,
) -> Result<ProveOptions, EggbauError> {
    let input = args.next().ok_or_else(|| {
        EggbauError::UnsupportedCommand("prove requires an MM0 input path".to_owned())
    })?;
    let mut targets = Vec::new();
    let mut out = None;
    let mut base = None;
    let mut format = AufRenderFormat::explicit();

    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--theorem" | "-t" => {
                let value = args.next().ok_or_else(|| {
                    EggbauError::UnsupportedCommand("--theorem requires a theorem name".to_owned())
                })?;
                targets.push(parse_theorem_target(&value, "command line --theorem")?);
            }
            "--lemma" => {
                let value = args.next().ok_or_else(|| {
                    EggbauError::UnsupportedCommand("--lemma requires a lemma header".to_owned())
                })?;
                targets.push(parse_lemma_target(&value, "command line --lemma")?);
            }
            "--targets" => {
                let value = args.next().ok_or_else(|| {
                    EggbauError::UnsupportedCommand("--targets requires a file path".to_owned())
                })?;
                let text = read_targets_text(&value)?;
                targets.extend(parse_target_lines(&value, &text)?);
            }
            "--out" | "-o" => {
                let value = args.next().ok_or_else(|| {
                    EggbauError::UnsupportedCommand("--out requires a file path".to_owned())
                })?;
                if out.replace(value).is_some() {
                    return Err(EggbauError::UnsupportedCommand(
                        "--out may only be supplied once".to_owned(),
                    ));
                }
            }
            "--format" | "--proof-style" => {
                let value = args.next().ok_or_else(|| {
                    EggbauError::UnsupportedCommand(
                        "--format requires explicit, implicit, compact, nocompact, \
                         kernel, or notation"
                            .to_owned(),
                    )
                })?;
                format = apply_auf_format_value(format, &value)?;
            }
            "--base" => {
                let value = args.next().ok_or_else(|| {
                    EggbauError::UnsupportedCommand("--base requires a file path".to_owned())
                })?;
                if base.replace(value).is_some() {
                    return Err(EggbauError::UnsupportedCommand(
                        "--base may only be supplied once".to_owned(),
                    ));
                }
            }
            other => return Err(EggbauError::UnsupportedCommand(other.to_owned())),
        }
    }

    validate_unique_targets(&targets)?;
    if targets.is_empty() {
        return Err(EggbauError::UnsupportedCommand(
            "at least one proof target is required".to_owned(),
        ));
    }

    Ok(ProveOptions {
        input,
        targets,
        out,
        base,
        format,
    })
}

fn to_proof_targets(targets: &[TargetSpec]) -> Vec<ProofTarget> {
    targets
        .iter()
        .map(|target| match target {
            TargetSpec::Theorem { name } => ProofTarget::PublicTheorem { name: name.clone() },
            TargetSpec::Lemma { name, header } => ProofTarget::LocalLemma {
                name: name.clone(),
                header: header.clone(),
            },
        })
        .collect()
}

fn public_target_names(targets: &[ProofTarget]) -> Result<Vec<String>, EggbauError> {
    targets
        .iter()
        .map(|target| match target {
            ProofTarget::PublicTheorem { name } => Ok(name.clone()),
            ProofTarget::LocalLemma { name, .. } => Err(EggbauError::UnsupportedCommand(format!(
                "--base currently supports only public theorem targets; \
                 local lemma `{name}` cannot be spliced safely yet"
            ))),
        })
        .collect()
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SpliceResult {
    text: String,
    diagnostics: Vec<crate::Diagnostic>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum AufItem {
    Text(String),
    PublicBlock { name: String, text: String },
    OtherBlock(String),
}

impl AufItem {
    fn text(&self) -> &str {
        match self {
            Self::Text(text) | Self::PublicBlock { text, .. } | Self::OtherBlock(text) => text,
        }
    }
}

fn splice_public_theorem_blocks(
    env: &mm0::Mm0Env,
    base_text: &str,
    generated_text: &str,
    targets: &[String],
) -> Result<SpliceResult, EggbauError> {
    let mut base_items = parse_auf_items(env, base_text)?;
    let generated_items = parse_auf_items(env, generated_text)?;
    let generated_blocks = generated_public_blocks(generated_items, targets)?;

    for target in targets {
        let block = generated_blocks.get(target).ok_or_else(|| {
            EggbauError::UnsupportedCommand(format!(
                "base splicing could not find generated block for `{target}`"
            ))
        })?;
        splice_one_public_block(env, &mut base_items, target, block)?;
    }

    let text = render_auf_items(&base_items);
    let present = public_block_names(&base_items).collect::<HashSet<_>>();
    let diagnostics = final_stream_order_diagnostics(env, &present);
    Ok(SpliceResult { text, diagnostics })
}

fn generated_public_blocks(
    items: Vec<AufItem>,
    targets: &[String],
) -> Result<HashMap<String, String>, EggbauError> {
    let target_set = targets.iter().map(String::as_str).collect::<HashSet<_>>();
    let mut blocks = HashMap::new();
    for item in items {
        match item {
            AufItem::PublicBlock { name, text } if target_set.contains(name.as_str()) => {
                blocks.insert(name, normalize_block_text(&text));
            }
            AufItem::PublicBlock { name, .. } => {
                return Err(EggbauError::UnsupportedCommand(format!(
                    "base splicing generated an unexpected public block `{name}`"
                )));
            }
            AufItem::Text(text) if text.trim().is_empty() => {}
            AufItem::Text(_) | AufItem::OtherBlock(_) => {
                return Err(EggbauError::UnsupportedCommand(
                    "base splicing generated non-public blocks; this is not supported yet"
                        .to_owned(),
                ));
            }
        }
    }
    Ok(blocks)
}

fn splice_one_public_block(
    env: &mm0::Mm0Env,
    items: &mut Vec<AufItem>,
    target: &str,
    block: &str,
) -> Result<(), EggbauError> {
    if let Some(pos) = items.iter().position(|item| {
        matches!(
            item,
            AufItem::PublicBlock { name, .. } if name == target
        )
    }) {
        items[pos] = AufItem::PublicBlock {
            name: target.to_owned(),
            text: block.to_owned(),
        };
        return Ok(());
    }

    let target_order = public_theorem_order(env, target)?;
    let later_public_pos = items.iter().position(|item| match item {
        AufItem::PublicBlock { name, .. } => public_theorem_order(env, name)
            .map(|order| order > target_order)
            .unwrap_or(false),
        _ => false,
    });
    let insert_pos = later_public_pos
        .map(|pos| insertion_before_leading_gap(items, pos))
        .unwrap_or(items.len());
    items.insert(
        insert_pos,
        AufItem::PublicBlock {
            name: target.to_owned(),
            text: block.to_owned(),
        },
    );
    Ok(())
}

fn parse_auf_items(env: &mm0::Mm0Env, text: &str) -> Result<Vec<AufItem>, EggbauError> {
    let lines = split_preserved_lines(text);
    let mut items = Vec::new();
    let mut text_buf = String::new();
    let mut seen_public = HashSet::new();
    let mut last_public_order = None;
    let mut index = 0;

    while index < lines.len() {
        if is_auf_block_start(&lines, index) {
            flush_text_item(&mut items, &mut text_buf);
            let next = find_next_auf_block_start(&lines, index + 2);
            let mut block_end = next.unwrap_or(lines.len());
            while block_end > index + 2 && is_detached_gap_line(&lines[block_end - 1]) {
                block_end -= 1;
            }

            let header = line_body(&lines[index]).trim().to_owned();
            let block_text = join_lines(&lines[index..block_end]);
            push_auf_block(
                env,
                &mut items,
                &mut seen_public,
                &mut last_public_order,
                &header,
                block_text,
            )?;
            text_buf.push_str(&join_lines(&lines[block_end..next.unwrap_or(lines.len())]));
            index = next.unwrap_or(lines.len());
        } else {
            reject_malformed_public_header(env, &lines, index)?;
            text_buf.push_str(&lines[index]);
            index += 1;
        }
    }
    flush_text_item(&mut items, &mut text_buf);
    Ok(items)
}

fn push_auf_block(
    env: &mm0::Mm0Env,
    items: &mut Vec<AufItem>,
    seen_public: &mut HashSet<String>,
    last_public_order: &mut Option<(usize, String)>,
    header: &str,
    block_text: String,
) -> Result<(), EggbauError> {
    if let Some(order) = maybe_public_theorem_order(env, header) {
        if !seen_public.insert(header.to_owned()) {
            return Err(EggbauError::UnsupportedCommand(format!(
                "base .auf has duplicate public theorem block `{header}`"
            )));
        }
        if let Some((previous_order, previous_name)) = last_public_order.as_ref()
            && *previous_order > order
        {
            return Err(EggbauError::UnsupportedCommand(format!(
                "base theorem blocks contradict MM0 declaration order: \
                 `{previous_name}` appears before `{header}`"
            )));
        }
        *last_public_order = Some((order, header.to_owned()));
        items.push(AufItem::PublicBlock {
            name: header.to_owned(),
            text: normalize_block_text(&block_text),
        });
        return Ok(());
    }

    if is_simple_ident(header) {
        return Err(EggbauError::UnsupportedCommand(format!(
            "base .auf contains unknown public theorem block `{header}`"
        )));
    }

    items.push(AufItem::OtherBlock(normalize_block_text(&block_text)));
    Ok(())
}

fn reject_malformed_public_header(
    env: &mm0::Mm0Env,
    lines: &[String],
    index: usize,
) -> Result<(), EggbauError> {
    let header = line_body(&lines[index]).trim();
    if maybe_public_theorem_order(env, header).is_some() {
        return Err(EggbauError::UnsupportedCommand(format!(
            "base .auf parse error: public theorem block `{header}` is \
             missing its dashed underline"
        )));
    }
    Ok(())
}

fn split_preserved_lines(text: &str) -> Vec<String> {
    if text.is_empty() {
        return Vec::new();
    }
    text.split_inclusive('\n').map(str::to_owned).collect()
}

fn find_next_auf_block_start(lines: &[String], start: usize) -> Option<usize> {
    (start..lines.len()).find(|&index| is_auf_block_start(lines, index))
}

fn is_auf_block_start(lines: &[String], index: usize) -> bool {
    let Some(header) = lines.get(index).map(|line| line_body(line).trim()) else {
        return false;
    };
    if header.is_empty() || header.starts_with("--") {
        return false;
    }
    lines
        .get(index + 1)
        .map(|line| is_dash_line(line_body(line).trim()))
        .unwrap_or(false)
}

fn is_dash_line(line: &str) -> bool {
    line.len() >= 3 && line.chars().all(|ch| ch == '-')
}

fn is_detached_gap_line(line: &str) -> bool {
    let trimmed = line_body(line).trim();
    trimmed.is_empty() || trimmed.starts_with("--")
}

fn insertion_before_leading_gap(items: &[AufItem], mut pos: usize) -> usize {
    while pos > 0 {
        match &items[pos - 1] {
            AufItem::Text(text) if is_detached_gap_text(text) => pos -= 1,
            _ => break,
        }
    }
    pos
}

fn is_detached_gap_text(text: &str) -> bool {
    text.lines().all(|line| {
        let trimmed = line.trim();
        trimmed.is_empty() || trimmed.starts_with("--")
    })
}

fn line_body(line: &str) -> &str {
    line.trim_end_matches(['\r', '\n'])
}

fn join_lines(lines: &[String]) -> String {
    lines.concat()
}

fn flush_text_item(items: &mut Vec<AufItem>, text: &mut String) {
    if !text.is_empty() {
        items.push(AufItem::Text(std::mem::take(text)));
    }
}

fn render_auf_items(items: &[AufItem]) -> String {
    let mut out = String::new();
    for item in items {
        if matches!(item, AufItem::PublicBlock { .. } | AufItem::OtherBlock(_)) {
            ensure_block_boundary_before(&mut out);
            out.push_str(item.text());
            ensure_block_boundary_after(&mut out);
        } else {
            out.push_str(item.text());
        }
    }
    out
}

fn ensure_block_boundary_before(out: &mut String) {
    if !out.is_empty() && !out.ends_with("\n\n") {
        if !out.ends_with('\n') {
            out.push('\n');
        }
        out.push('\n');
    }
}

fn ensure_block_boundary_after(out: &mut String) {
    if !out.ends_with('\n') {
        out.push('\n');
    }
}

fn normalize_block_text(text: &str) -> String {
    let mut normalized = text.trim_end_matches(['\r', '\n']).to_owned();
    normalized.push('\n');
    normalized
}

fn public_block_names(items: &[AufItem]) -> impl Iterator<Item = String> + '_ {
    items.iter().filter_map(|item| match item {
        AufItem::PublicBlock { name, .. } => Some(name.clone()),
        AufItem::Text(_) | AufItem::OtherBlock(_) => None,
    })
}

fn final_stream_order_diagnostics(
    env: &mm0::Mm0Env,
    present: &HashSet<String>,
) -> Vec<crate::Diagnostic> {
    let mut missing_earlier = Vec::new();
    for decl in &env.theorems {
        if decl.kind != mm0::AssertionKind::Theorem {
            continue;
        }
        if present.contains(&decl.name) {
            if !missing_earlier.is_empty() {
                return vec![crate::Diagnostic {
                    severity: crate::DiagnosticSeverity::Warning,
                    message: format!(
                        "emitted `{}` before earlier public obligations: {}\n\n\
                         The generated .auf may be useful for LSP or manual \
                         splicing, but may not compile as a standalone stream \
                         with `abc compile`.",
                        decl.name,
                        missing_earlier.join(", ")
                    ),
                }];
            }
        } else {
            missing_earlier.push(decl.name.clone());
        }
    }
    Vec::new()
}

fn maybe_public_theorem_order(env: &mm0::Mm0Env, name: &str) -> Option<usize> {
    env.theorems
        .iter()
        .filter(|decl| decl.kind == mm0::AssertionKind::Theorem)
        .position(|decl| decl.name == name)
}

fn public_theorem_order(env: &mm0::Mm0Env, name: &str) -> Result<usize, EggbauError> {
    maybe_public_theorem_order(env, name).ok_or_else(|| {
        EggbauError::UnsupportedCommand(format!(
            "unknown public theorem block `{name}` during base splicing"
        ))
    })
}

fn is_stream_order_diagnostic(diagnostic: &crate::Diagnostic) -> bool {
    diagnostic.severity == crate::DiagnosticSeverity::Warning
        && diagnostic.message.contains("earlier public obligations")
        && diagnostic.message.contains("standalone stream")
}

fn emit_cli_diagnostics(diagnostics: &[crate::Diagnostic]) {
    for diagnostic in diagnostics {
        if diagnostic.severity == crate::DiagnosticSeverity::Warning {
            eprintln!("warning: {}", diagnostic.message);
        }
    }
}

fn validate_unique_targets(targets: &[TargetSpec]) -> Result<(), EggbauError> {
    let mut seen = HashSet::new();
    for target in targets {
        let name = target.name();
        if !seen.insert(name.to_owned()) {
            return Err(EggbauError::UnsupportedCommand(format!(
                "duplicate proof target: {name}"
            )));
        }
    }
    Ok(())
}

pub fn parse_target_lines(source: &str, text: &str) -> Result<Vec<TargetSpec>, EggbauError> {
    let mut targets = Vec::new();
    for (idx, line) in text.lines().enumerate() {
        if let Some(target) = parse_target_line(source, idx + 1, line)? {
            targets.push(target);
        }
    }
    validate_unique_targets(&targets)?;
    Ok(targets)
}

fn parse_target_line(
    source: &str,
    line_number: usize,
    line: &str,
) -> Result<Option<TargetSpec>, EggbauError> {
    let line = line.trim();
    if line.is_empty() || line.starts_with("--") {
        return Ok(None);
    }

    if let Some(rest) = line.strip_prefix("theorem ") {
        return parse_theorem_target(rest, &format!("{source}:{line_number}")).map(Some);
    }
    if line == "theorem" {
        return Err(malformed_target_line(source, line_number));
    }

    if let Some(rest) = line.strip_prefix("lemma ") {
        return parse_lemma_target(rest, &format!("{source}:{line_number}")).map(Some);
    }
    if line == "lemma" {
        return Err(malformed_target_line(source, line_number));
    }

    Err(malformed_target_line(source, line_number))
}

fn parse_theorem_target(value: &str, source: &str) -> Result<TargetSpec, EggbauError> {
    let name = value.trim();
    if name.split_whitespace().count() != 1 || !is_simple_ident(name) {
        return Err(EggbauError::UnsupportedCommand(format!(
            "invalid theorem target name in {source}: {name}"
        )));
    }
    Ok(TargetSpec::Theorem {
        name: name.to_owned(),
    })
}

fn parse_lemma_target(value: &str, source: &str) -> Result<TargetSpec, EggbauError> {
    let header = value.trim();
    if header.is_empty() || !header.contains(':') {
        return Err(EggbauError::UnsupportedCommand(format!(
            "malformed lemma target in {source}: expected lemma HEADER"
        )));
    }

    let name_end = header
        .char_indices()
        .find(|(_, ch)| ch.is_whitespace() || *ch == '(' || *ch == '{' || *ch == ':')
        .map_or(header.len(), |(idx, _)| idx);
    let name = header[..name_end].trim();
    if !is_simple_ident(name) {
        return Err(EggbauError::UnsupportedCommand(format!(
            "invalid lemma target name in {source}: {name}"
        )));
    }

    Ok(TargetSpec::Lemma {
        name: name.to_owned(),
        header: header.to_owned(),
    })
}

fn malformed_target_line(source: &str, line_number: usize) -> EggbauError {
    EggbauError::UnsupportedCommand(format!(
        "malformed target line {source}:{line_number}: expected `theorem NAME` or `lemma HEADER`"
    ))
}

fn is_simple_ident(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !(first == '_' || first.is_ascii_alphabetic()) {
        return false;
    }
    if name == "_" {
        return false;
    }
    chars.all(|ch| ch == '_' || ch.is_ascii_alphanumeric())
}

fn read_targets_text(path: &str) -> Result<String, EggbauError> {
    read_stdin_or_file(path)
}

fn read_script_text(path: &str) -> Result<String, EggbauError> {
    read_stdin_or_file(path)
}

fn read_base_text(path: &str) -> Result<String, EggbauError> {
    std::fs::read_to_string(path).map_err(|source| EggbauError::ReadFile {
        path: path.to_owned(),
        source,
    })
}

fn read_stdin_or_file(path: &str) -> Result<String, EggbauError> {
    if path == "-" {
        let mut text = String::new();
        std::io::stdin()
            .read_to_string(&mut text)
            .map_err(|source| EggbauError::ReadFile {
                path: "<stdin>".to_owned(),
                source,
            })?;
        return Ok(text);
    }

    std::fs::read_to_string(path).map_err(|source| EggbauError::ReadFile {
        path: path.to_owned(),
        source,
    })
}

fn apply_auf_format_value(
    mut format: AufRenderFormat,
    value: &str,
) -> Result<AufRenderFormat, EggbauError> {
    match value {
        "explicit" => format.explicitness = AufRenderExplicitness::Explicit,
        "implicit" => format.explicitness = AufRenderExplicitness::Implicit,
        "compact" => format.compaction = AufRenderCompaction::Compact,
        "nocompact" | "no-compact" => {
            format.compaction = AufRenderCompaction::NoCompact;
        }
        "kernel" => format.math = AufMathFormat::Kernel,
        "notation" => format.math = AufMathFormat::Notation,
        other => {
            return Err(EggbauError::UnsupportedCommand(format!(
                "unknown Aufbau output format: {other}"
            )));
        }
    }
    Ok(format)
}

fn reject_extra_args(mut args: impl Iterator<Item = String>) -> Result<(), EggbauError> {
    if let Some(extra) = args.next() {
        return Err(EggbauError::UnsupportedCommand(extra));
    }
    Ok(())
}

fn read_mm0(file: &str) -> Result<String, EggbauError> {
    std::fs::read_to_string(file).map_err(|source| EggbauError::ReadFile {
        path: file.to_owned(),
        source,
    })
}

fn write_or_return(out: Option<&str>, text: String) -> Result<String, EggbauError> {
    if let Some(path) = out {
        std::fs::write(path, text).map_err(|source| EggbauError::WriteFile {
            path: path.to_owned(),
            source,
        })?;
        Ok(String::new())
    } else {
        Ok(text)
    }
}

pub fn help_text() -> String {
    [
        "eggbau - untrusted MM0/Aufbau proof search",
        "",
        "USAGE:",
        "  eggbau --version",
        "  eggbau discover INPUT.mm0 [--suggest-annotations]",
        "  eggbau list INPUT.mm0",
        "  eggbau lint INPUT.mm0",
        "  eggbau prove INPUT.mm0 [OPTIONS]",
        "  eggbau script emit INPUT.mm0 [OPTIONS]",
        "  eggbau script prove INPUT.mm0 [OPTIONS]",
        "  eggbau script check INPUT.mm0 [OPTIONS]",
        "",
        "PROVE TARGETS:",
        "  -t, --theorem NAME       Prove a public theorem from INPUT.mm0",
        "      --lemma HEADER       Prove and emit a proof-local Aufbau lemma",
        "      --targets FILE       Read theorem/lemma targets, one per line",
        "",
        "PROVE OUTPUT:",
        "  -o, --out FILE           Write generated .auf to FILE",
        "      --base FILE          Splice generated proofs into an existing .auf",
        "      --format FORMAT      explicit, implicit, compact, nocompact, kernel, notation",
        "",
        "If --out is omitted, generated .auf is written to stdout.",
        "Diagnostics and stream-order warnings are written to stderr.",
    ]
    .join("\n")
        + "\n"
}
