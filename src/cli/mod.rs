use std::path::Path;

use crate::{EggbauConfig, EggbauError, OutputMode, discover, export, mm0, version_report};

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
        Some("dump-env") => run_dump_env(args),
        Some("emit-egglog") => run_emit_egglog(args),
        Some("prove-egglog") => run_prove_egglog(args),
        Some("emit-auf") => run_emit_auf(args),
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

fn run_dump_env(mut args: impl Iterator<Item = String>) -> Result<String, EggbauError> {
    let file = args.next().ok_or_else(|| {
        EggbauError::UnsupportedCommand("dump-env requires an MM0 input path".to_owned())
    })?;
    let mut theorem = None;
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--theorem" => {
                theorem = Some(args.next().ok_or_else(|| {
                    EggbauError::UnsupportedCommand("--theorem requires a theorem name".to_owned())
                })?);
            }
            other => return Err(EggbauError::UnsupportedCommand(other.to_owned())),
        }
    }

    let input = read_mm0(&file)?;
    let env = mm0::parse_env(&input)?;
    let json = if let Some(name) = theorem {
        let theorem = env
            .theorem(&name)
            .ok_or_else(|| EggbauError::UnsupportedCommand(format!("unknown theorem: {name}")))?;
        serde_json::to_string_pretty(theorem).expect("theorem JSON should render")
    } else {
        serde_json::to_string_pretty(&env).expect("environment JSON should render")
    };

    Ok(json + "\n")
}

fn run_emit_egglog(mut args: impl Iterator<Item = String>) -> Result<String, EggbauError> {
    let file = args.next().ok_or_else(|| {
        EggbauError::UnsupportedCommand("emit-egglog requires an MM0 input path".to_owned())
    })?;
    let mut scheduled = false;
    for arg in args {
        match arg.as_str() {
            "--scheduled" => scheduled = true,
            other => return Err(EggbauError::UnsupportedCommand(other.to_owned())),
        }
    }

    let input = read_mm0(&file)?;
    let env = mm0::parse_env(&input)?;
    let export_env = export::ExportEnv::from_mm0(&env)?;
    if scheduled {
        Ok(export::render_egglog_with_schedule(&export_env))
    } else {
        Ok(export::render_egglog(&export_env))
    }
}

fn run_prove_egglog(mut args: impl Iterator<Item = String>) -> Result<String, EggbauError> {
    let file = args.next().ok_or_else(|| {
        EggbauError::UnsupportedCommand("prove-egglog requires an MM0 input path".to_owned())
    })?;
    let theorem = parse_required_theorem(&mut args)?;
    if let Some(extra) = args.next() {
        return Err(EggbauError::UnsupportedCommand(extra));
    }

    let input = read_mm0(&file)?;
    let env = mm0::parse_env(&input)?;
    let export_env = export::ExportEnv::from_mm0(&env)?;
    let proof = crate::egg::prove_theorem(&env, &export_env, &theorem)?;
    Ok(serde_json::to_string_pretty(&proof).expect("proof JSON should render") + "\n")
}

fn run_emit_auf(mut args: impl Iterator<Item = String>) -> Result<String, EggbauError> {
    let file = args.next().ok_or_else(|| {
        EggbauError::UnsupportedCommand("emit-auf requires an MM0 input path".to_owned())
    })?;
    let theorem = parse_required_theorem(&mut args)?;
    if let Some(extra) = args.next() {
        return Err(EggbauError::UnsupportedCommand(extra));
    }

    let input = read_mm0(&file)?;
    let result = crate::prove_theorem(
        &input,
        EggbauConfig {
            theorem: Some(theorem),
            output_mode: OutputMode::Fragment,
            allow_synthetic_discovery: false,
        },
    )?;
    Ok(result.auf)
}

fn parse_required_theorem(args: &mut impl Iterator<Item = String>) -> Result<String, EggbauError> {
    match args.next().as_deref() {
        Some("--theorem") => args.next().ok_or_else(|| {
            EggbauError::UnsupportedCommand("--theorem requires a theorem name".to_owned())
        }),
        Some(other) => Err(EggbauError::UnsupportedCommand(other.to_owned())),
        None => Err(EggbauError::UnsupportedCommand(
            "--theorem is required".to_owned(),
        )),
    }
}

fn read_mm0(file: &str) -> Result<String, EggbauError> {
    std::fs::read_to_string(file).map_err(|source| EggbauError::ReadFile {
        path: file.to_owned(),
        source,
    })
}

pub fn help_text() -> String {
    [
        "eggbau - untrusted MM0/Aufbau proof-search tooling",
        "",
        "USAGE:",
        "  eggbau --version",
        "  eggbau discover FILE.mm0 [--suggest-annotations]",
        "  eggbau dump-env FILE.mm0 [--theorem THEOREM]",
        "  eggbau emit-egglog FILE.mm0 [--scheduled]",
        "  eggbau prove-egglog FILE.mm0 --theorem THEOREM",
        "  eggbau emit-auf FILE.mm0 --theorem THEOREM",
        "",
        "Stage 8 can emit an Aufbau proof fragment for one theorem.",
    ]
    .join("\n")
        + "\n"
}
