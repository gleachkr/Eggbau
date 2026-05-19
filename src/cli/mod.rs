use std::path::Path;

use crate::{EggbauError, discover, mm0, version_report};

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
        Some(other) => Err(EggbauError::UnsupportedCommand(other.to_owned())),
    }
}

fn run_discover(mut args: impl Iterator<Item = String>) -> Result<String, EggbauError> {
    let file = args.next().ok_or_else(|| {
        EggbauError::UnsupportedCommand("discover requires an MM0 input path".to_owned())
    })?;
    let mm0 = read_mm0(&file)?;

    Ok(discover::render_empty_discovery(Path::new(&file), &mm0))
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
        "  eggbau discover FILE.mm0",
        "  eggbau dump-env FILE.mm0 [--theorem THEOREM]",
        "",
        "Stage 1 parses a conservative MM0 declaration subset.",
    ]
    .join("\n")
        + "\n"
}
