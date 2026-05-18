use std::path::Path;

use crate::{EggbauError, discover, version_report};

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
        Some("discover") => {
            let file = args.next().ok_or_else(|| {
                EggbauError::UnsupportedCommand("discover requires an MM0 input path".to_owned())
            })?;
            let mm0 = std::fs::read_to_string(&file).map_err(|source| EggbauError::ReadFile {
                path: file.clone(),
                source,
            })?;
            Ok(discover::render_empty_discovery(Path::new(&file), &mm0))
        }
        Some(other) => Err(EggbauError::UnsupportedCommand(other.to_owned())),
    }
}

pub fn help_text() -> String {
    [
        "eggbau - untrusted MM0/Aufbau proof-search tooling",
        "",
        "USAGE:",
        "  eggbau --version",
        "  eggbau discover FILE.mm0",
        "",
        "Stage 0 provides the crate skeleton and deterministic fixtures.",
    ]
    .join("\n")
        + "\n"
}
