use std::path::Path;

/// Stage-0 discovery deliberately authorizes nothing.
///
/// Later stages will parse MM0 and suggest `@saturation` annotations.  For now
/// this deterministic output gives the snapshot harness something meaningful to
/// compare without implying any theorem has been exported to egglog.
pub fn render_empty_discovery(path: &Path, _mm0: &str) -> String {
    format!(
        "discovery report\ninput: {}\n\npossible saturation conversions:\n\
         possible saturation horn rules:\npossible congruences:\n",
        path.display()
    )
}
