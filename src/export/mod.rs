use serde::{Deserialize, Serialize};

/// Minimal placeholder for a validated export environment.
#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
pub struct ExportEnv {
    pub sorts: Vec<String>,
    pub terms: Vec<String>,
}

pub fn render_empty_egglog(_env: &ExportEnv) -> String {
    String::new()
}
