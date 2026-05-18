use serde::{Deserialize, Serialize};

/// Stable placeholder for the future eggbau certificate IR.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Certificate {
    pub format_version: u32,
    pub steps: Vec<CertificateStep>,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct CertificateStep {
    pub label: String,
    pub rule: String,
}

impl Certificate {
    pub fn empty() -> Self {
        Self {
            format_version: 0,
            steps: Vec::new(),
        }
    }
}
