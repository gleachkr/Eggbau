use serde::{Deserialize, Serialize};

/// Source text wrapper used until the supported-fragment parser exists.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Mm0Source {
    pub text: String,
}

impl Mm0Source {
    pub fn new(text: impl Into<String>) -> Self {
        Self { text: text.into() }
    }
}
