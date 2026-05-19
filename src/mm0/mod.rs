mod env;
mod parse;

pub use env::*;
pub use parse::{Mm0ParseError, parse_env};

use serde::{Deserialize, Serialize};

/// Source text wrapper used by CLI commands and tests.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
pub struct Mm0Source {
    pub text: String,
}

impl Mm0Source {
    pub fn new(text: impl Into<String>) -> Self {
        Self { text: text.into() }
    }
}
