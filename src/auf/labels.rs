/// Deterministic label generator for emitted Aufbau proof lines.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LabelGenerator {
    prefix: String,
    next: usize,
}

impl LabelGenerator {
    pub fn new(prefix: impl Into<String>) -> Self {
        Self {
            prefix: prefix.into(),
            next: 0,
        }
    }

    pub fn fresh(&mut self) -> String {
        let label = format!("{}{}", self.prefix, self.next);
        self.next += 1;
        label
    }
}

#[cfg(test)]
mod tests {
    use super::LabelGenerator;

    #[test]
    fn labels_are_deterministic() {
        let mut first = LabelGenerator::new("eggbau_");
        let mut second = LabelGenerator::new("eggbau_");

        let left = (0..4).map(|_| first.fresh()).collect::<Vec<_>>();
        let right = (0..4).map(|_| second.fresh()).collect::<Vec<_>>();

        assert_eq!(left, right);
        assert_eq!(left, ["eggbau_0", "eggbau_1", "eggbau_2", "eggbau_3"]);
    }
}
