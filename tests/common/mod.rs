#![allow(dead_code)]

use std::path::{Path, PathBuf};

pub const THIRD_PARTY_ROOT: &str = "tests/fixtures/third_party_mm0";
pub const THIRD_PARTY_STRESS_ROOT: &str = "tests/fixtures/third_party_mm0/stress";

pub const AUFBAU_PASS_DEF: &str = include_str!("../fixtures/third_party_mm0/aufbau_pass_def.mm0");
pub const AUFBAU_PASS_NORMALIZE_IDENTITY: &str =
    include_str!("../fixtures/third_party_mm0/aufbau_pass_normalize_identity.mm0");
pub const MM0_HELLO: &str = include_str!("../fixtures/third_party_mm0/mm0_hello.mm0");
pub const MM0_PEANO: &str = include_str!("../fixtures/third_party_mm0/mm0_peano.mm0");

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ParseCountExpectation {
    pub sorts: usize,
    pub terms: usize,
    pub theorems: usize,
    pub notations: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct NamedFixture {
    pub name: &'static str,
    pub input: &'static str,
    pub expected: ParseCountExpectation,
}

pub const TOP_LEVEL_THIRD_PARTY_FIXTURES: &[NamedFixture] = &[
    NamedFixture {
        name: "aufbau_pass_def",
        input: AUFBAU_PASS_DEF,
        expected: ParseCountExpectation {
            sorts: 1,
            terms: 2,
            theorems: 2,
            notations: 2,
        },
    },
    NamedFixture {
        name: "aufbau_pass_normalize_identity",
        input: AUFBAU_PASS_NORMALIZE_IDENTITY,
        expected: ParseCountExpectation {
            sorts: 1,
            terms: 6,
            theorems: 9,
            notations: 3,
        },
    },
    NamedFixture {
        name: "mm0_hello",
        input: MM0_HELLO,
        expected: ParseCountExpectation {
            sorts: 3,
            terms: 30,
            theorems: 0,
            notations: 3,
        },
    },
    NamedFixture {
        name: "mm0_peano",
        input: MM0_PEANO,
        expected: ParseCountExpectation {
            sorts: 3,
            terms: 116,
            theorems: 81,
            notations: 57,
        },
    },
];

pub fn stress_fixture_paths() -> Vec<PathBuf> {
    mm0_paths_under(Path::new(THIRD_PARTY_STRESS_ROOT))
}

pub fn all_third_party_fixture_paths() -> Vec<PathBuf> {
    let mut paths = mm0_paths_under(Path::new(THIRD_PARTY_ROOT));
    paths.extend(stress_fixture_paths());
    paths.sort();
    paths
}

fn mm0_paths_under(dir: &Path) -> Vec<PathBuf> {
    let mut paths = std::fs::read_dir(dir)
        .unwrap_or_else(|err| panic!("could not read fixture dir {}: {err}", dir.display()))
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|ext| ext == "mm0"))
        .collect::<Vec<_>>();
    paths.sort();
    paths
}
