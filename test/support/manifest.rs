// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

pub type Preferences = BTreeMap<&'static str, &'static str>;

#[derive(Clone, Copy, Debug)]
pub struct Version {
    pub name: &'static str,
    pub dir: &'static str,
    pub jdk: Option<&'static str>,
    pub extension: &'static str,
}

impl Version {
    pub fn java8() -> Self {
        Self::parse("JAVA_8")
    }

    fn parse(name: &'static str) -> Self {
        let (dir, jdk) = match name {
            "CUSTOM" => ("custom", None),
            "JAVA_8" => ("java8", Some("8")),
            "JAVA_8_NODEBUG" => ("java8nodebug", Some("8")),
            "JAVA_9" => ("java9", Some("9")),
            "JAVA_11" => ("java11", Some("11")),
            "JAVA_16" => ("java16", Some("16")),
            "JAVA_16_NODEBUG" => ("java16nodebug", Some("16")),
            "JAVA_16_PREVIEW" => ("java16preview", Some("16")),
            "JAVA_17" => ("java17", Some("17")),
            "JAVA_17_PREVIEW" => ("java17preview", Some("17")),
            "JAVA_19_PREVIEW" => ("java19preview", Some("19")),
            "JAVA_21" => ("java21", Some("21")),
            "JAVA_21_PREVIEW" => ("java21preview", Some("21")),
            "JAVA_25" => ("java25", Some("25")),
            "GROOVY" => ("groovy", None),
            "KOTLIN" => ("kt", None),
            "KOTLIN_OLD" => ("ktold", None),
            "SCALA" => ("scala", None),
            "JASM" => ("jasm", None),
            _ => panic!("unknown upstream test version {name}"),
        };
        let extension = if name.starts_with("KOTLIN") {
            "kt"
        } else {
            "java"
        };
        Self {
            name,
            dir,
            jdk,
            extension,
        }
    }
}

pub struct Case {
    pub suite: &'static str,
    pub set: &'static str,
    pub version: Version,
    pub class: &'static str,
    pub output: Option<&'static str>,
    pub alternate: Option<&'static str>,
    pub companions: Vec<&'static str>,
    pub failable: bool,
    pub options: Preferences,
}

impl Case {
    pub fn id(&self) -> String {
        format!(
            "{}/{}/{}/{}",
            self.suite, self.set, self.version.name, self.class
        )
    }

    pub fn golden(&self, data: &Path) -> PathBuf {
        data.join("results").join(format!("{}.dec", self.class))
    }
}

pub struct Manifest {
    pub cases: Vec<Case>,
}

impl Manifest {
    pub fn load() -> Self {
        let mut defaults = None;
        let mut current_set = None;
        let mut cases = Vec::new();
        for line in include_str!("../registrations.tsv").lines() {
            if line.is_empty() || line.starts_with('#') {
                continue;
            }
            let fields: Vec<_> = line.split('\t').collect();
            match fields.as_slice() {
                ["fixture", pairs @ ..] => {
                    assert!(defaults.is_none(), "duplicated fixture defaults");
                    defaults = Some(preferences(pairs));
                }
                ["set", suite, set, pairs @ ..] => {
                    let mut options = defaults.clone().expect("missing fixture defaults");
                    options.extend(preferences(pairs));
                    current_set = Some((*suite, *set, options));
                }
                [
                    "case",
                    version,
                    kind,
                    class,
                    output,
                    alternate,
                    companions @ ..,
                ] => {
                    let (suite, set, options) = current_set.as_ref().expect("case without a set");
                    assert!(matches!(
                        *kind,
                        "register" | "registerRaw" | "registerFailable"
                    ));
                    cases.push(Case {
                        suite,
                        set,
                        version: Version::parse(version),
                        class,
                        output: (*output != "-").then_some(*output),
                        alternate: (*alternate != "-").then_some(*alternate),
                        companions: companions.to_vec(),
                        failable: *kind == "registerFailable",
                        options: options.clone(),
                    });
                }
                _ => panic!("invalid upstream registration: {line}"),
            }
        }
        assert!(defaults.is_some(), "missing fixture defaults");
        Self { cases }
    }
}

fn preferences(pairs: &[&'static str]) -> Preferences {
    let pairs = pairs
        .iter()
        .map(|pair| pair.split_once('=').expect("option without a value"));
    let mut values = Preferences::new();
    for (key, value) in pairs {
        assert!(
            values.insert(key, value).is_none(),
            "duplicate option {key}"
        );
    }
    values
}
