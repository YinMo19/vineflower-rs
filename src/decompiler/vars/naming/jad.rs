// SPDX-License-Identifier: Apache-2.0

use rustc_hash::FxHashMap;

#[derive(Clone)]
pub(crate) struct Jad(FxHashMap<String, Series>);

#[derive(Clone)]
struct Series {
    next: usize,
    omit_zero: bool,
    names: Vec<String>,
}

impl Default for Jad {
    fn default() -> Self {
        let seeds: &[(&str, usize, bool, &[&str])] = &[
            ("int", 0, true, &["i", "j", "k", "l"]),
            ("byte", 0, false, &["b"]),
            ("char", 0, false, &["c"]),
            ("short", 1, false, &["short"]),
            ("boolean", 0, true, &["flag"]),
            ("double", 0, false, &["d"]),
            ("float", 0, true, &["f"]),
            ("File", 1, true, &["file"]),
            ("String", 0, true, &["s"]),
            ("Class", 0, true, &["oclass"]),
            ("Long", 0, true, &["olong"]),
            ("Byte", 0, true, &["obyte"]),
            ("Short", 0, true, &["oshort"]),
            ("Boolean", 0, true, &["obool"]),
            ("Package", 0, true, &["opackage"]),
            ("Enum", 0, true, &["oenum"]),
        ];
        Self(
            seeds
                .iter()
                .map(|&(ty, next, omit_zero, names)| {
                    (
                        ty.to_owned(),
                        Series {
                            next,
                            omit_zero,
                            names: names.iter().map(|&name| name.to_owned()).collect(),
                        },
                    )
                })
                .collect(),
        )
    }
}

impl Jad {
    pub(super) fn next(&mut self, ty: &str) -> String {
        fn collapse_arrays(mut name: String) -> String {
            while name.contains("[][]") {
                name = name.replace("[][]", "[]");
            }
            name
        }
        let ty_key = collapse_arrays(ty.to_owned());
        let key = if self.0.contains_key(&ty_key) {
            ty_key
        } else if self.0.contains_key(&ty_key.to_lowercase()) {
            ty_key.to_lowercase()
        } else if ty == "long" {
            "int".to_owned()
        } else if ty.starts_with(|ch: char| ch.is_ascii_uppercase())
            || ty.contains('[')
            || ty.contains("...")
        {
            let key = collapse_arrays(ty.replace("...", "[]")).to_lowercase();
            let mut base = key.replace('.', "");
            if base.contains('[') {
                base = format!("a{}", base.replace("[]", ""));
            }
            self.0.insert(
                key.clone(),
                Series {
                    next: 0,
                    omit_zero: true,
                    names: vec![base],
                },
            );
            key
        } else {
            return ty.to_lowercase();
        };
        let series = self.0.get_mut(&key).unwrap();
        let index = series.next;
        series.next += 1;
        let base = &series.names[index % series.names.len()];
        let round = index / series.names.len();
        if round == 0 && series.omit_zero {
            base.clone()
        } else {
            format!("{base}{round}")
        }
    }
}
