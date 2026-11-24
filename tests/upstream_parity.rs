// Based on Vineflower's SingleClassesTestBase and DecompilerTestFixture.
// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

#[path = "support/cli.rs"]
mod cli;
#[path = "support/inputs.rs"]
mod inputs;
#[path = "support/manifest.rs"]
mod manifest;

use std::collections::BTreeSet;
use std::fmt::Display;
use std::fs;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::Path;

use vineflower_rs::{DecompileError, OptionError, Options, bytecode, classfile, decompile};

use inputs::{Inputs, fixture_root, require_file, suite_data};
use manifest::{Case, Manifest, Version};

#[derive(Clone, Debug)]
enum Failure {
    MissingJdk(String),
    MissingFixture(String),
    Unsupported(String),
    Mismatch(String),
    Execution(String),
}

impl Failure {
    fn fixture(path: &Path, description: &str) -> Self {
        Self::MissingFixture(format!("{description}: {}", path.display()))
    }

    fn io(path: &Path, error: impl Display) -> Self {
        Self::Execution(format!("{}: {error}", path.display()))
    }

    fn parts(self) -> (usize, String) {
        match self {
            Self::MissingJdk(reason) => (0, reason),
            Self::MissingFixture(reason) => (1, reason),
            Self::Unsupported(reason) => (2, reason),
            Self::Mismatch(reason) => (3, reason),
            Self::Execution(reason) => (4, reason),
        }
    }
}

#[derive(Default)]
struct Report {
    passed: usize,
    failures: [Vec<(String, String)>; 5],
}

impl Report {
    fn run(&mut self, id: String, run: impl FnOnce() -> Result<(), Failure>) {
        let result = catch_unwind(AssertUnwindSafe(run)).unwrap_or_else(|panic| {
            let message = panic
                .downcast_ref::<String>()
                .map(String::as_str)
                .or_else(|| panic.downcast_ref::<&str>().copied())
                .unwrap_or("non-string panic");
            Err(Failure::Execution(format!("native panic: {message}")))
        });
        match result {
            Ok(()) => self.passed += 1,
            Err(failure) => {
                let (category, reason) = failure.parts();
                self.failures[category].push((id, reason));
            }
        }
    }

    fn finish(self) {
        let failed: usize = self.failures.iter().map(Vec::len).sum();
        let attempted = self.passed + failed;
        assert_ne!(
            attempted, 0,
            "no upstream cases match VINEFLOWER_RS_PARITY_FILTER"
        );
        let labels = [
            "missing JDK",
            "missing fixture",
            "unsupported",
            "mismatch",
            "execution error",
        ];
        eprintln!(
            "Upstream parity: {attempted} case(s), {} exact match(es)",
            self.passed
        );
        for (label, cases) in labels.into_iter().zip(self.failures) {
            eprintln!("{label}: {}", cases.len());
            for (id, reason) in cases {
                eprintln!("  {id}: {reason}");
            }
        }
        assert_eq!(
            failed, 0,
            "not all upstream cases matched their exact goldens"
        );
    }
}

#[test]
fn imported_registrations_reference_checked_in_goldens() {
    let fixture = fixture_root();
    let manifest = Manifest::load();
    assert_eq!(manifest.defaults["__unit_test_mode__"], "1");
    let mut ids = BTreeSet::new();
    let mut alternates = 0;
    for case in &manifest.cases {
        let id = case.id();
        assert!(ids.insert(id.clone()), "duplicate registration {id}");
        let data = suite_data(&fixture, case.suite);
        let path = case.golden(&data);
        assert!(
            path.is_file(),
            "missing golden for {id}: {}",
            path.display()
        );
        if let Some(alternate) = case.alternate {
            alternates += 1;
            assert!(
                data.join("results").join(alternate).is_file(),
                "missing alternate {alternate}"
            );
        }
    }
    assert_eq!(ids.len(), 688);
    assert_eq!(alternates, 3);
}

#[test]
fn checked_in_class_identity_and_bytecode() {
    let root = fixture_root();
    let samples = [
        ("testData/classes/bulk/pkg/Main.class", "pkg/Main", 52, 0),
        (
            "testData/classes/bulk/pkg/res/Loader.class",
            "pkg/res/Loader",
            52,
            0,
        ),
        (
            "plugins/idea-not-null/testData/classes/custom/TestIdeaNotNull.class",
            "pkg/TestIdeaNotNull",
            52,
            0,
        ),
    ];
    for (file, name, major, minor) in samples {
        let bytes = fs::read(root.join(file)).unwrap_or_else(|e| panic!("{file}: {e}"));
        let class = classfile::ClassFile::parse(&bytes).unwrap_or_else(|e| panic!("{file}: {e}"));
        assert_eq!(class.pool.class_name(class.this_class).unwrap(), name);
        assert_eq!((class.major_version, class.minor_version), (major, minor));
        let mut bodies = 0;
        for method in &class.methods {
            if let Some(code) = method.code(&class.pool).unwrap() {
                let instructions =
                    bytecode::decode(code.bytes).unwrap_or_else(|e| panic!("{name}: {e}"));
                let mut end = 0;
                for insn in instructions {
                    assert_eq!(insn.offset, end, "noncontiguous instruction in {name}");
                    assert!(insn.len > 0);
                    end += insn.len;
                }
                assert_ne!(end, 0);
                assert_eq!(
                    end as usize,
                    code.bytes.len(),
                    "truncated bytecode in {name}"
                );
                bodies += 1;
            }
        }
        assert!(bodies > 0, "no method code in {name}");
    }
}

#[test]
fn upstream_source_goldens_without_jdk() {
    let cases: &[(&str, &[u8], bool)] = &[
        (
            "TestVarType",
            include_bytes!("smoke/java8/TestVarType.class"),
            false,
        ),
        (
            "TestSimpleWhile",
            include_bytes!("smoke/java8/TestSimpleWhile.class"),
            true,
        ),
        (
            "TestInterfaceFields",
            include_bytes!("smoke/java8/TestInterfaceFields.class"),
            true,
        ),
        (
            "TestRecordSimple",
            include_bytes!("smoke/java16/TestRecordSimple.class"),
            false,
        ),
        (
            "TestEnumStaticField",
            include_bytes!("smoke/jasm/TestEnumStaticField.class"),
            false,
        ),
    ];
    let goldens = fixture_root().join("testData/results/pkg");
    for &(name, bytes, mapped) in cases {
        let mut options = Options::default();
        options.include_line_mappings = mapped;
        options.dump_original_lines = mapped;
        options.unit_test_mode = mapped;
        let source = decompile(bytes, &options).unwrap_or_else(|error| panic!("{name}: {error}"));
        let expected = read_normalized(&goldens.join(format!("{name}.dec"))).unwrap();
        assert_eq!(
            normalized(source.text.as_bytes(), false),
            expected,
            "{name}"
        );
    }
}

#[test]
fn upstream_bulk_and_cli_goldens() {
    let scratch = tempfile::tempdir().unwrap();
    let mut report = Report::default();
    for test in cli::CASES {
        report.run(test.id.into(), || {
            test.run(&fixture_root().join("testData"), scratch.path())
        });
    }
    report.finish();
}

#[test]
#[ignore = "explicit exact upstream parity; may report missing toolchains/fixtures and unsupported features"]
fn full_parity() {
    let scratch = tempfile::tempdir().expect("create upstream test workspace");
    let mut inputs = Inputs::new(scratch.path().join("compiled"));
    let filter = std::env::var("VINEFLOWER_RS_PARITY_FILTER").unwrap_or_default();
    let mut report = Report::default();
    for case in Manifest::load().cases {
        let id = case.id();
        if id.contains(&filter) {
            report.run(id, || run_single(&case, &mut inputs));
        }
    }
    for test in cli::CASES {
        if test.id.contains(&filter) {
            report.run(test.id.into(), || {
                test.run(&inputs.data("core"), scratch.path())
            });
        }
    }
    let lazy = "lazyLibrary/testLazy";
    if lazy.contains(&filter) {
        report.run(lazy.into(), || run_lazy_library(&mut inputs));
    }
    report.finish();
}

fn run_single(case: &Case, inputs: &mut Inputs) -> Result<(), Failure> {
    let data = inputs.data(case.suite);
    let reference = require_file(case.golden(&data), "source golden")?;
    let alternate = case
        .alternate
        .map(|name| require_file(data.join("results").join(name), "alternate source golden"))
        .transpose()?;
    let (class, companions) = inputs.sources(case)?;
    // A known runtime version is injected even when the bytecode was prebuilt.
    let runtime = match (case.options.get("include-runtime"), case.version.jdk) {
        (Some(&("1" | "current")), Some(major)) => Some(inputs.jdk(major)?),
        _ => None,
    };

    if !companions.is_empty() {
        let paths: Vec<_> = companions
            .iter()
            .map(|path| path.file_name().unwrap())
            .collect();
        let scala = if case.version.name == "SCALA" {
            " and Scala companion output"
        } else {
            ""
        };
        return Err(Failure::Unsupported(format!(
            "multi-class context{scala}: {paths:?}"
        )));
    }
    match case.suite {
        "kotlin" => {
            return Err(Failure::Unsupported(
                "Kotlin plugin (.kt source rendering)".into(),
            ));
        }
        "idea-not-null" => return Err(Failure::Unsupported("IDEA not-null plugin".into())),
        _ => {}
    }
    let mut options = Options::default();
    let mut unsupported = Vec::new();
    for (&name, &registered_value) in &case.options {
        let value = match (name, &runtime) {
            ("include-runtime", Some(home)) => home.to_str().ok_or_else(|| {
                Failure::Execution(format!("non-UTF-8 JDK path {}", home.display()))
            })?,
            _ => registered_value,
        };
        match options.set(name, value) {
            Ok(()) => {}
            // Some fixture switches select diagnostics, validation, or the
            // upstream algorithm rather than enabling an independent feature.
            // Try the native algorithm; unsupported bytecode and output changes
            // still fail. Changes away from these specific values are not projected.
            Err(OptionError::Unsupported(_))
                if matches!(
                    (name, value),
                    ("log-level", "warn")
                        | ("error-message", "")
                        | ("dump-exception-on-error", "0")
                        | ("include-runtime", "")
                        | ("include-classpath", "0")
                        | ("decompile-inner", "1")
                        | ("verify-pre-post-merges", "1")
                        | ("verify-anonymous-classes", "1")
                        | ("ternary-in-if", "1")
                        | ("force-jsr-inline", "1")
                        | ("ignore-invalid-bytecode", "1")
                        | ("keep-literals", "1")
                ) => {}
            Err(OptionError::Unsupported(_)) => unsupported.push(format!("{name}={value}")),
            Err(error) => return Err(Failure::Execution(error.to_string())),
        }
    }
    if !unsupported.is_empty() {
        return Err(Failure::Unsupported(format!(
            "upstream options: {}",
            unsupported.join(", ")
        )));
    }

    let bytes = fs::read(&class).map_err(|e| Failure::io(&class, e))?;
    let source = decompile(&bytes, &options).map_err(|error| {
        let failure = format!("{}: {error}", class.display());
        match error {
            DecompileError::Unsupported { .. } | DecompileError::Method { .. } => {
                Failure::Unsupported(failure)
            }
            _ => Failure::Execution(failure),
        }
    })?;
    let actual_name = format!("{}.java", source.class_name.rsplit('/').next().unwrap());
    let stem = class
        .file_stem()
        .and_then(|s| s.to_str())
        .expect("non-UTF-8 fixture name");
    let preferred_name = format!("{stem}.{}", case.version.extension);
    let fallback_name = format!("{stem}.java");
    let expected_name = case.output.unwrap_or(if actual_name == preferred_name {
        &preferred_name
    } else {
        &fallback_name
    });
    if actual_name != expected_name {
        return Err(Failure::Mismatch(format!(
            "expected output {expected_name}, generated {actual_name}"
        )));
    }
    let actual = normalized(source.text.as_bytes(), false);
    let expected = read_normalized(&reference)?;
    if actual == expected {
        return Ok(());
    }
    if let Some(alternate) = alternate {
        let alternate_text = read_normalized(&alternate)?;
        if actual == alternate_text {
            return Ok(());
        }
        return Err(Failure::Mismatch(format!(
            "{}; alternate {} also differs: {}",
            difference(&expected, &actual),
            alternate.display(),
            difference(&alternate_text, &actual),
        )));
    }
    let warning = if case.failable {
        " (upstream marks this failable)"
    } else {
        ""
    };
    Err(Failure::Mismatch(format!(
        "{}{warning}",
        difference(&expected, &actual)
    )))
}

fn run_lazy_library(inputs: &mut Inputs) -> Result<(), Failure> {
    let java8 = Version::java8();
    require_file(
        inputs
            .data("core")
            .join("lazyLibrary/TestLibraryIsOnClasspath.java"),
        "lazy-library golden",
    )?;
    inputs.class_file("core", java8, "pkg/TestLibraryIsOnClasspath")?;
    inputs.class_file("core", java8, "ext/TestLibrary")?;
    Err(Failure::Unsupported(
        "lazy classpath provider (IContextSource)".into(),
    ))
}

fn read_normalized(path: &Path) -> Result<String, Failure> {
    let bytes = fs::read(path).map_err(|e| Failure::io(path, e))?;
    Ok(normalized(&bytes, false))
}

fn normalized(bytes: &[u8], archive: bool) -> String {
    let text = String::from_utf8_lossy(bytes).replace("\r\n", "\n");
    let text = if archive {
        text.replace('\r', "\n")
    } else {
        text
    };
    text.trim_matches(|c| c <= '\u{20}').to_owned()
}

fn difference(expected: &str, actual: &str) -> String {
    let mut left = expected.split('\n');
    let mut right = actual.split('\n');
    for line in 1.. {
        let expected = left.next();
        let actual = right.next();
        if expected != actual {
            return format!(
                "first difference at line {line}: expected {expected:?}, got {actual:?}"
            );
        }
        if expected.is_none() {
            break;
        }
    }
    unreachable!("difference requested for equal sources")
}
