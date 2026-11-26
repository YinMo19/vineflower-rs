// Based on Vineflower's SingleClassesTestBase and DecompilerTestFixture.
// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

#[path = "support/cli.rs"]
mod cli;
#[path = "support/inputs.rs"]
mod inputs;
#[path = "support/manifest.rs"]
mod manifest;

use std::fmt::Display;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::Path;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::{fs, io};

use vineflower_rs::engine::{
    Options,
    class_writer::javadoc::{JavadocProvider, JavadocStyle},
    context_source::{ContextSource, Entries},
    driver::{DecompiledClass, Decompiler, MemorySource},
};
use vineflower_rs::structs::{StructClass, StructField, StructMethod};

use inputs::{Inputs, fixture_root, require_file};
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

    fn native(path: &Path, error: io::Error) -> Self {
        if error.kind() == io::ErrorKind::Unsupported {
            Self::Unsupported(format!("{}: {error}", path.display()))
        } else {
            Self::io(path, error)
        }
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
            "TestRecordAnno",
            include_bytes!("smoke/java16/TestRecordAnno.class"),
            false,
        ),
        (
            "TestRecordEmptyConstructor",
            include_bytes!("smoke/java16/TestRecordEmptyConstructor.class"),
            true,
        ),
        (
            "TestRecordGenericVararg",
            include_bytes!("smoke/java16/TestRecordGenericVararg.class"),
            true,
        ),
        (
            "TestRecordMixup",
            include_bytes!("smoke/java16/TestRecordMixup.class"),
            true,
        ),
        (
            "TestClassSwitch",
            include_bytes!("smoke/java8/TestClassSwitch.class"),
            true,
        ),
        (
            "TestCompoundAssignment",
            include_bytes!("smoke/java8/TestCompoundAssignment.class"),
            true,
        ),
        (
            "TestPrimitiveTypeClasses",
            include_bytes!("smoke/java8/TestPrimitiveTypeClasses.class"),
            true,
        ),
        (
            "TestConstantUninlining",
            include_bytes!("smoke/java8/TestConstantUninlining.class"),
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
        let mut options = without_runtime();
        options.bytecode_source_mapping = mapped;
        options.dump_original_lines = mapped;
        options.unit_test_mode = mapped;
        let entry = format!("pkg/{name}");
        let source = decompile_smoke(name, &[(&entry, bytes)], options, None)
            .unwrap_or_else(|error| panic!("{name}: {error:?}"));
        let expected = read_normalized(&goldens.join(format!("{name}.dec"))).unwrap();
        assert_eq!(normalized(source.as_bytes(), false), expected, "{name}");
    }
}

#[test]
fn upstream_javadoc_and_selected_nested_method() {
    let goldens = fixture_root().join("testData/results/pkg");
    for (name, bytes, style) in [
        (
            "TestJavadoc",
            include_bytes!("smoke/java8/TestJavadoc.class").as_slice(),
            JavadocStyle::Html,
        ),
        (
            "TestMarkdownJavadoc",
            include_bytes!("smoke/java8/TestMarkdownJavadoc.class").as_slice(),
            JavadocStyle::Markdown,
        ),
    ] {
        let entry = format!("pkg/{name}");
        let source =
            decompile_smoke(name, &[(&entry, bytes)], without_runtime(), Some(style)).unwrap();
        assert_eq!(
            normalized(source.as_bytes(), false),
            read_normalized(&goldens.join(format!("{name}.dec"))).unwrap()
        );
    }
    let mut options = without_runtime();
    options.bytecode_source_mapping = true;
    options.dump_original_lines = true;
    options.unit_test_mode = true;
    options.method_to_decompile = "pkg/TestSingleMethodInInnerClass$Inner.test()V".into();
    let source = decompile_smoke(
        "TestSingleMethodInInnerClass",
        &[
            (
                "pkg/TestSingleMethodInInnerClass",
                include_bytes!("smoke/java8/TestSingleMethodInInnerClass.class"),
            ),
            (
                "pkg/TestSingleMethodInInnerClass$Inner",
                include_bytes!("smoke/java8/TestSingleMethodInInnerClass$Inner.class"),
            ),
        ],
        options,
        None,
    )
    .unwrap();
    let expected = read_normalized(&goldens.join("TestSingleMethodInInnerClass.dec")).unwrap();
    assert_eq!(normalized(source.as_bytes(), false), expected);
}

#[test]
fn upstream_lazy_library_golden() {
    let root = fixture_root();
    let expected =
        read_normalized(&root.join("testData/lazyLibrary/TestLibraryIsOnClasspath.java")).unwrap();
    let mut decompiler = Decompiler::new(without_runtime()).unwrap();
    add_smoke_classes(
        &mut decompiler,
        &[(
            "pkg/TestLibraryIsOnClasspath",
            include_bytes!("smoke/java8/TestLibraryIsOnClasspath.class"),
        )],
    )
    .unwrap();
    check_lazy_library(
        decompiler,
        || Ok(include_bytes!("smoke/java8/TestLibrary.class").to_vec()),
        &expected,
    )
    .unwrap();
}

#[test]
fn upstream_bulk_and_cli_goldens() {
    let scratch = tempfile::tempdir().unwrap();
    let fixture = Manifest::load().fixture;
    let mut report = Report::default();
    for test in cli::CASES {
        report.run(test.id.into(), || {
            test.run(&fixture_root().join("testData"), scratch.path(), &fixture)
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
    let Manifest { cases, fixture } = Manifest::load();
    for case in cases {
        let id = case.id();
        if id.contains(&filter) {
            report.run(id, || run_single(&case, &mut inputs));
        }
    }
    for test in cli::CASES {
        if test.id.contains(&filter) {
            report.run(test.id.into(), || {
                test.run(&inputs.data("core"), scratch.path(), &fixture)
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

    let mut options = Options::default();
    options.decompile_kotlin = case.suite == "kotlin";
    options.idea_notnull = case.suite == "idea-not-null";
    let mut javadoc = None;
    let mut unsupported = Vec::new();
    for (&name, &registered_value) in &case.options {
        if let ("fabric:javadoc", "javadoc" | "markdown") = (name, registered_value) {
            javadoc = Some(if registered_value == "markdown" {
                JavadocStyle::Markdown
            } else {
                JavadocStyle::Html
            });
            continue;
        }
        let value = match (name, &runtime) {
            ("include-runtime", Some(home)) => home.to_str().ok_or_else(|| {
                Failure::Execution(format!("non-UTF-8 JDK path {}", home.display()))
            })?,
            _ => registered_value,
        };
        if !options.set(name, value) {
            unsupported.push(format!("{name}={value}"));
        }
    }
    if !unsupported.is_empty() {
        return Err(Failure::Unsupported(format!(
            "upstream options: {}",
            unsupported.join(", ")
        )));
    }
    let mut decompiler = Decompiler::new(options).map_err(|e| Failure::native(&class, e))?;
    if let Some(style) = javadoc {
        decompiler.set_javadoc(Arc::new(FixtureJavadoc(style)));
    }
    for path in std::iter::once(&class).chain(&companions) {
        decompiler
            .add_source(path)
            .map_err(|e| Failure::native(path, e))?;
    }
    let sources = decompiler
        .decompile()
        .map_err(|e| Failure::native(&class, e))?;
    let stem = class
        .file_stem()
        .and_then(|s| s.to_str())
        .expect("non-UTF-8 fixture name");
    let preferred = format!("{stem}.{}", case.version.extension);
    let fallback = format!("{stem}.java");
    let source = if let Some(explicit) = case.output {
        require_source(&sources, explicit)?
    } else {
        match find_source(&sources, &preferred) {
            Some(source) => source,
            None => require_source(&sources, &fallback)?,
        }
    };
    let mut actual = normalized(source.as_bytes(), false);
    if case.version.name == "SCALA" {
        use std::fmt::Write;
        for companion in &case.companions {
            let basename = companion.rsplit('/').next().unwrap();
            let source =
                require_source(&sources, &format!("{basename}.{}", case.version.extension))?;
            let _ = write!(
                actual,
                "\n\n// Decompiled companion from {companion}\n{}",
                normalized(source.as_bytes(), false)
            );
        }
    }
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

fn find_source<'a>(sources: &'a [DecompiledClass], name: &str) -> Option<&'a str> {
    sources
        .iter()
        .rfind(|source| source.entry_name.rsplit('/').next() == Some(name))
        .map(|source| source.source.as_str())
}

fn require_source<'a>(sources: &'a [DecompiledClass], name: &str) -> Result<&'a str, Failure> {
    find_source(sources, name).ok_or_else(|| {
        let names: Vec<_> = sources
            .iter()
            .map(|source| source.entry_name.as_str())
            .collect();
        Failure::Mismatch(format!("expected output {name}, generated {names:?}"))
    })
}

fn without_runtime() -> Options {
    let mut options = Options::default();
    options.include_runtime.clear();
    options
}

fn add_smoke_classes(decompiler: &mut Decompiler, classes: &[(&str, &[u8])]) -> io::Result<()> {
    let entries = classes
        .iter()
        .map(|&(name, bytes)| (name.to_owned(), bytes.to_vec()));
    decompiler.add_source_context(Arc::new(MemorySource::new("smoke", entries)))
}

fn decompile_smoke(
    name: &str,
    classes: &[(&str, &[u8])],
    options: Options,
    javadoc: Option<JavadocStyle>,
) -> Result<String, Failure> {
    let path = Path::new(name);
    let mut decompiler = Decompiler::new(options).map_err(|e| Failure::native(path, e))?;
    if let Some(style) = javadoc {
        decompiler.set_javadoc(Arc::new(FixtureJavadoc(style)));
    }
    add_smoke_classes(&mut decompiler, classes).map_err(|e| Failure::native(path, e))?;
    let sources = decompiler
        .decompile()
        .map_err(|e| Failure::native(path, e))?;
    require_source(&sources, &format!("{name}.java")).map(str::to_owned)
}

struct FixtureJavadoc(JavadocStyle);

impl JavadocProvider for FixtureJavadoc {
    fn class_doc(&self, class: &StructClass) -> Option<String> {
        Some(format!("Class javadoc for '{}'", class.qualified_name))
    }

    fn field_doc(&self, _class: &StructClass, field: &StructField) -> Option<String> {
        Some(format!("Field javadoc for '{}'", field.name))
    }

    fn method_doc(&self, _class: &StructClass, method: &StructMethod) -> Option<String> {
        Some(format!("Method javadoc for '{}'", method.name))
    }

    fn class_style(&self, _class: &StructClass) -> JavadocStyle {
        self.0
    }
}

fn run_lazy_library(inputs: &mut Inputs) -> Result<(), Failure> {
    let java8 = Version::java8();
    let expected = read_normalized(&require_file(
        inputs
            .data("core")
            .join("lazyLibrary/TestLibraryIsOnClasspath.java"),
        "lazy-library golden",
    )?)?;
    let primary = inputs.class_file("core", java8, "pkg/TestLibraryIsOnClasspath")?;
    let library = inputs.class_file("core", java8, "ext/TestLibrary")?;
    let mut decompiler =
        Decompiler::new(without_runtime()).map_err(|e| Failure::native(&primary, e))?;
    decompiler
        .add_source(&primary)
        .map_err(|e| Failure::native(&primary, e))?;
    check_lazy_library(decompiler, move || fs::read(&library), &expected)
}

fn check_lazy_library(
    mut decompiler: Decompiler,
    load_class: impl Fn() -> io::Result<Vec<u8>> + Send + Sync + 'static,
    expected: &str,
) -> Result<(), Failure> {
    struct FixtureLibrary<F> {
        load_class: F,
        reads: AtomicUsize,
    }

    impl<F: Fn() -> io::Result<Vec<u8>> + Send + Sync> ContextSource for FixtureLibrary<F> {
        fn get_name(&self) -> String {
            "Test Lazy Library".to_owned()
        }

        fn get_entries(&self) -> Entries {
            Entries::default()
        }

        fn is_lazy(&self) -> bool {
            true
        }

        fn get_input_stream(&self, name: &str) -> io::Result<Option<Vec<u8>>> {
            if name != "ext/TestLibrary.class" {
                return Ok(None);
            }
            self.reads.fetch_add(1, Ordering::Relaxed);
            (self.load_class)().map(Some)
        }
    }

    let path = Path::new("TestLibraryIsOnClasspath");
    let library = Arc::new(FixtureLibrary {
        load_class,
        reads: AtomicUsize::new(0),
    });
    decompiler
        .add_library_context(library.clone())
        .map_err(|e| Failure::native(path, e))?;
    let sources = decompiler
        .decompile()
        .map_err(|e| Failure::native(path, e))?;
    let actual = normalized(
        require_source(&sources, "TestLibraryIsOnClasspath.java")?.as_bytes(),
        false,
    );
    if actual != expected {
        return Err(Failure::Mismatch(difference(expected, &actual)));
    }
    let reads = library.reads.load(Ordering::Relaxed);
    if reads != 1 {
        return Err(Failure::Execution(format!(
            "expected one lazy class read, including cached lookups, got {reads}"
        )));
    }
    Ok(())
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
