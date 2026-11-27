use std::{
    collections::BTreeMap, fs, io::Read, path::Path, process::Command, sync::Arc, time::Duration,
};

use vineflower_rs::{
    engine::{
        Options,
        class_writer::javadoc::JavadocProvider,
        context_source::{ContextSource, Entries},
        driver::{Decompiler, MemorySource},
    },
    structs::StructClass,
};

#[allow(dead_code, reason = "the driver uses CLI and fixture helpers")]
#[path = "support/upstream_reference.rs"]
mod upstream_reference;

#[path = "support/cli_interface.rs"]
mod cli_interface;

#[path = "support/worker_allocations.rs"]
mod worker_allocations;

#[test]
fn memory_group_writes_roots_and_maps_lines_using_a_read_only_library() {
    let classes = [
        (
            "pkg/TestLibraryIsOnClasspath".into(),
            include_bytes!("smoke/java8/TestLibraryIsOnClasspath.class").to_vec(),
        ),
        (
            "pkg/TestSingleMethodInInnerClass".into(),
            include_bytes!("smoke/java8/TestSingleMethodInInnerClass.class").to_vec(),
        ),
        (
            "pkg/TestSingleMethodInInnerClass$Inner".into(),
            include_bytes!("smoke/java8/TestSingleMethodInInnerClass$Inner.class").to_vec(),
        ),
    ];
    let mut options = Options::default();
    options.include_runtime = "0".into();
    options.bytecode_source_mapping = true;
    options.decompile_kotlin = true;
    let mut driver = Decompiler::new(options).unwrap();
    driver
        .add_source_context(Arc::new(MemorySource::new("sample classes", classes)))
        .unwrap();
    driver
        .add_library_context(Arc::new(LazyLibrary {
            before_read: |_| {},
        }))
        .unwrap();
    driver.set_javadoc(Arc::new(Documentation));

    let classes = driver.decompile().unwrap();
    assert_eq!(
        classes
            .iter()
            .map(|class| class.qualified_name.as_str())
            .collect::<Vec<_>>(),
        [
            "pkg/TestLibraryIsOnClasspath",
            "pkg/TestSingleMethodInInnerClass"
        ]
    );
    let mapped = &classes[0];
    assert_eq!(mapped.entry_name, "pkg/TestLibraryIsOnClasspath.java");
    assert!(mapped.source.contains("Driver documentation"));
    assert!(
        mapped
            .source
            .contains("TestLibrary.identity(\"Hello, World!\")")
    );
    let mapping = mapped.mapping.as_deref().unwrap();
    assert!(!mapping.is_empty());
    assert!(mapping.chunks_exact(2).all(|row| row[0] > 0 && row[1] > 0));
    assert!(classes[1].source.contains("static class Inner {"));
    assert!(classes[1].source.contains("Hello from inner class 2"));
}

#[test]
fn library_workers_keep_java_root_order_and_mixed_language_output() {
    let java: &[(&str, &[u8])] = &[
        (
            "pkg/TestSimpleWhile",
            include_bytes!("smoke/java8/TestSimpleWhile.class"),
        ),
        (
            "pkg/TestSingleMethodInInnerClass",
            include_bytes!("smoke/java8/TestSingleMethodInInnerClass.class"),
        ),
        (
            "pkg/TestSingleMethodInInnerClass$Inner",
            include_bytes!("smoke/java8/TestSingleMethodInInnerClass$Inner.class"),
        ),
    ];
    let mixed: &[(&str, &[u8])] = &[
        (
            "pkg/TestParams",
            include_bytes!("smoke/kt/TestParams.class"),
        ),
        java[0],
    ];
    let decompile = |entries: &[(&str, &[u8])], workers: Option<i32>| {
        let mut options = Options::default();
        if let Some(count) = workers {
            options.thread_count = count;
        }
        options.include_runtime = "0".into();
        options.decompile_kotlin = true;
        options.bytecode_source_mapping = true;
        let mut driver = Decompiler::new(options).unwrap();
        driver
            .add_source_context(Arc::new(MemorySource::new(
                "ordered roots",
                entries
                    .iter()
                    .map(|&(name, bytes)| (name.to_owned(), bytes.to_vec())),
            )))
            .unwrap();
        driver
            .decompile()
            .unwrap()
            .into_iter()
            .map(|class| (class.entry_name, class.source, class.mapping))
            .collect::<Vec<_>>()
    };
    for (entries, names) in [
        (
            java,
            [
                "pkg/TestSimpleWhile.java",
                "pkg/TestSingleMethodInInnerClass.java",
            ],
        ),
        (mixed, ["pkg/TestParams.kt", "pkg/TestSimpleWhile.java"]),
    ] {
        let expected = decompile(entries, Some(1));
        assert_eq!(
            expected
                .iter()
                .map(|class| class.0.as_str())
                .collect::<Vec<_>>(),
            names
        );
        assert!(
            expected
                .iter()
                .any(|class| class.2.as_ref().is_some_and(|mapping| !mapping.is_empty()))
        );
        for workers in [Some(2), Some(0), None] {
            assert_eq!(
                decompile(entries, workers),
                expected,
                "{names:?}, thread-count={workers:?}"
            );
        }
    }
}

struct LazyLibrary {
    before_read: fn(&str),
}

impl ContextSource for LazyLibrary {
    fn get_name(&self) -> String {
        "read-only sample library".into()
    }

    fn get_entries(&self) -> Entries {
        panic!("Lazy libraries are never enumerated")
    }

    fn is_lazy(&self) -> bool {
        true
    }

    fn get_input_stream(&self, resource: &str) -> std::io::Result<Option<Vec<u8>>> {
        (self.before_read)(resource);
        Ok((resource == "ext/TestLibrary.class")
            .then(|| include_bytes!("smoke/java8/TestLibrary.class").to_vec()))
    }
}

#[test]
fn method_deadline_expires_during_lazy_resolution_and_is_scoped_to_code() {
    let decompile = |seconds, test_mode, before_read| {
        let mut options = Options::default();
        options.include_runtime = "0".into();
        options.max_time_per_method = seconds;
        options.unit_test_mode = test_mode;
        let mut driver = Decompiler::new(options).unwrap();
        driver
            .add_source_context(Arc::new(MemorySource::new(
                "method deadline",
                [
                    (
                        "TestListIteratorHierarchy".into(),
                        include_bytes!("smoke/java8/TestListIteratorHierarchy.class").to_vec(),
                    ),
                    (
                        "pkg/TestLibraryIsOnClasspath".into(),
                        include_bytes!("smoke/java8/TestLibraryIsOnClasspath.class").to_vec(),
                    ),
                ],
            )))
            .unwrap();
        driver
            .add_library_context(Arc::new(LazyLibrary { before_read }))
            .unwrap();
        driver
            .decompile()
            .unwrap()
            .into_iter()
            .map(|class| class.source)
            .collect::<Vec<_>>()
    };

    // Foreach recognition consults the iterator hierarchy during the method.
    // The second root first resolves ext/TestLibrary in the writer. Delay both
    // lookups to distinguish their scopes independently of processor speed.
    let timed = decompile(1, false, |name| {
        if matches!(
            name,
            "java/util/ListIterator.class" | "ext/TestLibrary.class"
        ) {
            std::thread::sleep(Duration::from_millis(1100));
        }
    });
    assert_eq!(
        timed[0].matches("Couldn't be decompiled").count(),
        1,
        "{}",
        timed[0]
    );
    assert!(
        timed[0].contains("Processing time limit exceeded"),
        "{}",
        timed[0]
    );
    let untimed = decompile(0, false, |_| {});
    assert!(untimed[0].contains("iterator.hasNext()"));
    assert_eq!(timed[1], untimed[1]);
    assert!(timed[1].contains("TestLibrary.identity("));
    assert_eq!(decompile(-1, true, |_| {}), untimed);
}

struct Documentation;

impl JavadocProvider for Documentation {
    fn class_doc(&self, _class: &StructClass) -> Option<String> {
        Some("Driver documentation".into())
    }
}

fn compile_java17(sources: &[&Path], dest: &Path) {
    use upstream_reference::{jdk_tool, run};

    run(Command::new(jdk_tool("javac"))
        .args(["--release", "17", "-g", "-d"])
        .arg(dest)
        .args(sources));
}

fn replace_utf8_entry(bytes: &mut Vec<u8>, original: &str, replacement: &str) {
    // The fixtures use ASCII strings that each occupy one complete CONSTANT_Utf8.
    let entry = |value: &str| {
        let mut bytes = vec![1];
        bytes.extend_from_slice(&u16::try_from(value.len()).unwrap().to_be_bytes());
        bytes.extend_from_slice(value.as_bytes());
        bytes
    };
    let original = entry(original);
    let offsets: Vec<_> = bytes
        .windows(original.len())
        .enumerate()
        .filter_map(|(offset, bytes)| (bytes == original).then_some(offset))
        .collect();
    let [offset] = offsets.as_slice() else {
        panic!("expected a unique CONSTANT_Utf8 entry");
    };
    bytes.splice(*offset..offset + original.len(), entry(replacement));
}

fn run_main(classpath: &Path, class_name: &str) -> Vec<u8> {
    use upstream_reference::{jdk_tool, run};

    run(Command::new(jdk_tool("java"))
        .arg("-cp")
        .arg(classpath)
        .arg(class_name))
    .stdout
}

#[test]
#[ignore = "requires JDK 17 or later"]
fn generic_inner_class_and_loop_survive_recompilation() {
    use upstream_reference::run;

    let scratch = tempfile::tempdir().unwrap();
    let classes = scratch.path().join("classes");
    let output = scratch.path().join("output");
    let rebuilt = scratch.path().join("rebuilt");
    fs::create_dir(&output).unwrap();

    compile_java17(&[Path::new("test/support/Ledger.java")], &classes);
    run(Command::new(env!("CARGO_BIN_EXE_vineflower-rs"))
        .args(["--include-runtime=0", "--silent", "--folder"])
        .arg(&classes)
        .arg(&output));
    compile_java17(&[&output.join("Ledger.java")], &rebuilt);
    assert_eq!(run_main(&classes, "Ledger"), run_main(&rebuilt, "Ledger"));
}

#[test]
#[ignore = "requires JDK 17 or later"]
fn guarded_nested_finally_preserves_cleanup_and_exception_paths() {
    use upstream_reference::{jdk_tool, run};

    let scratch = tempfile::tempdir().unwrap();
    let classes = scratch.path().join("classes");
    let output = scratch.path().join("output");
    let rebuilt = scratch.path().join("rebuilt");
    compile_java17(&[Path::new("test/support/CloseTransaction.java")], &classes);
    run(Command::new(env!("CARGO_BIN_EXE_vineflower-rs"))
        .arg("--include-runtime=0")
        .arg(&classes)
        .arg(&output));
    let rendered = output.join("CloseTransaction.java");
    let source = fs::read_to_string(&rendered).unwrap();
    assert!(!source.contains("Couldn't be decompiled"), "{source}");
    // A spurious exit from the assertion leaves a labeled, empty then arm.
    assert!(source.contains("if (open) {"), "{source}");
    compile_java17(&[&rendered], &rebuilt);
    for classpath in [classes, rebuilt] {
        let execution = run(Command::new(jdk_tool("java"))
            .args(["-ea", "-cp"])
            .arg(classpath)
            .arg("CloseTransaction"));
        let lines = String::from_utf8(execution.stdout).unwrap();
        assert_eq!(
            lines.lines().collect::<Vec<_>>(),
            ["assert", "1345", "12345", "135!", "1345!", "1345!"]
        );
    }
}

#[test]
#[ignore = "requires JDK 17 or later"]
fn local_class_keeps_its_generic_scope_when_enclosing_method_is_referenced() {
    let scratch = tempfile::tempdir().unwrap();
    let classes = scratch.path().join("classes");
    let output = scratch.path().join("output");
    let rebuilt = scratch.path().join("rebuilt");
    compile_java17(&[Path::new("test/support/ScopedReferences.java")], &classes);

    let mut child = Command::new(env!("CARGO_BIN_EXE_vineflower-rs"))
        .arg(&classes)
        .arg(&output)
        .stdout(std::process::Stdio::null())
        .spawn()
        .unwrap();
    let deadline = std::time::Instant::now() + Duration::from_secs(30);
    while child.try_wait().unwrap().is_none() {
        if std::time::Instant::now() >= deadline {
            child.kill().unwrap();
            child.wait().unwrap();
            panic!("decompiling ScopedReferences exceeded 30 seconds");
        }
        std::thread::sleep(Duration::from_millis(25));
    }
    assert!(child.wait().unwrap().success());

    let rendered = output.join("ScopedReferences.java");
    let source = fs::read_to_string(&rendered).unwrap();
    // The method reference in length() must not replace copy()'s bound for T.
    assert!(source.contains("T apply(T input)"), "{source}");
    compile_java17(&[&rendered], &rebuilt);
    assert_eq!(run_main(&rebuilt, "ScopedReferences"), b"5");
}

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn nested_constructor_and_switch_map_survive_class_and_unit_order() {
    use upstream_reference::{jdk_tool, run, upstream_jar};

    let scratch = tempfile::tempdir().unwrap();
    let root = scratch.path();
    let classes = root.join("classes");
    fs::write(
        root.join("Owner.java"),
        r#"
public final class Owner {
    private final int base;

    public Owner(int base) {
        this.base = base;
    }

    public class Member {
        private final int delta;

        public Member(int delta) {
            this.delta = delta;
        }

        public int value() {
            return Owner.this.base + this.delta;
        }
    }

    public enum Mode {
        OFF, ON, OTHER
    }

    public static final class Table {
        public static int[] $SWITCH_TABLE$Mode() {
            int[] map = new int[Mode.values().length];
            map[Mode.OFF.ordinal()] = 70000;
            map[Mode.ON.ordinal()] = 90000;
            return map;
        }
    }
}
"#,
    )
    .unwrap();
    fs::write(
        root.join("Consumer.java"),
        r#"
public final class Consumer {
    private static int select(Owner.Mode mode) {
        switch (Owner.Table.$SWITCH_TABLE$Mode()[mode.ordinal()]) {
            case 70000: return 13;
            case 90000: return 17;
            default: return 23;
        }
    }

    public static void main(String[] args) {
        Owner owner = new Owner(31);
        System.out.println(owner.new Member(11).value());
        for (Owner.Mode mode : Owner.Mode.values()) {
            System.out.println(select(mode));
        }
    }
}
"#,
    )
    .unwrap();
    let compile = |sources: &Path, dest: &Path| {
        compile_java17(
            &[&sources.join("Owner.java"), &sources.join("Consumer.java")],
            dest,
        );
    };
    compile(root, &classes);
    // Keep another independent root so the Owner/Consumer component can run
    // alongside it even when their cross-root wrapper access connects them.
    let other_source = root.join("Other.java");
    fs::write(
        &other_source,
        "public class Other { int value() { return 41; } }",
    )
    .unwrap();
    compile_java17(&[&other_source], &classes);
    let expected_execution = run_main(&classes, "Consumer");
    assert_eq!(expected_execution, b"42\n13\n17\n23\n");

    // ZIP entry order controls preprocessing within a unit independently of
    // the command-line order of separate units.
    let owner = [
        "Owner.class",
        "Owner$Member.class",
        "Owner$Mode.class",
        "Owner$Table.class",
    ];
    let consumer = ["Consumer.class"];
    for (name, entries) in [
        ("owner", owner.to_vec()),
        ("consumer", consumer.to_vec()),
        (
            "owner-first",
            [owner.as_slice(), &["Other.class"], &consumer].concat(),
        ),
        (
            "consumer-first",
            [consumer.as_slice(), &["Other.class"], &owner].concat(),
        ),
    ] {
        let mut jar =
            zip::ZipWriter::new(fs::File::create(root.join(format!("{name}.jar"))).unwrap());
        for entry in entries {
            jar.start_file(entry, zip::write::SimpleFileOptions::default())
                .unwrap();
            std::io::copy(&mut fs::File::open(classes.join(entry)).unwrap(), &mut jar).unwrap();
        }
        jar.finish().unwrap();
    }

    let options = ["--include-runtime=0", "--folder", "--silent"];
    let upstream = upstream_jar();
    for (layout, inputs, enum_switch) in [
        ("holder-first", &["owner-first"][..], true),
        ("holder-last", &["consumer-first"][..], true),
        ("holder-unit-first", &["owner", "consumer"][..], true),
        ("holder-unit-last", &["consumer", "owner"][..], false),
    ] {
        let expected = root.join(format!("{layout}-upstream"));
        fs::create_dir(&expected).unwrap();
        let inputs = inputs.iter().map(|name| root.join(format!("{name}.jar")));
        run(Command::new(jdk_tool("java"))
            .arg("-jar")
            .arg(&upstream)
            .arg("--thread-count=1")
            .args(options)
            .args(inputs.clone())
            .arg(&expected));
        let expected = directory(&expected);
        for (name, count) in [
            ("one", Some(1)),
            ("two", Some(2)),
            ("auto", Some(0)),
            ("default", None),
        ] {
            let actual = root.join(format!("{layout}-native-{name}"));
            fs::create_dir(&actual).unwrap();
            run(Command::new(env!("CARGO_BIN_EXE_vineflower-rs"))
                .args(count.map(|count| format!("--thread-count={count}")))
                .args(options)
                .args(inputs.clone())
                .arg(&actual));
            assert_eq!(directory(&actual), expected, "{layout}, {name}");
            if count.is_none() {
                let source = fs::read_to_string(actual.join("Consumer.java")).unwrap();
                assert_eq!(source.contains("switch (mode)"), enum_switch, "{layout}");
                assert!(source.contains("owner.new Member(11)"), "{layout}");
                let rebuilt = root.join(format!("{layout}-rebuilt"));
                compile(&actual, &rebuilt);
                assert_eq!(
                    run_main(&rebuilt, "Consumer"),
                    expected_execution,
                    "{layout}"
                );
            }
        }
    }
}

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn wide_reaching_versions_match_upstream_and_recompile() {
    use std::fmt::Write as _;

    use upstream_reference::{jdk_tool, run, upstream_jar};

    let scratch = tempfile::tempdir().unwrap();
    let root = scratch.path();
    let source = root.join("WideFlow.java");
    let mut java = String::from(
        "public class WideFlow {\n    static int run(int bits) {\n        int value = bits;\n",
    );
    // Each conditional introduces a definition that meets the previous value.
    for branch in 0..150 {
        let mask = 1 << (branch % 29);
        let offset = 11 * branch;
        writeln!(
            java,
            "        if ((bits & {mask}) != 0) value ^= (bits + {offset});"
        )
        .unwrap();
    }
    java.push_str(
        r#"        for (int i = 0; i < 5; ++i) {
            try {
                value += 100 / ((bits >>> (i * 3)) & 7);
                if ((value & 15) == 2) break;
            } catch (ArithmeticException ex) {
                value ^= i + 271;
            } finally {
                value = Integer.rotateLeft(value, 7);
            }
        }
        return value;
    }
    public static void main(String[] args) {
        long checksum = 3;
        int seed = 17;
        for (int i = 0; i < 256; ++i) {
            seed = 1664525 * seed + 1013904223;
            checksum = 31 * checksum + run(seed);
        }
        System.out.println(checksum);
    }
}
"#,
    );
    fs::write(&source, java).unwrap();
    let classes = root.join("classes");
    compile_java17(&[&source], &classes);
    let expected = run_main(&classes, "WideFlow");
    assert_eq!(expected, b"317456771009520057\n");

    let input = classes.join("WideFlow.class");
    let upstream = root.join("upstream");
    let native = root.join("native");
    fs::create_dir(&upstream).unwrap();
    fs::create_dir(&native).unwrap();
    let flags = ["--folder", "--log-level=ERROR", "--thread-count=1"];
    run(Command::new(jdk_tool("java"))
        .arg("-jar")
        .arg(upstream_jar())
        .args(flags)
        .arg(&input)
        .arg(&upstream));
    run(Command::new(env!("CARGO_BIN_EXE_vineflower-rs"))
        .args(flags)
        .arg(&input)
        .arg(&native));

    let rendered = native.join("WideFlow.java");
    assert_eq!(
        fs::read_to_string(&rendered).unwrap(),
        fs::read_to_string(upstream.join("WideFlow.java")).unwrap()
    );
    let rebuilt = root.join("rebuilt");
    compile_java17(&[&rendered], &rebuilt);
    assert_eq!(run_main(&rebuilt, "WideFlow"), expected);
}

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn parallel_method_graphs_preserve_archive_order_and_mappings() {
    use upstream_reference::{jdk_tool, run, upstream_jar};

    let scratch = tempfile::tempdir().unwrap();
    let root = scratch.path();
    let source = root.join("Main.java");
    fs::write(
        &source,
        r#"
abstract class First {
    abstract int unavailable(long value, double scale);

    static int choose(int n, StringBuilder trace) {
        try {
            if (n < 0) return -n;
            int total = 0;
            for (int i = 0; i < n; i++) {
                if ((i & 1) == 0) total += i;
            }
            return total;
        } finally {
            trace.append('A');
        }
    }

    static Missing absentFromClasspath(Missing value) { return value; }
}

class Second {
    native int unavailable(long value, double scale);

    static int choose(int n, StringBuilder trace) {
        try {
            switch (n) {
                case 2: return 11;
                case 3: return 13;
                default: return 17;
            }
        } finally {
            trace.append('B');
        }
    }
}

class Missing {}

public class Main {
    public static void main(String[] args) {
        StringBuilder trace = new StringBuilder();
        int total = First.choose(6, trace) + Second.choose(3, trace) + First.choose(-2, trace);
        System.out.println(total + ":" + trace);
    }
}
"#,
    )
    .unwrap();
    let classes = root.join("classes");
    run(Command::new(jdk_tool("javac"))
        .args(["--release", "17", "-g", "-d"])
        .arg(&classes)
        .arg(source));
    let input = root.join("methods.jar");
    let mut jar = zip::ZipWriter::new(fs::File::create(&input).unwrap());
    for entry in ["Second.class", "Main.class", "First.class"] {
        jar.start_file(entry, zip::write::SimpleFileOptions::default())
            .unwrap();
        std::io::copy(&mut fs::File::open(classes.join(entry)).unwrap(), &mut jar).unwrap();
    }
    jar.finish().unwrap();

    // The common CLI invocation uses just an input and a destination.
    let mut java_cli = Command::new(jdk_tool("java"));
    java_cli.arg("-jar").arg(upstream_jar());
    let java_default = root.join("java-default");
    let native_default = root.join("native-default");
    run(java_cli.arg(&input).arg(&java_default));
    run(Command::new(env!("CARGO_BIN_EXE_vineflower-rs"))
        .arg(&input)
        .arg(&native_default));
    assert_eq!(directory(&native_default), directory(&java_default));

    let options = [
        "--include-runtime=1",
        "--legacy-saving",
        "--bytecode-source-mapping=1",
        "--dump-code-lines=1",
        "--silent",
    ];
    let upstream = root.join("upstream");
    fs::create_dir(&upstream).unwrap();
    run(Command::new(jdk_tool("java"))
        .arg("-jar")
        .arg(upstream_jar())
        .arg("--thread-count=1")
        .args(options)
        .arg(&input)
        .arg(&upstream));
    let expected = archive(&upstream.join("methods.jar"));
    let sources = ["Second.java", "Main.java", "First.java"];
    for name in sources {
        assert!(!expected[name].2.is_empty(), "missing mapping for {name}");
    }

    let rebuilt_sources = root.join("rebuilt-sources");
    fs::create_dir(&rebuilt_sources).unwrap();
    for (name, count) in [
        ("default", None),
        ("one", Some("1")),
        ("two", Some("2")),
        ("auto", Some("0")),
        ("two-again", Some("2")),
    ] {
        let output = root.join(name);
        fs::create_dir(&output).unwrap();
        run(Command::new(env!("CARGO_BIN_EXE_vineflower-rs"))
            .args(count.map(|count| format!("--thread-count={count}")))
            .args(options)
            .arg(&input)
            .arg(&output));
        let output = output.join("methods.jar");
        let entries = zip::ZipArchive::new(fs::File::open(&output).unwrap()).unwrap();
        assert_eq!(entries.file_names().collect::<Vec<_>>(), sources, "{name}");
        let actual = archive(&output);
        assert_eq!(actual, expected, "{name}");
        if name == "default" {
            for name in sources {
                fs::write(rebuilt_sources.join(name), &actual[name].1).unwrap();
            }
        }
    }

    let dependency = root.join("dependency");
    fs::create_dir(&dependency).unwrap();
    fs::copy(
        classes.join("Missing.class"),
        dependency.join("Missing.class"),
    )
    .unwrap();
    let rebuilt = root.join("rebuilt");
    run(Command::new(jdk_tool("javac"))
        .arg("-cp")
        .arg(&dependency)
        .arg("-d")
        .arg(&rebuilt)
        .args(sources.map(|name| rebuilt_sources.join(name))));
    for output in [&classes, &rebuilt] {
        let classpath = std::env::join_paths([output, &dependency]).unwrap();
        let result = run(Command::new(jdk_tool("java"))
            .arg("-cp")
            .arg(classpath)
            .arg("Main"));
        assert_eq!(result.stdout, b"21:ABA\n");
    }
}

#[test]
#[ignore = "requires compiled upstream fixtures, the upstream +local.jar, and JDK 17 or later"]
fn parallel_stack_preparation_preserves_shared_class_access() {
    use std::io::Write;
    use upstream_reference::{Corpus, jdk_tool, run, upstream_jar};

    let scratch = tempfile::tempdir().unwrap();
    let root = scratch.path();
    let library = root.join("library");
    let annotated = root.join("TestCondy.java");
    fs::write(
        &annotated,
        "@Deprecated(since = \"1\", forRemoval = true) public class TestCondy {}",
    )
    .unwrap();
    compile_java17(&[&annotated], &library);

    let subject = root.join("WarningSubject.java");
    fs::write(
        &subject,
        r#"
package art;
public class WarningSubject {
    static int value = 1;
    public void call() { "a".length(); }
    public int branch(boolean a, boolean b) {
        if (a) {
            if (b) return 1;
        }
        return 0;
    }
}
"#,
    )
    .unwrap();
    let classes = root.join("classes");
    compile_java17(&[&subject], &classes);
    let subject = "art/WarningSubject.class";

    let fixtures = Corpus::discover().root;
    let fixture = |group: &str, entry: &'static str| {
        (entry, fs::read(fixtures.join(group).join(entry)).unwrap())
    };
    // Put the Condy method first so its import lookup first loads the annotated library.
    let mut entries = [
        fixture("jasm", "pkg/TestComplexCondy.class"),
        (subject, fs::read(classes.join(subject)).unwrap()),
        fixture("java25", "pkg/TestAssertInterface2.class"),
        fixture("java25", "pkg/TestAssertInterface2$1.class"),
        fixture("java25", "pkg/TestAssertInterface2$Interface.class"),
    ];
    let write_input = |name, entries: &[(&str, Vec<u8>)]| {
        let input = root.join(name);
        let mut jar = zip::ZipWriter::new(fs::File::create(&input).unwrap());
        for (entry, bytes) in entries {
            jar.start_file(*entry, zip::write::SimpleFileOptions::default())
                .unwrap();
            jar.write_all(bytes).unwrap();
        }
        jar.finish().unwrap();
        input
    };
    let valid = write_input("valid.jar", &entries);

    // Replace the first instruction of the five-byte <clinit> with tableswitch.
    // The class retains the Code attribute, and decoding the instruction fails.
    let code = &mut entries[1].1;
    let initializers = code
        .windows(15)
        .enumerate()
        .filter_map(|(index, bytes)| {
            matches!(
                bytes,
                [0, 1, 0, 0, 0, 0, 0, 5, 0x04, 0xb3, _, _, 0xb1, 0, 0]
            )
            .then_some(index + 8)
        })
        .collect::<Vec<_>>();
    let [opcode] = initializers.as_slice() else {
        panic!("expected one <clinit> with iconst_1, putstatic and return");
    };
    code[*opcode] = 0xaa;
    // Keep call()'s own descriptor valid. Expression lifting reads the broken String.length reference.
    replace_utf8_entry(code, "()I", "()Q");
    let malformed = write_input("malformed.jar", &entries);

    let options = [
        "--include-runtime=1",
        "--legacy-saving",
        "--bytecode-source-mapping=1",
        "--dump-code-lines=1",
        "--decompile-complex-constant-dynamic=1",
        "--log-level=INFO",
    ];
    let dependency = format!("-e={}", library.display());
    let upstream = root.join("upstream");
    fs::create_dir(&upstream).unwrap();
    run(Command::new(jdk_tool("java"))
        .arg("-jar")
        .arg(upstream_jar())
        .arg("--thread-count=1")
        .args(options)
        .arg(&dependency)
        .arg(&valid)
        .arg(&upstream));
    let expected = archive(&upstream.join("valid.jar"));
    for (name, source) in [
        ("pkg/TestComplexCondy.java", "pkg.TestCondy.class"),
        ("art/WarningSubject.java", "branch(boolean a, boolean b)"),
        ("pkg/TestAssertInterface2.java", "assert x > 10;"),
    ] {
        assert!(String::from_utf8_lossy(&expected[name].1).contains(source));
        assert!(!expected[name].2.is_empty(), "missing mapping for {name}");
    }

    let decompile = |input: &Path, count| {
        let name = input.file_name().unwrap();
        let output = root.join(count).join(name);
        fs::create_dir_all(&output).unwrap();
        let result = run(Command::new(env!("CARGO_BIN_EXE_vineflower-rs"))
            .arg(format!("--thread-count={count}"))
            .args(options)
            .arg(&dependency)
            .arg(input)
            .arg(&output));
        assert!(
            result.stderr.is_empty(),
            "{:?}",
            String::from_utf8_lossy(&result.stderr)
        );
        let jar = output.join(name);
        let entries = zip::ZipArchive::new(fs::File::open(&jar).unwrap()).unwrap();
        assert_eq!(
            entries.file_names().collect::<Vec<_>>(),
            [
                "pkg/",
                "art/",
                "pkg/TestComplexCondy.java",
                "art/WarningSubject.java",
                "pkg/TestAssertInterface2.java",
            ],
            "{name:?}, thread-count={count}"
        );
        (archive(&jar), String::from_utf8(result.stdout).unwrap())
    };

    // The malformed initializer has native diagnostics that differ from Java's.
    let damaged = decompile(&malformed, "1");
    assert!(damaged.1.contains("Invalid type: Q"));
    let diagnostics = [
        "Preprocessing class pkg/TestComplexCondy",
        "Loading Class: TestCondy from directory",
        "Preprocessing class art/WarningSubject",
        "Could not read method properties of art/WarningSubject.<clinit>",
        "Could not decompile art/WarningSubject.call ()V",
        "Could not decompile art/WarningSubject.<clinit>",
        "Preprocessing class pkg/TestAssertInterface2",
    ];
    assert_eq!(
        damaged
            .1
            .lines()
            .filter_map(|line| diagnostics
                .iter()
                .copied()
                .find(|message| line.contains(message)))
            .collect::<Vec<_>>(),
        diagnostics,
        "{}",
        damaged.1
    );
    for count in ["1", "2", "0"] {
        let (actual, log) = decompile(&valid, count);
        assert_eq!(actual, expected, "thread-count={count}");
        assert!(!log.contains("Could not read method properties"));
    }
    for count in ["2", "0"] {
        assert_eq!(
            decompile(&malformed, count),
            damaged,
            "thread-count={count}"
        );
    }
}

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn parallel_lambda_discovery_preserves_nested_call_sites_and_output() {
    use upstream_reference::{jdk_tool, run, upstream_jar};

    let scratch = tempfile::tempdir().unwrap();
    let root = scratch.path();
    let classes = root.join("classes");
    let source = root.join("Main.java");
    fs::write(
        &source,
        r#"
import java.util.function.IntSupplier;
import java.util.function.Supplier;

class Left {
    static Supplier<IntSupplier> make(int n) { return () -> () -> n + 1; }
}
class Right {
    static IntSupplier make(String s) { return s::length; }
}
public class Main {
    public static void main(String[] args) {
        System.out.println(Left.make(7).get().getAsInt() + Right.make("abcd").getAsInt());
    }
}
"#,
    )
    .unwrap();
    run(Command::new(jdk_tool("javac"))
        .args(["-g", "-d"])
        .arg(&classes)
        .arg(&source));
    let expected = root.join("upstream");
    fs::create_dir(&expected).unwrap();
    let flags = ["--include-runtime=1", "--folder", "--silent"];
    run(Command::new(jdk_tool("java"))
        .arg("-jar")
        .arg(upstream_jar())
        .arg("--thread-count=1")
        .args(flags)
        .arg(&classes)
        .arg(&expected));

    let cli = env!("CARGO_BIN_EXE_vineflower-rs");
    for count in ["1", "2", "0", "-1"] {
        let output = root.join(count);
        fs::create_dir(&output).unwrap();
        run(Command::new(cli)
            .arg(format!("-thr={count}"))
            .args(flags)
            .arg(&classes)
            .arg(&output));
        assert_eq!(
            directory(&output),
            directory(&expected),
            "thread-count={count}"
        );
    }

    let output = root.join("2");
    let rebuilt = root.join("rebuilt");
    run(Command::new(jdk_tool("javac"))
        .arg("-d")
        .arg(&rebuilt)
        .args(["Main.java", "Left.java", "Right.java"].map(|name| output.join(name))));
    for classpath in [&classes, &rebuilt] {
        let result = run(Command::new(jdk_tool("java"))
            .arg("-cp")
            .arg(classpath)
            .arg("Main"));
        assert_eq!(result.stdout, b"12\n");
    }
    let invalid = Command::new(cli)
        .arg("--thread-count=32768")
        .args(flags)
        .arg(&classes)
        .arg(root.join("invalid"))
        .output()
        .unwrap();
    assert!(!invalid.status.success());
    assert!(String::from_utf8_lossy(&invalid.stderr).contains("32767"));
}

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn native_cli_saving_and_configuration_match_upstream() {
    let scratch = tempfile::tempdir().unwrap();
    let root = scratch.path();
    let stdout = upstream_reference::Corpus::discover().run("DriverCliReference", &[], root);
    let binary = env!("CARGO_BIN_EXE_vineflower-rs");
    let config = root.join("args.cfg");
    let keyed = root.join("own/fixture/Subject.class");
    let library = format!("-e={}", root.join("library").display());

    let actual = Command::new(binary)
        .arg("--dump-text-tokens")
        .arg("-cfg")
        .arg(&config)
        .arg(&library)
        .arg(keyed)
        .output()
        .unwrap();
    assert!(
        actual.status.success(),
        "{}",
        String::from_utf8_lossy(&actual.stderr)
    );
    assert_eq!(String::from_utf8(actual.stdout).unwrap(), stdout);

    for (input, flag, output_name) in [
        ("own", "--file", "directory.jar"),
        ("source.jar", "--file", "archive.jar"),
        ("source.jar", "--legacy-saving", "legacy"),
        ("source.jar", "--folder", "folder"),
    ] {
        let output = root.join(output_name);
        let result = Command::new(binary)
            .arg("-cfg")
            .arg(&config)
            .arg(flag)
            .arg(&library)
            .arg(root.join(input))
            .arg(&output)
            .output()
            .unwrap();
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
        let expected = root.join("reference").join(output_name);
        if output_name == "folder" {
            assert_eq!(directory(&output), directory(&expected), "{output_name}");
        } else {
            let (output, expected) = if output_name == "legacy" {
                (output.join("source.jar"), expected.join("source.jar"))
            } else {
                (output, expected)
            };
            assert_eq!(archive(&output), archive(&expected), "{output_name}");
        }
    }
}

type Directory = BTreeMap<String, Option<Vec<u8>>>;

fn directory(root: &Path) -> Directory {
    fn read(root: &Path, current: &Path, entries: &mut Directory) {
        for entry in fs::read_dir(current).unwrap() {
            let entry = entry.unwrap();
            let path = entry.path();
            let name = path
                .strip_prefix(root)
                .unwrap()
                .to_string_lossy()
                .to_string();
            if path.is_dir() {
                entries.insert(name, None);
                read(root, &path, entries);
            } else {
                entries.insert(name, Some(fs::read(path).unwrap()));
            }
        }
    }
    let mut entries = Directory::new();
    read(root, root, &mut entries);
    entries
}

type Archive = BTreeMap<String, (bool, Vec<u8>, Vec<u8>)>;

fn archive(path: &Path) -> Archive {
    let mut zip = zip::ZipArchive::new(fs::File::open(path).unwrap()).unwrap();
    let mut entries = Archive::new();
    for index in 0..zip.len() {
        let mut entry = zip.by_index(index).unwrap();
        let mut bytes = Vec::new();
        entry.read_to_end(&mut bytes).unwrap();
        let extras = mapping_extra(entry.extra_data().unwrap_or_default()).to_vec();
        entries.insert(entry.name().to_owned(), (entry.is_dir(), bytes, extras));
    }
    entries
}

fn mapping_extra(mut bytes: &[u8]) -> &[u8] {
    while let Some(header) = bytes.get(..4) {
        let id = u16::from_le_bytes(header[..2].try_into().unwrap());
        let len = u16::from_le_bytes(header[2..].try_into().unwrap()) as usize;
        let Some(extra) = bytes.get(4..4 + len) else {
            break;
        };
        if id == 0x4646 {
            return extra;
        }
        bytes = &bytes[4 + len..];
    }
    &[]
}
