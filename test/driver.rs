// SPDX-License-Identifier: Apache-2.0

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

#[allow(dead_code, reason = "the driver fixture compiles its own classes")]
#[path = "support/upstream_reference.rs"]
mod upstream_reference;

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

#[test]
#[ignore = "requires JDK 17 or later"]
fn generic_inner_class_and_loop_survive_recompilation() {
    use upstream_reference::{jdk_tool, run};

    let scratch = tempfile::tempdir().unwrap();
    let classes = scratch.path().join("classes");
    let output = scratch.path().join("output");
    let rebuilt = scratch.path().join("rebuilt");
    fs::create_dir(&output).unwrap();

    let compile = |source: &Path, dest: &Path| {
        run(Command::new(jdk_tool("javac"))
            .args(["--release", "17", "-g", "-d"])
            .arg(dest)
            .arg(source));
    };
    let execute = |dir: &Path| {
        run(Command::new(jdk_tool("java"))
            .arg("-cp")
            .arg(dir)
            .arg("Ledger"))
        .stdout
    };

    compile(Path::new("test/support/Ledger.java"), &classes);
    run(Command::new(env!("CARGO_BIN_EXE_vineflower-rs"))
        .args(["--include-runtime=0", "--silent", "--folder"])
        .arg(&classes)
        .arg(&output));
    compile(&output.join("Ledger.java"), &rebuilt);
    assert_eq!(execute(&classes), execute(&rebuilt));
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
        run(Command::new(jdk_tool("javac"))
            .args(["--release", "17", "-g", "-d"])
            .arg(dest)
            .arg(sources.join("Owner.java"))
            .arg(sources.join("Consumer.java")));
    };
    let execute = |dir: &Path| {
        run(Command::new(jdk_tool("java"))
            .arg("-cp")
            .arg(dir)
            .arg("Consumer"))
        .stdout
    };
    compile(root, &classes);
    let expected_execution = execute(&classes);
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
        ("owner-first", [owner.as_slice(), &consumer].concat()),
        ("consumer-first", [consumer.as_slice(), &owner].concat()),
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
        for count in [1, 2] {
            let actual = root.join(format!("{layout}-native-{count}"));
            fs::create_dir(&actual).unwrap();
            run(Command::new(env!("CARGO_BIN_EXE_vineflower-rs"))
                .arg(format!("--thread-count={count}"))
                .args(options)
                .args(inputs.clone())
                .arg(&actual));
            assert_eq!(
                directory(&actual),
                expected,
                "{layout}, thread-count={count}"
            );
        }
        let actual = root.join(format!("{layout}-native-2"));
        let source = fs::read_to_string(actual.join("Consumer.java")).unwrap();
        assert_eq!(source.contains("switch (mode)"), enum_switch, "{layout}");
        assert!(source.contains("owner.new Member(11)"), "{layout}");
        let rebuilt = root.join(format!("{layout}-rebuilt"));
        compile(&actual, &rebuilt);
        assert_eq!(execute(&rebuilt), expected_execution, "{layout}");
    }
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
        if name == "two" {
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
