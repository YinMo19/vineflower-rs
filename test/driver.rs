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
                [(
                    "TestListIteratorHierarchy".into(),
                    include_bytes!("smoke/java8/TestListIteratorHierarchy.class").to_vec(),
                )],
            )))
            .unwrap();
        driver
            .add_library_context(Arc::new(LazyLibrary { before_read }))
            .unwrap();
        driver.decompile().unwrap().pop().unwrap().source
    };

    // Foreach recognition consults the iterator hierarchy during the method.
    // Delay that lookup so the test is independent of processor speed.
    let timed = decompile(1, false, |name| {
        if name == "java/util/ListIterator.class" {
            std::thread::sleep(Duration::from_millis(1100));
        }
    });
    assert_eq!(
        timed.matches("Couldn't be decompiled").count(),
        1,
        "{timed}"
    );
    assert!(timed.contains("Processing time limit exceeded"), "{timed}");
    let untimed = decompile(0, false, |_| {});
    assert!(untimed.contains("iterator.hasNext()"));
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

    let options = [
        "--thread-count=1",
        "--include-runtime=0",
        "--folder",
        "--silent",
    ];
    let upstream = upstream_jar();
    for (layout, inputs, enum_switch) in [
        ("holder-first", &["owner-first"][..], true),
        ("holder-last", &["consumer-first"][..], true),
        ("holder-unit-first", &["owner", "consumer"][..], true),
        ("holder-unit-last", &["consumer", "owner"][..], false),
    ] {
        let actual = root.join(format!("{layout}-native"));
        let expected = root.join(format!("{layout}-upstream"));
        fs::create_dir(&actual).unwrap();
        fs::create_dir(&expected).unwrap();
        let inputs = inputs.iter().map(|name| root.join(format!("{name}.jar")));
        run(Command::new(env!("CARGO_BIN_EXE_vineflower-rs"))
            .args(options)
            .args(inputs.clone())
            .arg(&actual));
        run(Command::new(jdk_tool("java"))
            .arg("-jar")
            .arg(&upstream)
            .args(options)
            .args(inputs)
            .arg(&expected));
        assert_eq!(directory(&actual), directory(&expected), "{layout}");
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
