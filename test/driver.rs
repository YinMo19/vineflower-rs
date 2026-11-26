// SPDX-License-Identifier: Apache-2.0

use std::{collections::BTreeMap, fs, io::Read, path::Path, process::Command, sync::Arc};

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
    driver.add_library_context(Arc::new(LazyLibrary)).unwrap();
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

struct LazyLibrary;

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
        Ok((resource == "ext/TestLibrary.class")
            .then(|| include_bytes!("smoke/java8/TestLibrary.class").to_vec()))
    }
}

struct Documentation;

impl JavadocProvider for Documentation {
    fn class_doc(&self, _class: &StructClass) -> Option<String> {
        Some("Driver documentation".into())
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
