// SPDX-License-Identifier: Apache-2.0

use std::{env, fmt::Write, path::PathBuf, sync::Arc};

use prost::Message;
use vineflower_rs::{
    engine::Options,
    kotlin::metadata::{self, Payload},
    structs::{StructContext, attr::ElementValue, consts::ConstantValue},
    util::java_str::JavaString,
};

use super::upstream_reference::Corpus;

#[test]
#[ignore = "requires the upstream Kotlin plugin, its compiled Kotlin fixtures, and JDK 17+"]
fn kotlin_metadata_matches_upstream() {
    let upstream = env::var_os("VINEFLOWER_UPSTREAM")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../vineflower"));
    let fixtures = upstream.join("plugins/kotlin/testData/classes");
    let expected = Corpus::discover().run_with_kotlin("KotlinMetadataReference", &[], &fixtures);
    let mut classes = StructContext::new(Arc::new(Options::default()), None);
    for directory in ["kt", "ktold"] {
        classes.add_file(&fixtures.join(directory), true).unwrap();
    }
    let mut classes = classes.get_own_classes();
    classes.sort_unstable_by(|a, b| a.qualified_name.cmp(&b.qualified_name));
    let mut actual = String::new();
    for example in [
        vec![],
        vec!["".into(), "abcdefgh".into()],
        vec![
            JavaString::from_utf16(vec![0, 0xd800, 0x01ff]),
            JavaString::from_utf16(vec![0xdc08]),
        ],
        vec![
            JavaString::from_utf16(vec![0xffff, 0x0081, 0x00ff, 0x0080, 0xfe00]),
            "XYZ".into(),
        ],
        vec!["abcdefg".into()],
        vec!["abcdefghijk".into(), "lmnopqrstuvwxyz".into()],
    ] {
        writeln!(actual, "bits|{}", hex(metadata::decode_bytes(&example))).unwrap();
    }
    let records = decode_hex(
        "0a04220200010a09220200012a030001580a08220200032a0203000a053203eda0800a04080118010a0608ffffffff0f0a0618ffffffff0f",
    );
    let names = metadata::NameResolver::new(
        metadata::proto::jvm::StringTableTypes::decode(records.as_slice()).unwrap(),
        ["abcd", "abcd", "abcd", "ignored", "A$B", "ignored"]
            .into_iter()
            .map(JavaString::from)
            .collect(),
    );
    for i in -1..7 {
        print_name(&mut actual, &names, i);
    }
    for class in classes {
        writeln!(actual, "class|{}", class.qualified_name).unwrap();
        for decompile in [false, true] {
            for export in [false, true] {
                let selected = metadata::select(&class, decompile, export);
                writeln!(actual, "choose|{}", selected.is_some_and(|s| s.decompile)).unwrap();
            }
        }
        if let Some(annotation) = metadata::metadata_annotation(&class)
            && let Some(index) = annotation.par_names.iter().position(|key| key == "k")
            && let ElementValue::Const {
                value: ConstantValue::Integer(kind),
                ..
            } = &annotation.par_values[index].value
        {
            writeln!(actual, "kind|{kind}").unwrap();
        }
        let parsed = match metadata::parse(&class) {
            Ok(Some(parsed)) => parsed,
            Ok(None) => {
                writeln!(actual, "none").unwrap();
                continue;
            }
            Err(_) => {
                writeln!(actual, "error").unwrap();
                continue;
            }
        };
        if let Some(names) = parsed.names {
            let table = names.string_table();
            wire(&mut actual, "table", table);
            for i in 0..table
                .record
                .iter()
                .map(|record| record.range().max(0))
                .sum()
            {
                print_name(&mut actual, &names, i);
            }
        }
        match parsed.payload {
            Payload::Class(value) => wire(&mut actual, "wire", &*value),
            Payload::File(value) => wire(&mut actual, "wire", &*value),
            Payload::Synthetic(value) => wire(&mut actual, "wire", &*value),
            Payload::MultifileFacade(parts) => {
                for part in parts {
                    writeln!(actual, "part|{}", units(&part)).unwrap();
                }
            }
            Payload::MultifilePart { package, facade } => {
                wire(&mut actual, "wire", &*package);
                writeln!(actual, "facade|{}", units(&facade)).unwrap();
            }
            Payload::FunctionReference => writeln!(actual, "reference").unwrap(),
        }
    }
    let mut class = "";
    for (i, (expected, actual)) in expected.lines().zip(actual.lines()).enumerate() {
        if let Some(name) = expected.strip_prefix("class|") {
            class = name;
        }
        assert_eq!(actual, expected, "{class} at line {}", i + 1);
    }
    assert_eq!(actual.lines().count(), expected.lines().count());
}

fn hex(bytes: Vec<u8>) -> String {
    let mut out = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        write!(out, "{byte:02x}").unwrap();
    }
    out
}

fn units(value: &JavaString) -> String {
    let mut out = String::new();
    for unit in value.utf16() {
        write!(out, "{unit:04x}").unwrap();
    }
    out
}

fn wire(out: &mut String, tag: &str, message: &impl Message) {
    writeln!(out, "{tag}|{}", hex(message.encode_to_vec())).unwrap();
}

fn decode_hex(hex: &str) -> Vec<u8> {
    hex.as_bytes()
        .chunks_exact(2)
        .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
        .collect()
}

fn print_name(out: &mut String, names: &metadata::NameResolver, index: i32) {
    match names.resolve(index) {
        Ok(value) => writeln!(out, "name|{}", units(&value)),
        Err(_) => writeln!(out, "name-error"),
    }
    .unwrap();
}
