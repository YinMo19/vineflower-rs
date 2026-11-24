// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use std::borrow::Cow;

use crate::{classfile::ClassFile, descriptor::{Primitive, Type as JvmType}};

use super::{Declaration, KotlinError, decompile_class, has_metadata, metadata::decode_payload,
    names::Names, proto::{StringRecord, StringTableTypes}, read_metadata};

// The Test* class files are upstream's Kotlin 2.0.0 Gradle fixtures, from
// tests/upstream/plugins/kotlin/testData/src/kt/pkg. The other class files
// come from this module's Kotlin sources (Kotlin 2.2.20, -jvm-target 1.8).
// Hex keeps the test class files usable without a JVM or an upstream build.
const CLASS: &str = include_str!("fixtures/Declaration.class.hex");
const FACADE: &str = include_str!("fixtures/DeclarationsKt.class.hex");
const CONTRACT: &str = include_str!("fixtures/Contract.class.hex");
const UNSUPPORTED: &str = include_str!("fixtures/Unsupported.class.hex");
const CONTROL: &str = include_str!("fixtures/Control.class.hex");
const COMPARE: &str = include_str!("fixtures/TestComparison.class.hex");
const BITWISE: &str = include_str!("fixtures/TestBitwiseFunctions.class.hex");

fn bytes(hex: &str) -> Vec<u8> {
    assert!(hex.lines().all(|line| line.len() % 2 == 0));
    hex.lines().flat_map(|line| (0..line.len()).step_by(2).map(move |index|
        u8::from_str_radix(&line[index..index + 2], 16).expect("compiled class hex"))).collect()
}

fn render(hex: &str) -> String {
    let bytes = bytes(hex);
    let class = ClassFile::parse(&bytes).unwrap();
    assert!(has_metadata(&class).unwrap());
    decompile_class(&class).unwrap().expect("Kotlin source")
}

#[test]
fn renders_class_from_kotlin_metadata_and_bytecode() {
    assert_eq!(render(CLASS), concat!(
        "package parity.kotlin\n\n",
        "public class Declaration(public val id: Int, public var active: Boolean) {\n",
        "   public val label: String = \"ok\"\n\n",
        "   public fun twice(x: Int): Int = x * 2\n",
        "}\n",
    ));
}

#[test]
fn renders_file_facade_without_a_jvm_wrapper_class() {
    assert_eq!(render(FACADE), concat!(
        "package parity.kotlin\n\n",
        "public const val answer: Int = 42\n",
        "public var visits: Int = 3\n",
        "public val note: String = \"cost \\$5\"\n\n",
        "public fun greet(): String = \"hi\"\n",
    ));
}

#[test]
fn renders_abstract_generic_and_extension_function_types() {
    assert_eq!(render(CONTRACT), concat!(
        "package parity.kotlin\n\n",
        "public interface Contract<T : Any> {\n",
        "   public val getter: Int.(String) -> Unit\n\n",
        "   public fun project(value: T?): List<T?>\n",
        "}\n",
    ));
}

#[test]
fn resolves_typed_jvm_member_signatures() {
    let bytes = bytes(CLASS);
    let class = ClassFile::parse(&bytes).unwrap();
    let metadata = read_metadata(&class).unwrap().unwrap();
    assert_eq!(metadata.header.version, [2, 2, 0]);
    let Declaration::Class(declaration) = metadata.declaration else { panic!("class metadata"); };
    assert_eq!(declaration.name.id, "parity/kotlin/Declaration");
    let active = declaration.members.properties.iter().find(|prop| prop.name == "active").unwrap();
    assert!(active.mutable());
    let getter = active.signature.getter.as_ref().unwrap();
    let setter = active.signature.setter.as_ref().unwrap();
    assert_eq!(getter.name, "getActive");
    assert_eq!(getter.descriptor.return_type, JvmType::Primitive(Primitive::Boolean));
    assert_eq!(setter.name, "setActive");
    assert_eq!(setter.descriptor.parameters, [JvmType::Primitive(Primitive::Boolean)]);
    let method = declaration.members.functions[0].signature.as_ref().unwrap();
    assert_eq!(method.name, "twice");
    assert_eq!(method.descriptor.parameters, [JvmType::Primitive(Primitive::Int)]);
}

#[test]
fn unsupported_method_returns_error_not_partial_kotlin_source() {
    let bytes = bytes(UNSUPPORTED);
    let class = ClassFile::parse(&bytes).unwrap();
    assert!(matches!(read_metadata(&class).unwrap().unwrap().declaration, Declaration::Class(_)));
    assert!(matches!(decompile_class(&class), Err(KotlinError::Unsupported {
        declaration, feature: "loop or backward control transfer"
    }) if declaration == "loop"));
}

#[test]
fn renders_value_joins_early_returns_and_short_circuit() {
    assert_eq!(render(CONTROL), concat!(
        "package parity.kotlin\n\n",
        "public class Control {\n",
        "   public fun branch(flag: Boolean): Int = if (flag) 1 else 2\n\n",
        "   public fun early(value: Int): Int = if (value == 0) 5 else value * 2\n\n",
        "   public fun shortCircuit(flag: Boolean, value: Int): Boolean = flag && 120 / value > 1\n\n",
        "   public fun wide(a: Long, b: Long): Boolean = a < b\n\n",
        "   public fun charEqual(value: Char): Boolean = value == 'Z'\n\n",
        "   public fun bit(value: Long, count: Int): Long = value ushr count\n\n",
        "   public fun directBoolean(a: Boolean, b: Boolean): Boolean = a xor b\n",
        "}\n",
    ));
}

#[test]
fn distinguishes_structural_identity_and_null_comparison() {
    assert_eq!(render(COMPARE), concat!(
        "package pkg\n\n",
        "public class TestComparison {\n",
        "   public fun test2(a: Any, b: Any): Boolean = a == b\n\n",
        "   public fun test3(a: Any, b: Any): Boolean = a === b\n\n",
        "   public fun testNull2(a: Any?): Boolean = a == null\n\n",
        "   public fun testNull3(a: Any?): Boolean = a == null\n\n",
        "   public fun testNullDouble2(a: Any?, b: Any?): Boolean = a == b\n\n",
        "   public fun testNullDouble3(a: Any?, b: Any?): Boolean = a === b\n",
        "}\n",
    ));
}

#[test]
fn renders_bitwise_operators_as_kotlin_infix_calls() {
    assert_eq!(render(BITWISE), concat!(
        "package pkg\n\n",
        "public class TestBitwiseFunctions {\n",
        "   public fun and(a: Int, b: Int): Int = a and b\n\n",
        "   public fun or(a: Int, b: Int): Int = a or b\n\n",
        "   public fun xor(a: Int, b: Int): Int = a xor b\n\n",
        "   public fun shl(a: Int, b: Int): Int = a shl b\n\n",
        "   public fun shr(a: Int, b: Int): Int = a shr b\n\n",
        "   public fun ushr(a: Int, b: Int): Int = a ushr b\n",
        "}\n",
    ));
}

#[test]
fn decodes_both_jvm_metadata_bit_encodings() {
    let raw = [Cow::Borrowed(&[0, 0x80][..]), Cow::Borrowed(&[0xff, 0][..])];
    let legacy = [Cow::Borrowed(&[0xffff, 1, 0][..]), Cow::Borrowed(&[4, 1][..])];
    let unmarked = [Cow::Borrowed(&[1, 0, 4, 1][..])];
    for chunks in [raw.as_slice(), legacy.as_slice(), unmarked.as_slice()] {
        assert_eq!(decode_payload(chunks).unwrap(), [0x80, 0xff, 0]);
    }
    assert!(decode_payload(&[Cow::Borrowed(&[0, 256])]).is_err());
    assert!(decode_payload(&[Cow::Borrowed(&[0xffff, 128])]).is_err());
}

#[test]
fn jvm_name_transforms_use_utf16_and_separate_substring_from_replacement() {
    let string = StringRecord { operation: Some(2), substring: vec![2, 17], replace: vec![i32::from(b'z'), i32::from(b'a')], ..Default::default() };
    let names = Names::new(StringTableTypes { records: vec![string], local_names: vec![0] }, vec!["😀Lpkg/A$Nestedz;discard"]).unwrap();
    let name = names.class(0).unwrap();
    assert_eq!(name.id, "pkg/A.Nesteda");
    assert!(name.local);
    assert!(names.text(1).is_err());
}
