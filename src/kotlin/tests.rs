// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use std::borrow::Cow;

use crate::{
    classfile::ClassFile,
    descriptor::{Primitive, Type as JvmType},
};

use super::{
    Declaration, KotlinError, decompile_class, has_metadata,
    metadata::decode_payload,
    names::Names,
    proto::{StringRecord, StringTableTypes},
    read_metadata,
};

// The Test* class files are upstream's Kotlin 2.0.0 Gradle fixtures, from
// tests/upstream/plugins/kotlin/testData/src/kt/pkg. The other class files
// come from this module's Kotlin sources (Kotlin 2.2.20, -jvm-target 1.8).
// ForLoops uses -jvm-target 17; TestForRange also requires the JVM 17
// fixture to exercise Kotlin's invokedynamic message on invalid step values.
// Hex keeps the test class files usable without a JVM or an upstream build.
const CLASS: &str = include_str!("fixtures/Declaration.class.hex");
const FACADE: &str = include_str!("fixtures/DeclarationsKt.class.hex");
const CONTRACT: &str = include_str!("fixtures/Contract.class.hex");
const UNSUPPORTED: &str = include_str!("fixtures/Unsupported.class.hex");
const CONTROL: &str = include_str!("fixtures/Control.class.hex");
const COMPARE: &str = include_str!("fixtures/TestComparison.class.hex");
const BITWISE: &str = include_str!("fixtures/TestBitwiseFunctions.class.hex");
const MULTIFILE: &str = include_str!("fixtures/TestMultifile.class.hex");
const PART_A: &str = include_str!("fixtures/TestMultifile__TestMultifileAKt.class.hex");
const PART_B: &str = include_str!("fixtures/TestMultifile__TestMultifileBKt.class.hex");
const DEFAULTS: &str = include_str!("fixtures/Defaults.class.hex");
const FACADE_DEFAULTS: &str = include_str!("fixtures/DefaultsKt.class.hex");
const UNSUPPORTED_DEFAULTS: &str = include_str!("fixtures/UnsupportedDefaults.class.hex");
const DATA_CLASS: &str = include_str!("fixtures/TestDataClass.class.hex");
const BRANCHES: &str = include_str!("fixtures/Branches.class.hex");
const WHEN_BOOLEAN: &str = include_str!("fixtures/TestWhenBoolean.class.hex");
const FOR_RANGE: &str = include_str!("fixtures/TestForRange.class.hex");
const FOR_LOOPS: &str = include_str!("fixtures/ForLoops.class.hex");

fn bytes(hex: &str) -> Vec<u8> {
    assert!(hex.lines().all(|line| line.len() % 2 == 0));
    hex.lines()
        .flat_map(|line| {
            (0..line.len()).step_by(2).map(move |index| {
                u8::from_str_radix(&line[index..index + 2], 16).expect("compiled class hex")
            })
        })
        .collect()
}

fn render(hex: &str) -> String {
    let bytes = bytes(hex);
    let class = ClassFile::parse(&bytes).unwrap();
    assert!(has_metadata(&class).unwrap());
    decompile_class(&class).unwrap().expect("Kotlin source")
}

#[test]
fn renders_class_from_kotlin_metadata_and_bytecode() {
    assert_eq!(
        render(CLASS),
        concat!(
            "package parity.kotlin\n\n",
            "public class Declaration(public val id: Int, public var active: Boolean) {\n",
            "   public val label: String = \"ok\"\n\n",
            "   public fun twice(x: Int): Int = x * 2\n",
            "}\n",
        )
    );
}

#[test]
fn renders_file_facade_without_a_jvm_wrapper_class() {
    assert_eq!(
        render(FACADE),
        concat!(
            "package parity.kotlin\n\n",
            "public const val answer: Int = 42\n",
            "public var visits: Int = 3\n",
            "public val note: String = \"cost \\$5\"\n\n",
            "public fun greet(): String = \"hi\"\n",
        )
    );
}

#[test]
fn renders_abstract_generic_and_extension_function_types() {
    assert_eq!(
        render(CONTRACT),
        concat!(
            "package parity.kotlin\n\n",
            "public interface Contract<T : Any> {\n",
            "   public val getter: Int.(String) -> Unit\n\n",
            "   public fun project(value: T?): List<T?>\n",
            "}\n",
        )
    );
}

#[test]
fn resolves_typed_jvm_member_signatures() {
    let bytes = bytes(CLASS);
    let class = ClassFile::parse(&bytes).unwrap();
    let metadata = read_metadata(&class).unwrap().unwrap();
    assert_eq!(metadata.header.version, [2, 2, 0]);
    let Declaration::Class(declaration) = metadata.declaration else {
        panic!("class metadata");
    };
    assert_eq!(declaration.name.id, "parity/kotlin/Declaration");
    let active = declaration
        .members
        .properties
        .iter()
        .find(|prop| prop.name == "active")
        .unwrap();
    assert!(active.mutable());
    let getter = active.signature.getter.as_ref().unwrap();
    let setter = active.signature.setter.as_ref().unwrap();
    assert_eq!(getter.name, "getActive");
    assert_eq!(
        getter.descriptor.return_type,
        JvmType::Primitive(Primitive::Boolean)
    );
    assert_eq!(setter.name, "setActive");
    assert_eq!(
        setter.descriptor.parameters,
        [JvmType::Primitive(Primitive::Boolean)]
    );
    let method = declaration.members.functions[0].signature.as_ref().unwrap();
    assert_eq!(method.name, "twice");
    assert_eq!(
        method.descriptor.parameters,
        [JvmType::Primitive(Primitive::Int)]
    );
}

#[test]
fn unsupported_method_returns_error_not_partial_kotlin_source() {
    let bytes = bytes(UNSUPPORTED);
    let class = ClassFile::parse(&bytes).unwrap();
    assert!(matches!(
        read_metadata(&class).unwrap().unwrap().declaration,
        Declaration::Class(_)
    ));
    assert!(
        matches!(decompile_class(&class), Err(KotlinError::Unsupported {
        declaration, feature: "loop or backward control transfer"
    }) if declaration == "loop")
    );
}

#[test]
fn renders_value_joins_early_returns_and_short_circuit() {
    assert_eq!(
        render(CONTROL),
        concat!(
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
        )
    );
}

#[test]
fn recovers_switch_groups_joined_values_and_typed_when_predicates() {
    let source = render(BRANCHES);
    assert!(
        source.contains(concat!(
            "   public fun lookup(key: Int): String {\n",
            "      return when (key) {\n",
            "         -20 -> \"left\"\n",
            "         7, 1024 -> \"right\"\n",
            "         else -> \"center\"\n",
        )),
        "{source}"
    );
    assert!(
        source.contains(concat!(
            "   public fun table(key: Int) {\n",
            "      when (key) {\n",
            "         1 -> System.out.println(\"one\")\n",
            "         2, 3 -> System.out.println(\"two or three\")\n",
            "         else -> System.out.println(\"default\")\n",
        )),
        "{source}"
    );
    assert!(
        source.contains(concat!(
            "      val text: String = when (key) {\n",
            "         1 -> \"one\"\n",
            "         2, 3, 5 -> \"some prime\"\n",
            "         else -> \"anything else\"\n",
            "      }\n",
            "      System.out.println(text)\n",
        )),
        "{source}"
    );
    assert!(
        source.contains(concat!(
            "      when {\n",
            "         value == 7 -> System.out.println(\"seven\")\n",
            "         value == null -> System.out.println(\"nothing\")\n",
            "         value is kotlin.String -> System.out.println(\"string\")\n",
            "         value !is kotlin.Long -> System.out.println(\"not long\")\n",
            "         else -> System.out.println(\"long\")\n",
        )),
        "{source}"
    );
}

#[test]
fn recovers_upstream_boolean_decision_graph_with_mapped_call() {
    let options = crate::Options {
        decompile_kotlin: true,
        include_line_mappings: true,
        ..crate::Options::default()
    };
    let source = crate::decompile(&bytes(WHEN_BOOLEAN), &options).unwrap();
    assert!(source.text.contains("      when {\n"));
    assert!(source.text.contains(" -> System.out.println(\"hello\")"));
    assert_eq!(source.text.matches("System.out.println").count(), 1);
    let map = source.map.unwrap();
    let [method] = map.methods.as_slice() else {
        panic!("expected one mapped method");
    };
    assert_eq!(method.name, "testIf");
    let call_line = source
        .text
        .lines()
        .position(|line| line.contains("System.out.println"))
        .unwrap();
    assert_eq!(method.offsets[&170], call_line);
    assert_eq!(method.offsets[&172], call_line);
    assert!(method.offsets[&173] > call_line);
}

#[test]
fn renders_counted_ranges_and_stepped_progressions() {
    let options = crate::Options {
        decompile_kotlin: true,
        include_line_mappings: true,
        ..crate::Options::default()
    };
    let source = crate::decompile(&bytes(FOR_RANGE), &options).unwrap();
    for (signature, binding, range) in [
        ("testInt()", "i", "1..10"),
        ("testChar()", "c", "'a'..'z'"),
        ("testIntStep()", "i", "1..10 step 2"),
        ("testIntStepX(x: Int)", "i", "1..100 step x"),
        ("testIntDownTo()", "i", "10 downTo 1"),
        ("testIntDownToStep()", "i", "10 downTo 1 step 2"),
        ("testIntDownToStepX(x: Int)", "i", "100 downTo 1 step x"),
        ("testUntil()", "i", "1..9"),
        ("testUntilStep()", "i", "1 until 100 step 2"),
        ("testUntilStepX(x: Int)", "i", "1 until 100 step x"),
        ("testIntY(x: Int, y: Int)", "i", "x..y"),
        ("testIntYStep(x: Int, y: Int)", "i", "x..y step 2"),
        ("testIntYStepX(x: Int, y: Int, z: Int)", "i", "x..y step z"),
    ] {
        assert!(
            source.text.contains(&format!(
                "   public fun {signature} {{\n      for ({binding} in {range}) {{\n         System.out.println({binding})\n      }}\n   }}"
            )),
            "{signature} in {}",
            source.text
        );
    }
    assert_eq!(source.text.matches("      for (").count(), 13);
    let map = source.map.unwrap();
    let method = map.methods.iter().find(|method| method.name == "testInt").unwrap();
    let mut lines = source.text.lines();
    assert_eq!(lines.nth(method.offsets[&5]), Some("      for (i in 1..10) {"));
    assert_eq!(lines.next(), Some("         System.out.println(i)"));
    assert_eq!(method.offsets[&12], method.offsets[&5] + 1);
    assert_eq!(method.offsets[&17], method.offsets[&5]);
    assert_eq!(method.offsets[&21], method.offsets[&5] + 3);
}

#[test]
fn renders_generic_iterator_elements_and_variable_exclusive_bound() {
    assert_eq!(
        render(FOR_LOOPS),
        concat!(
            "package parity.kotlin\n\n",
            "public class ForLoops {\n",
            "   public fun list(words: List<String>) {\n",
            "      for (word in words) {\n",
            "         System.out.println(word as kotlin.Any?)\n",
            "      }\n",
            "   }\n\n",
            "   public fun numbers(values: Iterable<Int>) {\n",
            "      for (value in values) {\n",
            "         System.out.println(value + 1)\n",
            "      }\n",
            "   }\n\n",
            "   public fun untilBound(end: Int) {\n",
            "      for (index in 0 until end) {\n",
            "         System.out.println(index)\n",
            "      }\n",
            "   }\n",
            "}\n",
        )
    );
}

#[test]
fn rejects_wrong_progression_exit_and_iterator_slot_alias() {
    for (fixture, name, offset, from, to) in [
        (FOR_RANGE, "testIntY", 4, 0xa3, 0xa2),
        (FOR_LOOPS, "list", 31, 0x4e, 0x4d),
    ] {
        let mut class_bytes = bytes(fixture);
        let start = {
            let class = ClassFile::parse(&class_bytes).unwrap();
            let method = class.methods.iter().find(|method| {
                class.pool.utf8(method.name_index).unwrap() == name
            }).unwrap();
            let code = method.code(&class.pool).unwrap().unwrap();
            assert_eq!(code.bytes[offset], from);
            code.bytes.as_ptr() as usize - class_bytes.as_ptr() as usize
        };
        class_bytes[start + offset] = to;
        let class = ClassFile::parse(&class_bytes).unwrap();
        assert!(matches!(decompile_class(&class), Err(KotlinError::Unsupported {
            declaration, feature: "loop or backward control transfer"
        }) if declaration == name));
    }
}

#[test]
fn distinguishes_structural_identity_and_null_comparison() {
    assert_eq!(
        render(COMPARE),
        concat!(
            "package pkg\n\n",
            "public class TestComparison {\n",
            "   public fun test2(a: Any, b: Any): Boolean = a == b\n\n",
            "   public fun test3(a: Any, b: Any): Boolean = a === b\n\n",
            "   public fun testNull2(a: Any?): Boolean = a == null\n\n",
            "   public fun testNull3(a: Any?): Boolean = a == null\n\n",
            "   public fun testNullDouble2(a: Any?, b: Any?): Boolean = a == b\n\n",
            "   public fun testNullDouble3(a: Any?, b: Any?): Boolean = a === b\n",
            "}\n",
        )
    );
}

#[test]
fn renders_bitwise_operators_as_kotlin_infix_calls() {
    assert_eq!(
        render(BITWISE),
        concat!(
            "package pkg\n\n",
            "public class TestBitwiseFunctions {\n",
            "   public fun and(a: Int, b: Int): Int = a and b\n\n",
            "   public fun or(a: Int, b: Int): Int = a or b\n\n",
            "   public fun xor(a: Int, b: Int): Int = a xor b\n\n",
            "   public fun shl(a: Int, b: Int): Int = a shl b\n\n",
            "   public fun shr(a: Int, b: Int): Int = a shr b\n\n",
            "   public fun ushr(a: Int, b: Int): Int = a ushr b\n",
            "}\n",
        )
    );
}

#[test]
fn decompiles_multifile_parts_and_optional_wrappers_exactly() {
    use crate::{Options, context::ClassGroup};

    let (facade, part_a, part_b) = (bytes(MULTIFILE), bytes(PART_A), bytes(PART_B));
    let group = ClassGroup::new([facade.as_slice(), part_a.as_slice(), part_b.as_slice()]).unwrap();
    let mut options = Options::default();
    options.decompile_kotlin = true;
    let default = group.decompile("pkg/TestMultifile", &options).unwrap();
    assert_eq!(default.file_extension, "kt");
    assert_eq!(
        default.text,
        concat!(
            "package pkg\n\n",
            "/*\n * This is a multifile facade. The actual implementations of the functions are in the following files:\n",
            " * pkg/TestMultifile__TestMultifileAKt\n",
            " * pkg/TestMultifile__TestMultifileBKt\n",
            " */\n",
        )
    );

    options.set("kt-decompile-facades", "1").unwrap();
    options.include_line_mappings = true;
    options.dump_original_lines = true;
    options.unit_test_mode = true;
    options.remove_synthetic = false;
    for (name, golden) in [
        (
            "pkg/TestMultifile",
            include_str!(
                "../../tests/upstream/plugins/kotlin/testData/results/pkg/TestMultifile.dec"
            ),
        ),
        (
            "pkg/TestMultifile__TestMultifileAKt",
            include_str!(
                "../../tests/upstream/plugins/kotlin/testData/results/pkg/TestMultifile__TestMultifileA.dec"
            ),
        ),
        (
            "pkg/TestMultifile__TestMultifileBKt",
            include_str!(
                "../../tests/upstream/plugins/kotlin/testData/results/pkg/TestMultifile__TestMultifileB.dec"
            ),
        ),
    ] {
        let source = group.decompile(name, &options).unwrap();
        assert_eq!(source.file_extension, "kt");
        assert_eq!(source.text, golden, "{name}");
    }
}

#[test]
fn renders_mapped_comparisons_and_bitwise_returns_exactly() {
    let mut options = crate::Options::default();
    options.decompile_kotlin = true;
    options.include_line_mappings = true;
    options.dump_original_lines = true;
    options.unit_test_mode = true;
    options.remove_synthetic = false;
    for (fixture, golden) in [
        (
            COMPARE,
            include_str!(
                "../../tests/upstream/plugins/kotlin/testData/results/pkg/TestComparison.dec"
            ),
        ),
        (
            BITWISE,
            include_str!(
                "../../tests/upstream/plugins/kotlin/testData/results/pkg/TestBitwiseFunctions.dec"
            ),
        ),
    ] {
        let source = crate::decompile(&bytes(fixture), &options).unwrap();
        assert_eq!(source.text, golden, "{}", source.class_name);
    }
}

#[test]
fn recovers_primary_data_properties_and_checked_masked_defaults() {
    assert_eq!(
        render(DEFAULTS),
        concat!(
            "package parity.kotlin\n\n",
            "public data class Defaults(val title: String = \"hello\", var count: Int = 7, val active: Boolean = true) {\n",
            "   public fun amount(base: Int = 3, scale: Int = 2): Int = base * scale\n\n",
            "   public fun indirect(base: Int, amount: Int = base * 2): Int = amount\n",
            "}\n",
        )
    );
    assert_eq!(
        render(FACADE_DEFAULTS),
        concat!(
            "package parity.kotlin\n\n",
            "public fun withDefaults(required: Int, first: Long = 4L, second: Long = first): Long = first + second\n",
        )
    );
    assert_eq!(
        render(DATA_CLASS),
        concat!(
            "package pkg\n\n",
            "public data class TestDataClass(val dataClassVal: Regex, val variableWithVeryLongName: Int, ",
            "val requestLineWrapsIfTheParamListIsTooLong: List<String>, val nullability: String?)\n",
        )
    );
}

#[test]
fn rejects_default_expressions_that_require_unsupported_invocations() {
    let class_bytes = bytes(UNSUPPORTED_DEFAULTS);
    let class = ClassFile::parse(&class_bytes).unwrap();
    assert!(
        matches!(decompile_class(&class), Err(KotlinError::Unsupported { declaration, .. })
        if declaration == "parity/kotlin/UnsupportedDefaults")
    );
}

#[test]
fn decodes_both_jvm_metadata_bit_encodings() {
    let raw = [Cow::Borrowed(&[0, 0x80][..]), Cow::Borrowed(&[0xff, 0][..])];
    let legacy = [
        Cow::Borrowed(&[0xffff, 1, 0][..]),
        Cow::Borrowed(&[4, 1][..]),
    ];
    let unmarked = [Cow::Borrowed(&[1, 0, 4, 1][..])];
    for chunks in [raw.as_slice(), legacy.as_slice(), unmarked.as_slice()] {
        assert_eq!(decode_payload(chunks).unwrap(), [0x80, 0xff, 0]);
    }
    assert!(decode_payload(&[Cow::Borrowed(&[0, 256])]).is_err());
    assert!(decode_payload(&[Cow::Borrowed(&[0xffff, 128])]).is_err());
}

#[test]
fn jvm_name_transforms_use_utf16_and_separate_substring_from_replacement() {
    let string = StringRecord {
        operation: Some(2),
        substring: vec![2, 17],
        replace: vec![i32::from(b'z'), i32::from(b'a')],
        ..Default::default()
    };
    let names = Names::new(
        StringTableTypes {
            records: vec![string],
            local_names: vec![0],
        },
        vec!["😀Lpkg/A$Nestedz;discard"],
    )
    .unwrap();
    let name = names.class(0).unwrap();
    assert_eq!(name.id, "pkg/A.Nesteda");
    assert!(name.local);
    assert!(names.text(1).is_err());
}
