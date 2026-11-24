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
// Extensions uses Kotlin 2.0.0 with the same JVM target.
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
const TRY_REGIONS: &str = include_str!("fixtures/TryRegions.class.hex");
const TRY_THROWABLE: &str = include_str!("fixtures/TestTryCatchThrowable.class.hex");
pub(super) const INDY_TEMPLATE: &str = include_str!("fixtures/TestStringInterpolation.class.hex");
const CLASSIC_TEMPLATE: &str = include_str!("fixtures/TestClassicStringInterpolation.class.hex");
const OBJECT: &str = include_str!("fixtures/TestObject.class.hex");
const COMPANION_HOST: &str = include_str!("fixtures/TestCompanionObject.class.hex");
const COMPANION_CHILD: &str = include_str!("fixtures/TestCompanionObject$Companion.class.hex");
const NESTING: [&str; 4] = [
    include_str!("fixtures/Nesting.class.hex"),
    include_str!("fixtures/Nesting$Factory.class.hex"),
    include_str!("fixtures/Nesting$Payload.class.hex"),
    include_str!("fixtures/Nesting$Settings.class.hex"),
];
const EXTENSIONS: [&str; 3] = [
    include_str!("fixtures/Extensions.class.hex"),
    include_str!("fixtures/Extensions$Point.class.hex"),
    include_str!("fixtures/ExtensionsKt.class.hex"),
];

pub(super) fn bytes(hex: &str) -> Vec<u8> {
    assert!(hex.lines().all(|line| line.len() % 2 == 0));
    hex.lines()
        .flat_map(|line| {
            (0..line.len()).step_by(2).map(move |index| {
                u8::from_str_radix(&line[index..index + 2], 16).expect("compiled class hex")
            })
        })
        .collect()
}

#[test]
fn recovers_member_and_file_extension_receivers_with_mappings() {
    let classes = EXTENSIONS.map(bytes);
    let group = crate::ClassGroup::new(classes.iter().map(Vec::as_slice)).unwrap();
    let options = crate::Options { decompile_kotlin: true, ..crate::Options::default() };
    let mapped_options = crate::Options {
        include_line_mappings: true,
        ..options.clone()
    };
    for (class, cases) in [
        ("parity/kotlin/Extensions", [
            ("dot", "(Lparity/kotlin/Extensions$Point;Lparity/kotlin/Extensions$Point;)I",
                "fun parity.kotlin.Extensions.Point.dot(other: parity.kotlin.Extensions.Point): Int",
                "this.x * other.x + this.y * other.y", 12),
            ("own", "(Lparity/kotlin/Extensions;Lparity/kotlin/Extensions;)I",
                "fun Extensions.own(other: Extensions): Int", "this.x + other.x", 12),
            ("shift", "(JIJ)J", "fun Long.shift(bits: Int, delta: Long): Long",
                "(this shl bits) + delta", 0),
        ].as_slice()),
        ("parity/kotlin/ExtensionsKt", [
            ("describe", "(Lparity/kotlin/Extensions$Point;Lparity/kotlin/Extensions$Point;)Ljava/lang/String;",
                "fun Extensions.Point.describe(other: Extensions.Point): String", "other.label", 12),
            ("echo", "(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;",
                "fun String.echo(other: String): String", "this", 12),
            ("echoNullable", "(Ljava/lang/String;Ljava/lang/String;)Ljava/lang/String;",
                "fun (String?).echoNullable(other: String?): String?", "this", 0),
            ("offset", "(DD)D", "fun Double.offset(delta: Double): Double", "this - delta", 0),
        ].as_slice()),
    ] {
        let source = group.decompile(class, &options).unwrap();
        let mapped = group.decompile(class, &mapped_options).unwrap();
        let map = mapped.map.unwrap();
        for &(name, descriptor, declaration, expression, start) in cases {
            let expected = format!("{declaration} = {expression}");
            assert!(source.text.contains(expected.as_str()), "missing {expected} in {}", source.text);
            let method = map.methods.iter().find(|method| method.name == name).unwrap();
            assert_eq!(method.class_name, class);
            assert_eq!(method.descriptor, descriptor);
            assert_eq!(method.offsets.keys().next(), Some(&start));
            let member_name = format!(".{name}(");
            let original = include_str!("fixtures/Extensions.kt").lines()
                .position(|line| line.contains(member_name.as_str())).unwrap() + 1;
            let target = method.offsets[&start];
            assert_eq!(map.original_lines.get(&(original as u16)), Some(&(target + 1)));
            assert_eq!(
                mapped.text.lines().nth(target).unwrap().trim_start(),
                format!("return {expression}"),
            );
        }
    }
}

#[test]
fn rejects_unproven_extension_getters_and_wrong_receiver_slots() {
    let [host, point, file] = EXTENSIONS.map(bytes);
    let options = crate::Options { decompile_kotlin: true, ..crate::Options::default() };
    let facade = "parity/kotlin/ExtensionsKt";
    let owner = "parity/kotlin/Extensions";

    let mut java_like_point = point.clone();
    let annotation = b"Lkotlin/Metadata;";
    let start = java_like_point.windows(annotation.len()).position(|window| window == annotation).unwrap();
    java_like_point[start..start + annotation.len()].copy_from_slice(b"Lkotlin/Xetadata;");
    for library in [None, Some(java_like_point.as_slice())] {
        let group = crate::ClassGroup::new([file.as_slice()].into_iter().chain(library)).unwrap();
        assert!(matches!(
            group.decompile(facade, &options),
            Err(crate::DecompileError::Kotlin(KotlinError::Unsupported { declaration, .. }))
                if declaration == "describe"
        ));
    }

    for (mut input, method, offset, from, to, class, expected) in [
        (file, "echo", 0, 0x2a, 0x2b, facade, "unproven Kotlin extension parameter null guard"),
        (host.clone(), "own", 12, 0x2b, 0x2a, owner, "bytecode outside the supported expression subset"),
        (host, "shift", 1, 0x1d, 0x1c, owner, "load of non-parameter local"),
    ] {
        let index = {
            let parsed = ClassFile::parse(&input).unwrap();
            let member = parsed.methods.iter().find(|member| {
                parsed.pool.utf8(member.name_index).unwrap() == method
            }).unwrap();
            let code = member.code(&parsed.pool).unwrap().unwrap();
            assert_eq!(code.bytes[offset], from);
            code.bytes.as_ptr() as usize - input.as_ptr() as usize + offset
        };
        input[index] = to;
        let group = crate::ClassGroup::new([input.as_slice(), point.as_slice()]).unwrap();
        assert!(matches!(
            group.decompile(class, &options),
            Err(crate::DecompileError::Kotlin(KotlinError::Unsupported { declaration, feature }))
                if declaration == method && feature == expected
        ));
    }
}

#[test]
fn renders_original_indy_and_classic_templates_with_mappings() {
    let options = crate::Options {
        decompile_kotlin: true,
        include_line_mappings: true,
        dump_original_lines: true,
        unit_test_mode: true,
        remove_synthetic: false,
        ..crate::Options::default()
    };
    for (fixture, golden) in [
        (
            INDY_TEMPLATE,
            include_str!("../../tests/upstream/plugins/kotlin/testData/results/pkg/TestStringInterpolation.dec"),
        ),
        (
            CLASSIC_TEMPLATE,
            include_str!("../../tests/upstream/plugins/kotlin/testData/results/pkg/TestClassicStringInterpolation.dec"),
        ),
    ] {
        let source = crate::decompile(&bytes(fixture), &options).unwrap();
        assert_eq!(source.text, golden, "{}", source.class_name);
    }
}

#[test]
fn braces_interpolation_names_before_literal_identifier_characters() {
    for (fixture, old, new) in [
        (INDY_TEMPLATE, b"\x01 5".as_slice(), b"\x01a$".as_slice()),
        (CLASSIC_TEMPLATE, b"\x01\x00\x02 5", b"\x01\x00\x02a$"),
    ] {
        let mut data = bytes(fixture);
        let start = data.windows(old.len()).position(|window| window == old).unwrap();
        data[start..start + old.len()].copy_from_slice(new);
        let class = ClassFile::parse(&data).unwrap();
        let source = decompile_class(&class).unwrap().expect("Kotlin source");
        assert!(source.contains(r#"System.out.println("${x}a\$")"#), "{source}");
    }
}

#[test]
fn rejects_unmatched_concat_recipe_and_wrong_append_overload() {
    for (fixture, old, new) in [
        (INDY_TEMPLATE, b"\x01 \x01".as_slice(), b"\x01 !".as_slice()),
        (CLASSIC_TEMPLATE, b"(C)Ljava/lang/StringBuilder;", b"(Z)Ljava/lang/StringBuilder;"),
        (
            INDY_TEMPLATE,
            b"(ILjava/lang/String;)Ljava/lang/String;",
            b"(ILjava/lang/Double;)Ljava/lang/String;",
        ),
    ] {
        let mut data = bytes(fixture);
        let start = data.windows(old.len()).position(|window| window == old).unwrap();
        data[start..start + old.len()].copy_from_slice(new);
        let class = ClassFile::parse(&data).unwrap();
        assert!(matches!(
            decompile_class(&class),
            Err(KotlinError::Unsupported { declaration, .. }) if declaration == "stringInterpolation"
        ));
    }
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
            "   public final val label: String = \"ok\"\n\n",
            "   public fun twice(x: Int): Int = x * 2\n",
            "}\n",
        )
    );
}

#[test]
fn restores_jvm_default_fields_without_claiming_a_constructor_store() {
    let input = bytes(include_str!("fixtures/FieldDefaults.class.hex"));
    let options = crate::Options {
        decompile_kotlin: true,
        include_line_mappings: true,
        ..crate::Options::default()
    };
    let recovered = crate::decompile(&input, &options).unwrap();
    for declaration in [
        "   public final val disabled: Boolean = false",
        "   public final var empty: Long = 0L",
        "   public final val absent: String? = null",
    ] {
        assert!(recovered.text.lines().any(|line| line == declaration));
    }
    let map = recovered.map.unwrap();
    let constructor = map.methods.iter().find(|entry| entry.name == "<init>").unwrap();
    assert_eq!(constructor.offsets.keys().copied().collect::<Vec<_>>(), [5, 6]);
    for &line in constructor.offsets.values() {
        assert_eq!(
            recovered.text.lines().nth(line),
            Some("   public final val literal: Int = 7"),
        );
    }
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
fn recovers_ordered_and_nested_throwable_handlers() {
    let source = render(TRY_THROWABLE);
    for fragment in [
        concat!(
            "   public fun testEmptyCatch() {\n",
            "      try {\n",
            "         System.out.println(\"Hi\")\n",
            "      } catch (caught1: kotlin.Throwable) {\n",
            "      }\n",
            "   }\n",
        ),
        concat!(
            "   public fun testCatchWithReturnAndTail(): String? {\n",
            "      try {\n",
            "         System.out.println(\"Hi\")\n",
            "      } catch (ignored: kotlin.Throwable) {\n",
            "         return null\n",
            "      }\n\n",
            "      System.out.println(\"Ho\")\n",
            "      return \"bye\"\n",
            "   }\n",
        ),
        concat!(
            "      } catch (ignored: kotlin.Throwable) {\n",
            "         try {\n",
            "            System.out.println(\"Hi!\")\n",
            "            return \"5\"\n",
            "         } catch (throwable: kotlin.Throwable) {\n",
            "            return throwable.message\n",
            "         }\n",
            "      }\n",
        ),
        concat!(
            "      } catch (throwable: kotlin.Throwable) {\n",
            "         System.out.println(\"Oh no\")\n",
            "         throw throwable\n",
            "      }\n",
        ),
        concat!(
            "      } catch (ignored: kotlin.RuntimeException) {\n",
            "         System.out.println(\"Hello\")\n",
            "      } catch (ignored: kotlin.Throwable) {\n",
            "         System.out.println(\"Oh no\")\n",
            "      }\n",
        ),
    ] {
        assert!(source.contains(fragment), "missing {fragment:?} in {source}");
    }
    assert_eq!(source.matches(" catch (").count(), 11);
}

#[test]
fn renders_try_value_joins_and_proves_cleanup_return_order() {
    let options = crate::Options {
        decompile_kotlin: true,
        include_line_mappings: true,
        ..crate::Options::default()
    };
    let source = crate::decompile(&bytes(TRY_REGIONS), &options).unwrap();
    for fragment in [
        concat!(
            "   public fun divide(value: Int): Int {\n",
            "      return try {\n",
            "         100 / value\n",
            "      } catch (failure: kotlin.ArithmeticException) {\n",
            "         System.out.println(failure)\n",
            "         -1\n",
            "      }\n",
            "   }\n",
        ),
        concat!(
            "   public fun divideAndClean(value: Int): Int {\n",
            "      return try {\n",
            "         100 / value\n",
            "      } catch (failure: kotlin.ArithmeticException) {\n",
            "         System.out.println(failure)\n",
            "         -1\n",
            "      } finally {\n",
            "         System.out.println(\"cleanup\")\n",
            "      }\n",
            "   }\n",
        ),
        concat!(
            "   public fun returnAndClean(value: Int): Int {\n",
            "      return try {\n",
            "         100 / value\n",
            "      } finally {\n",
            "         System.out.println(\"cleanup\")\n",
            "      }\n",
            "   }\n",
        ),
        concat!(
            "   public fun cleanupThenTail(value: Int) {\n",
            "      try {\n",
            "         System.out.println(value)\n",
            "      } finally {\n",
            "         System.out.println(\"cleanup\")\n",
            "      }\n\n",
            "      System.out.println(\"tail\")\n",
            "   }\n",
        ),
    ] {
        assert!(source.text.contains(fragment), "missing {fragment:?} in {}", source.text);
    }
    let map = source.map.unwrap();
    let method = map.methods.iter().find(|method| method.name == "divideAndClean").unwrap();
    let cleanup = method.offsets[&12];
    assert_eq!(source.text.lines().nth(cleanup), Some("         System.out.println(\"cleanup\")"));
    for offset in [34, 47] {
        assert_eq!(method.offsets[&offset], cleanup);
    }
    assert!(method.offsets[&4] < cleanup);
    assert!(method.offsets[&53] > cleanup);
}

#[test]
fn rejects_different_cleanup_copies_or_returns_from_unspilled_slots() {
    for (name, offset, from, to) in [
        ("divideAndClean", 42, 33, 42),
        ("returnAndClean", 15, 0x1c, 0x1b),
    ] {
        let mut data = bytes(TRY_REGIONS);
        let index = {
            let class = ClassFile::parse(&data).unwrap();
            let method = class.methods.iter().find(|method| {
                class.pool.utf8(method.name_index).unwrap() == name
            }).unwrap();
            let code = method.code(&class.pool).unwrap().unwrap();
            assert_eq!(code.bytes[offset], from);
            code.bytes.as_ptr() as usize - data.as_ptr() as usize + offset
        };
        data[index] = to;
        let class = ClassFile::parse(&data).unwrap();
        assert!(matches!(decompile_class(&class), Err(KotlinError::Unsupported {
            declaration, feature: "unsupported Kotlin exception region"
        }) if declaration == name));
    }
}

#[test]
fn recovers_singleton_initializer_and_instance_and_static_updates() {
    let source = render(OBJECT);
    assert_eq!(
        source,
        concat!(
            "package pkg\n\n",
            "public object TestObject {\n",
            "   public const val objectConstVal: Int = 926\n",
            "   private final var objectVar: Int = 42\n",
            "   public final val objectVal: Regex = kotlin.text.Regex(\"\")\n\n",
            "   public fun objectFun() {\n",
            "      objectVar--\n",
            "   }\n\n",
            "   @kotlin.jvm.JvmStatic\n",
            "   public fun objectJvmStaticFun() {\n",
            "      objectVar++\n",
            "   }\n",
            "}\n",
        )
    );
}

#[test]
fn recovers_companion_storage_and_static_forwarders_once() {
    let host = bytes(COMPANION_HOST);
    let child = bytes(COMPANION_CHILD);
    let group = crate::ClassGroup::new([host.as_slice(), child.as_slice()]).unwrap();
    let options = crate::Options {
        decompile_kotlin: true,
        ..crate::Options::default()
    };
    let source = group.decompile("pkg/TestCompanionObject$Companion", &options).unwrap();
    assert_eq!(source.file_extension, "kt");
    assert_eq!(
        source.text,
        concat!(
            "package pkg\n\n",
            "public class TestCompanionObject {\n",
            "   public fun notInCompanion() {\n",
            "      System.out.println(\"notInCompanion\")\n",
            "   }\n\n",
            "   public companion object {\n",
            "      public final val companionVal: String = \"inCompanion\"\n",
            "      @kotlin.jvm.JvmStatic\n",
            "      public final val companionValJvmStatic: String = \"inCompanionJvmStatic\"\n\n",
            "      public fun inCompanion() {\n",
            "         System.out.println(\"inCompanion\")\n",
            "      }\n\n",
            "      @kotlin.jvm.JvmStatic\n",
            "      public fun inCompanionJvmStatic() {\n",
            "         System.out.println(\"inCompanionJvmStatic\")\n",
            "      }\n",
            "   }\n",
            "}\n",
        )
    );
    assert!(matches!(
        decompile_class(&ClassFile::parse(&host).unwrap()),
        Err(KotlinError::Unsupported { feature: "Kotlin nested class does not match the class group", .. })
    ));
}

#[test]
fn recovers_typed_static_nested_declarations_and_mapped_companion() {
    let classes = NESTING.map(bytes);
    let group = crate::ClassGroup::new(classes.iter().map(Vec::as_slice)).unwrap();
    let options = crate::Options {
        decompile_kotlin: true,
        include_line_mappings: true,
        ..crate::Options::default()
    };
    let source = group.decompile("parity/kotlin/Nesting", &options).unwrap();
    for fragment in [
        "   public companion object Factory {\n      @kotlin.jvm.JvmStatic\n      public fun size(value: Long): Long",
        "   public class Payload(public val value: Int) {\n      public fun doubled(value: Int): Int",
        "   public object Settings {\n      public final val enabled: Boolean = true",
        "      @kotlin.jvm.JvmStatic\n      public fun valueOrDefault(value: Int = 3): Int",
    ] {
        assert!(source.text.contains(fragment), "missing {fragment:?} in {}", source.text);
    }
    let map = source.map.unwrap();
    for (name, class, line) in [
        ("size", "Factory", "         return value + 1L"),
        ("doubled", "Payload", "         return value * 2"),
        ("valueOrDefault", "Settings", "         return value"),
    ] {
        let method = map.methods.iter().find(|method| method.name == name).unwrap();
        assert_eq!(method.class_name, format!("parity/kotlin/Nesting${class}"));
        assert_eq!(source.text.lines().nth(method.offsets[&0]), Some(line));
    }
}

#[test]
fn rejects_invalid_singleton_shell_and_companion_forwarding() {
    fn replace_opcode(data: &mut [u8], name: &str, offset: usize, from: u8, to: u8) {
        let index = {
            let class = ClassFile::parse(data).unwrap();
            let method = class.methods.iter().find(|method| {
                class.pool.utf8(method.name_index).unwrap() == name
            }).unwrap();
            let code = method.code(&class.pool).unwrap().unwrap();
            assert_eq!(code.bytes[offset], from);
            code.bytes.as_ptr() as usize - data.as_ptr() as usize + offset
        };
        data[index] = to;
    }
    let mut object = bytes(OBJECT);
    replace_opcode(&mut object, "<clinit>", 3, 0x59, 0x00);
    assert!(matches!(
        decompile_class(&ClassFile::parse(&object).unwrap()),
        Err(KotlinError::Unsupported { feature: "Kotlin singleton constructor or allocation shell", .. })
    ));
    let mut classes = NESTING.map(bytes);
    replace_opcode(&mut classes[0], "size", 3, 0x1e, 0x1f);
    let group = crate::ClassGroup::new(classes.iter().map(Vec::as_slice)).unwrap();
    let options = crate::Options {
        decompile_kotlin: true,
        ..crate::Options::default()
    };
    assert!(matches!(
        group.decompile("parity/kotlin/Nesting", &options),
        Err(crate::DecompileError::Kotlin(KotlinError::Unsupported {
            feature: "unproven @JvmStatic companion forwarder", ..
        }))
    ));
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
