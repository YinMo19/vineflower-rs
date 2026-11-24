use crate::bytecode::decode;

use super::*;

// Class Example extends Object. #9 is Example.side:()I and #13 is its constructor.
const CLASS: &[u8] = b"\xca\xfe\xba\xbe\0\0\0\x3d\0\x0e\
    \x01\0\x07Example\x07\0\x01\x01\0\x10java/lang/Object\x07\0\x03\
    \x01\0\x04test\x01\0\x03()I\x01\0\x04side\x0c\0\x07\0\x06\x0a\0\x02\0\x08\
    \x01\0\x06<init>\x01\0\x03()V\x0c\0\x0a\0\x0b\x0a\0\x02\0\x0c\
    \0\x21\0\x02\0\x04\0\0\0\0\0\0\0\0";

fn with_machine(test: impl FnOnce(Machine<'_, '_>)) {
    let class = ClassFile::parse(CLASS).unwrap();
    let method = Member {
        access_flags: 0x0008,
        name_index: 5,
        descriptor_index: 6,
        attributes: vec![],
    };
    let code = Code {
        max_stack: 16,
        max_locals: 4,
        bytes: &[],
        exceptions: vec![],
        attributes: vec![],
    };
    let descriptor = MethodDescriptor::parse("()I").unwrap();
    let options = Options::default();
    test(
        Machine::new(&class, &method, &code, &descriptor, &options, &|name| {
            name.rsplit('/').next().unwrap().into()
        })
        .unwrap(),
    );
}

#[test]
fn implements_every_legal_dup_slot_shape() {
    // Symbols a-d are one-slot ints; X and Y are two-slot longs.
    let cases = [
        ("a", 0x59, "aa"),
        ("ab", 0x5a, "bab"),
        ("abc", 0x5b, "cabc"),
        ("Xa", 0x5b, "aXa"),
        ("ab", 0x5c, "abab"),
        ("X", 0x5c, "XX"),
        ("abc", 0x5d, "bcabc"),
        ("aX", 0x5d, "XaX"),
        ("abcd", 0x5e, "cdabcd"),
        ("Xab", 0x5e, "abXab"),
        ("abX", 0x5e, "XabX"),
        ("XY", 0x5e, "YXY"),
    ];
    for (input, opcode, expected) in cases {
        with_machine(|mut machine| {
            let mut bytes: Vec<_> = input
                .bytes()
                .map(|op| match op {
                    b'a'..=b'd' => op - b'a' + 3,
                    b'X'..=b'Y' => op - b'X' + 9,
                    _ => unreachable!(),
                })
                .collect();
            bytes.push(opcode);
            for instruction in decode(&bytes).unwrap() {
                machine.step(&instruction).unwrap();
            }
            let symbols: String = machine
                .stack
                .iter()
                .map(|expr| match expr.text.as_str() {
                    "0" => 'a',
                    "1" => 'b',
                    "2" => 'c',
                    "3" => 'd',
                    "0L" => 'X',
                    "1L" => 'Y',
                    _ => panic!("unexpected operand expression {}", expr.text),
                })
                .collect();
            assert_eq!(symbols, expected, "{opcode:#04x} with stack {input}");
        });
    }
}

#[test]
fn rejects_splitting_a_category_two_value() {
    for opcode in [0x57, 0x59, 0x5a, 0x5b, 0x5f] {
        with_machine(|mut machine| {
            let instructions = decode(&[0x09, opcode]).unwrap();
            machine.step(&instructions[0]).unwrap();
            assert!(matches!(
                machine.step(&instructions[1]),
                Err(LiftError::InvalidStack { offset: 1, .. })
            ));
        });
    }
}

#[test]
fn duplicated_call_runs_once() {
    with_machine(|mut machine| {
        let instructions = decode(&[0xb8, 0, 9, 0x59, 0x60, 0xac]).unwrap();
        machine.step(&instructions[0]).unwrap();
        machine.step(&instructions[1]).unwrap();
        assert_eq!(machine.take_prelude(), ["int stack3 = Example.side();"]);
        machine.step(&instructions[2]).unwrap();
        assert!(
            matches!(machine.step(&instructions[3]).unwrap(), Effect::Return(Some(text)) if text == "stack3 + stack3")
        );
    });
}

#[test]
fn own_static_members_keep_symbols_and_respect_local_and_initializer_scope() {
    use crate::{classfile::Attribute, source_text::tokens::TokenKind};

    const CLASS: &[u8] = b"\xca\xfe\xba\xbe\0\0\0\x3d\0\x12\
        \x01\0\x07Example\x07\0\x01\x01\0\x10java/lang/Object\x07\0\x03\
        \x01\0\x04test\x01\0\x03()I\x01\0\x04side\x0c\0\x07\0\x06\x0a\0\x02\0\x08\
        \x01\0\x05value\x01\0\x01I\x0c\0\x0a\0\x0b\x09\0\x02\0\x0c\
        \x01\0\x12LocalVariableTable\x01\0\x04(I)I\x01\0\x08<clinit>\x01\0\x03()V\
        \0\x21\0\x02\0\x04\0\0\0\0\0\0\0\0";
    let mut class = ClassFile::parse(CLASS).unwrap();
    let member = |name_index, descriptor_index| Member {
        access_flags: 0x0008,
        name_index,
        descriptor_index,
        attributes: Vec::new(),
    };
    class.methods.push(member(7, 6));
    class.fields.push(member(10, 11));
    let options = Options {
        dump_text_tokens: true,
        ..Options::default()
    };

    let lift = |name, kind, bytes: &[u8], locals: Option<&[u8]>| {
        let method = member(name, kind);
        let code = Code {
            max_stack: 1,
            max_locals: 1,
            bytes,
            exceptions: Vec::new(),
            attributes: locals.map_or_else(Vec::new, |data| vec![Attribute {
                name_index: 14,
                data,
            }]),
        };
        let descriptor =
            MethodDescriptor::parse(class.pool.utf8(kind).unwrap()).unwrap();
        let mut machine =
            Machine::new(&class, &method, &code, &descriptor, &options, &str::to_owned).unwrap();
        for instruction in decode(bytes).unwrap() {
            match machine.step(&instruction).unwrap() {
                Effect::Return(Some(text)) | Effect::Statement(text) => return text,
                Effect::FieldAssignment { value, .. } => return value,
                _ => continue,
            }
        }
        panic!("expected lifted expression");
    };
    let getstatic = &[0xb2, 0, 13, 0xac];
    let field = lift(5, 6, getstatic, None);
    assert_eq!(field, "value");
    let mut tokens = field.flat_tokens();
    let (range, token) = tokens.next().unwrap();
    assert_eq!(range, 0..5);
    assert!(matches!(&token.kind, TokenKind::Field { owner, name, descriptor }
        if owner == "Example" && name == "value" && descriptor == "I"));
    assert!(tokens.next().is_none());

    let call = lift(5, 6, &[0xb8, 0, 9, 0xac], None);
    assert_eq!(call, "side()");
    let mut tokens = call.flat_tokens();
    let (range, token) = tokens.next().unwrap();
    assert_eq!(range, 0..4);
    assert!(matches!(&token.kind, TokenKind::Method { owner, name, descriptor }
        if owner == "Example" && name == "side" && descriptor == "()I"));
    assert!(tokens.next().is_none());

    let parameter = b"\0\x01\0\0\0\x04\0\x0a\0\x0b\0\0";
    assert_eq!(lift(5, 15, getstatic, Some(parameter)), "Example.value");
    let later_local = b"\0\x01\0\x04\0\x02\0\x0a\0\x0b\0\0";
    assert_eq!(
        lift(5, 6, &[0xb2, 0, 13, 0x3b, 0x1a, 0xac], Some(later_local)),
        "int value = Example.value;",
    );
    assert_eq!(
        lift(16, 17, &[0xb2, 0, 13, 0xb3, 0, 13, 0xb1], None),
        "Example.value",
    );
}

#[test]
fn recovers_postincrement_of_the_loaded_local_without_a_spill() {
    with_machine(|mut machine| {
        let instructions = decode(&[0x04, 0x3b, 0x1a, 0x84, 0, 1, 0xac]).unwrap();
        machine.step(&instructions[0]).unwrap();
        let Effect::Statement(initial) = machine.step(&instructions[1]).unwrap() else {
            panic!()
        };
        assert_eq!(initial, "int var0 = 1;");
        machine.step(&instructions[2]).unwrap();
        assert!(matches!(
            machine.step(&instructions[3]).unwrap(),
            Effect::None
        ));
        assert!(machine.take_prelude().is_empty());
        assert!(
            matches!(machine.step(&instructions[4]).unwrap(), Effect::Return(Some(text)) if text == "var0++")
        );
    });
}

#[test]
fn binary_layout_preserves_numeric_association() {
    let cases = [
        (Primitive::Int, 0x60, 0x60, "a + b + c"),
        (Primitive::Int, 0x60, 0x64, "a - (b + c)"),
        (Primitive::Long, 0x6d, 0x69, "a * (b / c)"),
        (Primitive::Float, 0x62, 0x62, "a + (b + c)"),
        (Primitive::Double, 0x6b, 0x6b, "a * (b * c)"),
    ];
    for (ty, inner, outer, expected) in cases {
        with_machine(|mut machine| {
            for name in ["a", "b", "c"] {
                machine.push(Expr::atom(Type::Primitive(ty), name.into())).unwrap();
            }
            machine.arithmetic(inner).unwrap();
            machine.arithmetic(outer).unwrap();
            let result = machine.pop_raw().unwrap().text;
            assert_eq!(result, expected);
            if expected == "a + b + c" {
                let mut out = String::new();
                result.render(&mut out, 6, "  ");
                assert_eq!(out, "a\n  + b\n  + c");
            }
        });
    }
}

#[test]
fn floating_comparison_keeps_nan_on_the_correct_branch() {
    with_machine(|mut machine| {
        let instructions = decode(&[0x0b, 0x0c, 0x95, 0x9b, 0, 3, 0x00]).unwrap();
        for instruction in &instructions[..3] {
            machine.step(instruction).unwrap();
        }
        let Effect::Branch {
            target,
            when_true,
            when_false,
        } = machine.step(&instructions[3]).unwrap()
        else {
            panic!()
        };
        assert_eq!(target, 6);
        assert_eq!(when_true, "!(0.0F >= 1.0F)");
        assert_eq!(when_false, "0.0F >= 1.0F");
    });
}

#[test]
fn constructor_initializes_the_surviving_dup_alias() {
    with_machine(|mut machine| {
        let instructions = decode(&[0xbb, 0, 2, 0x59, 0xb7, 0, 13, 0x4b, 0x03, 0xac]).unwrap();
        for instruction in &instructions[..3] {
            assert!(matches!(machine.step(instruction).unwrap(), Effect::None));
        }
        assert!(machine.take_prelude().is_empty());
        assert!(
            matches!(machine.step(&instructions[3]).unwrap(), Effect::Statement(text)
            if text == "Example var0 = new Example();")
        );
    });
}

#[test]
fn boolean_array_store_uses_single_slot_and_boolean_conversion() {
    with_machine(|mut machine| {
        let instructions =
            decode(&[0x04, 0xbc, 4, 0x4b, 0x2a, 0x03, 0x04, 0x54, 0x03, 0xac]).unwrap();
        for instruction in &instructions[..6] {
            machine.step(instruction).unwrap();
        }
        assert!(
            matches!(machine.step(&instructions[6]).unwrap(), Effect::Statement(text)
            if text == "var0[0] = true;")
        );
    });
}
