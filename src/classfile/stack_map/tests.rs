// Copyright 2000-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use super::*;
use crate::{bytecode::decode, classfile::Attribute};
use VerificationType::*;

fn pool() -> ConstantPool<'static> {
    let bytes = b"\0\x09\x01\0\x0dStackMapTable\x01\0\x0bpkg/Fixture\x07\0\x02\
        \x01\0\x10java/lang/Object\x07\0\x04\x01\0\x06<init>\
        \x01\0\x1c(ZBCSIFDJ[[I[Lpkg/Missing;)V\x01\0\x03run";
    ConstantPool::read(&mut Reader::new(bytes), false).unwrap()
}

fn code<'a>(bytes: &'a [u8], data: &'a [u8], max_locals: u16, max_stack: u16) -> Code<'a> {
    Code {
        max_stack,
        max_locals,
        bytes,
        exceptions: Vec::new(),
        attributes: vec![Attribute {
            name_index: 1,
            data,
        }],
    }
}

#[test]
fn expands_all_frame_encodings_and_counts_slots_not_entries() {
    let mut bytes = [0; 80];
    bytes[..3].copy_from_slice(&[0xbb, 0, 3]);
    bytes[79] = 0xb1;
    let instructions = decode(&bytes).unwrap();
    #[rustfmt::skip]
    let data = [
        0, 8,
        3,                              // same at 3
        64, 5,                          // same_locals_1_stack_item at 4
        247, 0, 64, 8, 0, 0,            // same_locals_1_stack_item_extended at 69
        254, 0, 0, 2, 4, 7, 0, 5,       // append Float, Long, Object at 70
        249, 0, 0,                      // chop Long and Object at 71
        251, 0, 0,                      // same_frame_extended at 72
        254, 0, 0, 4, 3, 4,             // append Long, Double, Long at 73
        255, 0, 0,                      // full at 74
        0, 9, 0, 1, 2, 3, 4, 5, 6, 7, 0, 3, 8, 0, 0,
        0, 2, 3, 7, 0, 5,
    ];
    let initial = [Object(3), Long];
    let appended = [Object(3), Long, Float, Long, Object(5)];
    let chopped = [Object(3), Long, Float];
    let reappended = [Object(3), Long, Float, Long, Double, Long];
    let full = [
        Top,
        Integer,
        Float,
        Double,
        Long,
        Null,
        UninitializedThis,
        Object(3),
        Uninitialized(0),
    ];
    let expected: [(u16, &[_], &[_]); 8] = [
        (3, &initial, &[]),
        (4, &initial, &[Null]),
        (69, &initial, &[Uninitialized(0)]),
        (70, &appended, &[]),
        (71, &chopped, &[]),
        (72, &chopped, &[]),
        (73, &reappended, &[]),
        (74, &full, &[Double, Object(5)]),
    ];
    let mut expected = expected.into_iter();
    let present = code(&bytes, &data, 11, 3)
        .visit_stack_map_frames(&pool(), &initial, Some(&instructions), |frame| {
            assert_eq!(
                (frame.offset, frame.locals, frame.stack),
                expected.next().unwrap()
            );
            match frame.offset {
                70 => {
                    assert_eq!(frame.local(2), Top); // Tail of the initial long.
                    assert_eq!(frame.local(4), Long);
                    assert_eq!(frame.local(5), Top); // Tail of the appended long.
                    assert_eq!(frame.local(6), Object(5));
                }
                71 | 72 => {
                    assert_eq!(frame.local(3), Float);
                    assert_eq!(frame.local(4), Top);
                    assert_eq!(frame.local(6), Top);
                }
                73 => {
                    assert_eq!(frame.local(4), Long);
                    assert_eq!(frame.local(6), Double);
                    assert_eq!(frame.local(8), Long);
                    assert_eq!(frame.local(9), Top);
                }
                74 => {
                    assert_eq!(frame.local(3), Double);
                    assert_eq!(frame.local(4), Top);
                    assert_eq!(frame.local(5), Long);
                    assert_eq!(frame.local(6), Top);
                    assert_eq!(frame.local(10), Uninitialized(0));
                }
                _ => {}
            }
        })
        .unwrap();
    assert!(present);
    assert!(expected.next().is_none());
}

#[test]
fn initial_locals_use_descriptor_references_and_constructor_receiver() {
    let mut class = ClassFile {
        minor_version: 0,
        major_version: 50,
        pool: pool(),
        access_flags: 0,
        this_class: 3,
        super_class: 5,
        interfaces: Vec::new(),
        fields: Vec::new(),
        methods: Vec::new(),
        attributes: Vec::new(),
    };
    let mut member = Member {
        access_flags: 0,
        name_index: 6,
        descriptor_index: 7,
        attributes: Vec::new(),
    };
    let descriptor =
        MethodDescriptor::parse(class.pool.utf8(member.descriptor_index).unwrap()).unwrap();
    let parameters = [
        Integer,
        Integer,
        Integer,
        Integer,
        Integer,
        Float,
        Double,
        Long,
        DescriptorReference(&descriptor.parameters[8]),
        DescriptorReference(&descriptor.parameters[9]),
    ];
    let initial = initial_stack_map_locals(&class, &member, &descriptor).unwrap();
    assert_eq!(initial[0], UninitializedThis);
    assert_eq!(initial[1..], parameters);
    code(&[0xb1], &[0, 1, 0], 13, 0)
        .visit_stack_map_frames(&class.pool, &initial, None, |frame| {
            assert_eq!(frame.local(8), Top); // Tail of the double parameter.
            assert_eq!(frame.local(9), Long);
            assert_eq!(frame.local(11), parameters[8]);
            assert_eq!(frame.local(12), parameters[9]);
        })
        .unwrap();

    class.this_class = 5;
    class.super_class = 0;
    assert_eq!(
        initial_stack_map_locals(&class, &member, &descriptor).unwrap()[0],
        Object(5)
    );
    member.name_index = 8;
    member.access_flags = 0x0008;
    assert_eq!(
        initial_stack_map_locals(&class, &member, &descriptor).unwrap(),
        parameters
    );
}

#[test]
fn reads_original_javac_loop_frames() {
    let class =
        ClassFile::parse(include_bytes!("../../../tests/smoke/java8/TestSimpleWhile.class")).unwrap();
    let member = class
        .methods
        .iter()
        .find(|member| class.pool.utf8(member.name_index).unwrap() == "test")
        .unwrap();
    let descriptor =
        MethodDescriptor::parse(class.pool.utf8(member.descriptor_index).unwrap()).unwrap();
    let initial = initial_stack_map_locals(&class, member, &descriptor).unwrap();
    let code = member.code(&class.pool).unwrap().unwrap();
    let instructions = decode(code.bytes).unwrap();
    let mut offsets = Vec::new();
    assert!(
        code.visit_stack_map_frames(&class.pool, &initial, Some(&instructions), |frame| {
            offsets.push(frame.offset);
            assert_eq!(frame.locals, [Object(class.this_class), Integer]);
            assert!(frame.stack.is_empty());
        })
        .unwrap()
    );
    assert_eq!(offsets, [0, 19]);
}

#[test]
fn missing_empty_and_duplicate_attributes_are_distinct() {
    let pool = pool();
    let mut code = code(&[0xb1], &[0, 0], 0, 0);
    let never = |_: StackMapFrame<'_, '_>| panic!("no frames expected");
    assert!(code.visit_stack_map_frames(&pool, &[], None, never).unwrap());
    code.attributes.push(code.attributes[0]);
    assert!(matches!(
        code.visit_stack_map_frames(&pool, &[], None, never),
        Err(StackMapError::DuplicateAttribute)
    ));
    code.attributes.clear();
    assert!(!code.visit_stack_map_frames(&pool, &[], None, never).unwrap());
}

#[test]
fn checks_frame_and_new_offsets_against_instruction_boundaries_when_supplied() {
    // Offset 1 contains the byte for `new` but is an operand of offset 0.
    let bytes = [0xbb, 0xbb, 3, 0xb1];
    let instructions = decode(&bytes).unwrap();
    let pool = pool();
    let invalid = |data: &[u8]| {
        code(&bytes, data, 0, 1)
            .visit_stack_map_frames(&pool, &[], Some(&instructions), |_| {
                panic!("invalid frame")
            })
            .unwrap_err()
    };
    assert!(matches!(
        invalid(&[0, 1, 4]),
        StackMapError::FrameOutOfBounds(4)
    ));
    assert!(matches!(
        invalid(&[0, 1, 1]),
        StackMapError::FrameNotInstruction(1)
    ));
    for offset in [1, 3] {
        assert!(matches!(
            invalid(&[0, 1, 67, 8, 0, offset]),
            StackMapError::UninitializedNotNew(actual) if actual == u16::from(offset)
        ));
    }
    assert!(matches!(
        invalid(&[0, 1, 67, 8, 0, 4]),
        StackMapError::UninitializedOutOfBounds(4)
    ));
    assert!(
        code(&bytes, &[0, 1, 65, 8, 0, 1], 0, 1)
            .visit_stack_map_frames(&pool, &[], None, |frame| {
                assert_eq!(frame.offset, 1);
                assert_eq!(frame.stack, [Uninitialized(1)]);
            })
            .unwrap()
    );
}

#[test]
fn rejects_frame_offset_overflow_without_wrapping() {
    let bytes = vec![0; usize::from(u16::MAX)];
    let mut offsets = Vec::new();
    let result = code(&bytes, &[0, 2, 251, 255, 254, 251, 0, 1], 0, 0)
        .visit_stack_map_frames(&pool(), &[], None, |frame| offsets.push(frame.offset));
    assert!(matches!(result, Err(StackMapError::FrameOutOfBounds(65536))));
    assert_eq!(offsets, [65534]);
}

#[test]
fn rejects_bad_tags_pool_indices_slot_counts_and_payload_boundaries() {
    let pool = pool();
    let invalid = |data| {
        code(&[0xb1], data, 1, 1)
            .visit_stack_map_frames(&pool, &[], None, |_| panic!("invalid frame"))
            .unwrap_err()
    };
    assert!(matches!(invalid(&[0, 2]), StackMapError::TooManyFrames { count: 2, .. }));
    assert!(matches!(invalid(&[0, 1, 128]), StackMapError::ReservedFrameTag(128)));
    assert!(matches!(invalid(&[0, 1, 64, 9]), StackMapError::InvalidTypeTag(9)));
    assert!(matches!(
        invalid(&[0, 1, 64, 7, 0, 0]),
        StackMapError::Class(ClassError::InvalidConstantIndex(0))
    ));
    assert!(matches!(
        invalid(&[0, 1, 64, 7, 0, 2]),
        StackMapError::Class(ClassError::WrongConstantType { index: 2, expected: "Class", .. })
    ));
    assert!(matches!(
        invalid(&[0, 1, 250, 0, 0]),
        StackMapError::InvalidChop { count: 1, available: 0 }
    ));
    assert!(matches!(
        invalid(&[0, 1, 252, 0, 0, 4]),
        StackMapError::TooManySlots { kind: "locals", limit: 1 }
    ));
    assert!(matches!(
        invalid(&[0, 1, 64, 3]),
        StackMapError::TooManySlots { kind: "operand stack entries", limit: 1 }
    ));
    assert!(matches!(
        invalid(&[0, 1, 64, 7, 0]),
        StackMapError::Class(ClassError::UnexpectedEof { offset: 4, .. })
    ));
    assert!(matches!(
        invalid(&[0, 0, 0]),
        StackMapError::Class(ClassError::TrailingBytes { context: "StackMapTable", .. })
    ));
}
