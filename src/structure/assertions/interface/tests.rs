use crate::{ClassGroup, Options, decompile_group};

use super::interface_guards;

// Shared pool prefix for a constructorless synthetic holder Test$1 and the
// interface Test that accesses it. No compiler is needed for these tests.
const POOL: &[u8] = b"\x01\0\x04Test\x07\0\x01\x01\0\x06Test$1\x07\0\x03\
    \x01\0\x10java/lang/Object\x07\0\x05\x01\0\x0fjava/lang/Class\x07\0\x07\
    \x01\0\x16desiredAssertionStatus\x01\0\x03()Z\x0c\0\x09\0\x0a\x0a\0\x08\0\x0b\
    \x01\0\x13$assertionsDisabled\x01\0\x01Z\x0c\0\x0d\0\x0e\x09\0\x04\0\x0f\
    \x01\0\x08<clinit>\x01\0\x03()V\x01\0\x04Code\
    \x01\0\x0fEnclosingMethod\x01\0\x0cInnerClasses";
const TEST_POOL: &[u8] = b"\x01\0\x18java/lang/AssertionError\x07\0\x16\x01\0\x06<init>\
    \x0c\0\x18\0\x12\x0a\0\x17\0\x19\x01\0\x05check\x01\0\x04(Z)V\
    \x01\0\x05value\x01\0\x01I\x0c\0\x1d\0\x1e\x09\0\x02\0\x1f\
    \x01\0\x07initial\x01\0\x03()I\x0c\0\x21\0\x22\x0b\0\x02\0\x23\
    \x01\0\x06expose\x01\0\x13()Ljava/lang/Class;";

fn header(entries: u8) -> Vec<u8> {
    let mut bytes = b"\xca\xfe\xba\xbe\0\0\0\x45\0".to_vec();
    bytes.push(entries);
    bytes.extend_from_slice(POOL);
    bytes
}

fn method(class: &mut Vec<u8>, flags: u8, name: u8, desc: u8, locals: u8, code: &[u8]) {
    class.extend_from_slice(&[0, flags, 0, name, 0, desc, 0, 1, 0, 19]);
    class.extend_from_slice(&(12 + code.len() as u32).to_be_bytes());
    class.extend_from_slice(&[0, 3, 0, locals]);
    class.extend_from_slice(&(code.len() as u32).to_be_bytes());
    class.extend_from_slice(code);
    class.extend_from_slice(&[0, 0, 0, 0]);
}

fn holder() -> Vec<u8> {
    let mut class = header(22);
    // One final guard field, then the synthetic initializer.
    class.extend_from_slice(&[
        0x10, 0x20, 0, 4, 0, 6, 0, 0, 0, 1, 0x10, 0x18, 0, 13, 0, 14, 0, 0, 0, 1,
    ]);
    method(
        &mut class,
        8,
        17,
        18,
        0,
        &[
            0x12, 2, 0xb6, 0, 12, 0x9a, 0, 7, 0x04, 0xa7, 0, 4, 0x03, 0xb3, 0, 16, 0xb1,
        ],
    );
    class.extend_from_slice(&[0, 2, 0, 20, 0, 0, 0, 4, 0, 2, 0, 0]);
    class.extend_from_slice(&[0, 21, 0, 0, 0, 10, 0, 1, 0, 4, 0, 0, 0, 0, 0x10, 8]);
    class
}

fn interface(trigger_displacement: u8, expose_holder: bool) -> Vec<u8> {
    let mut class = header(39);
    class.extend_from_slice(TEST_POOL);
    class.extend_from_slice(&[0x06, 1, 0, 2, 0, 6, 0, 0, 0, 1, 0, 0x19, 0, 29, 0, 30, 0, 0]);
    class.extend_from_slice(&[0, 3 + u8::from(expose_holder)]);
    method(
        &mut class,
        8,
        17,
        18,
        0,
        &[
            0xb2,
            0,
            16,
            0x99,
            0,
            trigger_displacement,
            0xb8,
            0,
            36,
            0xb3,
            0,
            32,
            0xb1,
        ],
    );
    method(
        &mut class,
        1,
        27,
        28,
        2,
        &[
            0xb2, 0, 16, 0x9a, 0, 15, 0x1b, 0x9a, 0, 11, 0xbb, 0, 23, 0x59, 0xb7, 0, 26, 0xbf, 0xb1,
        ],
    );
    method(&mut class, 9, 33, 34, 0, &[0x08, 0xac]);
    if expose_holder {
        method(&mut class, 9, 37, 38, 0, &[0x12, 4, 0xb0]);
    }
    class.extend_from_slice(&[0, 0]);
    class
}

#[test]
fn removes_only_the_eager_holder_trigger_before_an_interface_field_initializer() {
    let source = decompile_group(
        &interface(3, false),
        [holder().as_slice()],
        &Options::default(),
    )
    .unwrap();
    assert!(
        source.text.contains("int value = Test.initial();"),
        "{}",
        source.text
    );
    assert!(source.text.contains("assert "));
    assert!(!source.text.contains("$assertionsDisabled"));
    assert!(!source.text.contains("Test$1"));
}

#[test]
fn rejects_a_live_holder_class_literal_or_a_nontrivial_initialization_branch() {
    let holder = holder();
    for (trigger, expose) in [(3, true), (9, false)] {
        let interface = interface(trigger, expose);
        let group = ClassGroup::new([holder.as_slice(), interface.as_slice()]).unwrap();
        assert!(interface_guards(&group, "Test").is_empty());
    }
}
