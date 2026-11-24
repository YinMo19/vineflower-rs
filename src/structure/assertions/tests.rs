use crate::{Options, decompile};

// Handwritten javac-shaped JVM code keeps tests independent of the host JDK.
// The fixture also contains a user throw that must not become an assert.
const POOL: &[u8] = b"\xca\xfe\xba\xbe\0\0\0\x34\0\x23\
    \x01\0\x07Example\x07\0\x01\x01\0\x10java/lang/Object\x07\0\x03\
    \x01\0\x13$assertionsDisabled\x01\0\x01Z\x0c\0\x05\0\x06\x09\0\x02\0\x07\
    \x01\0\x0fjava/lang/Class\x07\0\x09\x01\0\x16desiredAssertionStatus\x01\0\x03()Z\
    \x0c\0\x0b\0\x0c\x0a\0\x0a\0\x0d\
    \x01\0\x18java/lang/AssertionError\x07\0\x0f\x01\0\x06<init>\x01\0\x04(I)V\
    \x0c\0\x11\0\x12\x0a\0\x10\0\x13\x01\0\x03()V\x0c\0\x11\0\x15\x0a\0\x10\0\x16\
    \x01\0\x04Code\x01\0\x08<clinit>\x01\0\x05check\x01\0\x05(ZZ)V\
    \x01\0\x07message\x01\0\x03()I\x0c\0\x1c\0\x1d\x0a\0\x02\0\x1e\
    \x01\0\x05plain\x01\0\x08constant\x01\0\x07exposes";

fn class(flags: u16, extra_read: bool) -> Vec<u8> {
    let mut class = POOL.to_vec();
    class.extend_from_slice(&[0, 0x21, 0, 2, 0, 4, 0, 0, 0, 1]);
    class.extend_from_slice(&flags.to_be_bytes());
    class.extend_from_slice(&[0, 5, 0, 6, 0, 0, 0, 5 + u8::from(extra_read)]);
    fn method(class: &mut Vec<u8>, name: u8, desc: u8, locals: u8, code: &[u8]) {
        class.extend_from_slice(&[0, 8, 0, name, 0, desc, 0, 1, 0, 24]);
        class.extend_from_slice(&(12 + code.len() as u32).to_be_bytes());
        class.extend_from_slice(&[0, 3, 0, locals]);
        class.extend_from_slice(&(code.len() as u32).to_be_bytes());
        class.extend_from_slice(code);
        class.extend_from_slice(&[0, 0, 0, 0]);
    }
    method(&mut class, 25, 21, 0, &[
        0x12, 2, 0xb6, 0, 14, 0x9a, 0, 7, 0x04, 0xa7, 0, 4, 0x03, 0xb3, 0, 8, 0xb1,
    ]);
    method(&mut class, 26, 27, 2, &[
        0xb2, 0, 8, 0x9a, 0, 22, 0x1a, 0x99, 0, 7, 0x1b, 0x9a, 0, 14,
        0xbb, 0, 16, 0x59, 0xb8, 0, 31, 0xb7, 0, 20, 0xbf, 0xb1,
    ]);
    method(&mut class, 28, 29, 0, &[0x10, 42, 0xac]);
    method(&mut class, 32, 21, 0, &[0xbb, 0, 16, 0x59, 0xb7, 0, 23, 0xbf]);
    method(&mut class, 33, 21, 0, &[
        0xb2, 0, 8, 0x9a, 0, 11, 0xbb, 0, 16, 0x59, 0xb7, 0, 23, 0xbf, 0xb1,
    ]);
    if extra_read {
        method(&mut class, 34, 12, 0, &[0xb2, 0, 8, 0xac]);
    }
    class.extend_from_slice(&[0, 0]);
    class
}

#[test]
fn recovers_constant_short_circuit_and_lazy_detail_but_not_a_user_throw() {
    let source = decompile(&class(0x1018, false), &Options::default()).unwrap();
    assert!(source.text.contains("assert var0 && var1 : Example.message();"), "{}", source.text);
    assert!(source.text.contains("assert false;"));
    assert!(source.text.contains("throw new AssertionError();"));
    assert!(!source.text.contains("$assertionsDisabled"));
    assert!(!source.text.contains("desiredAssertionStatus"));
}

#[test]
fn retains_guard_when_disabled_or_not_proven() {
    let mut options = Options::default();
    options.remove_synthetic = true;
    for (flags, extra_read, recover) in [(0x0018, false, true), (0x1018, true, true), (0x1018, false, false)] {
        options.decompile_assert = recover;
        let source = decompile(&class(flags, extra_read), &options).unwrap();
        assert!(source.text.contains("boolean $assertionsDisabled;"), "{}", source.text);
        assert!(source.text.contains("desiredAssertionStatus()"));
        assert!(!source.text.contains("assert false;"));
    }
}
