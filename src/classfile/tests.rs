use super::*;
use std::borrow::Cow;

struct Fixture {
    pool: Vec<u8>,
    count: u16,
    minor: u16,
    major: u16,
}

impl Fixture {
    fn new() -> Self {
        let mut fixture = Self {
            pool: Vec::new(),
            count: 1,
            minor: 0,
            major: 65,
        };
        let name = fixture.utf8(b"example/Fixture");
        fixture.cp(7, &name.to_be_bytes());
        fixture
    }

    fn utf8(&mut self, bytes: &[u8]) -> u16 {
        let index = self.count;
        self.count += 1;
        self.pool.push(1);
        self.pool.extend((bytes.len() as u16).to_be_bytes());
        self.pool.extend(bytes);
        index
    }

    fn cp(&mut self, tag: u8, data: &[u8]) -> u16 {
        let index = self.count;
        self.count += if matches!(tag, 5 | 6) { 2 } else { 1 };
        self.pool.push(tag);
        self.pool.extend(data);
        index
    }

    fn finish(self, methods: &[Vec<u8>], attributes: &[Vec<u8>]) -> Vec<u8> {
        let mut output = 0xcafe_babeu32.to_be_bytes().to_vec();
        output.extend(words(&[self.minor, self.major, self.count]));
        output.extend(self.pool);
        output.extend(words(&[0x21, 2, 0, 0, 0])); // flags, this, super, interfaces, fields
        write_table(&mut output, methods);
        write_table(&mut output, attributes);
        output
    }
}

fn words(values: &[u16]) -> Vec<u8> {
    values.iter().flat_map(|word| word.to_be_bytes()).collect()
}

fn write_table(bytes: &mut Vec<u8>, entries: &[Vec<u8>]) {
    bytes.extend((entries.len() as u16).to_be_bytes());
    for entry in entries {
        bytes.extend(entry);
    }
}

fn attribute(name: u16, bytes: &[u8]) -> Vec<u8> {
    let mut out = name.to_be_bytes().to_vec();
    out.extend((bytes.len() as u32).to_be_bytes());
    out.extend(bytes);
    out
}

fn member(name: u16, descriptor: u16, attributes: &[Vec<u8>]) -> Vec<u8> {
    let mut bytes = words(&[1, name, descriptor]);
    write_table(&mut bytes, attributes);
    bytes
}

#[test]
fn modified_utf8_preserves_surrogates_and_borrows_compatible_bytes() {
    let mut fixture = Fixture::new();
    let plain = fixture.utf8("aé日".as_bytes());
    let paired = fixture.utf8(&[0xc0, 0x80, 0xed, 0xa0, 0xbd, 0xed, 0xb8, 0x80]);
    let unpaired = fixture.utf8(&[0xed, 0xb0, 0x80, b'x', 0xed, 0xa0, 0x80]);
    let literal = fixture.cp(8, &unpaired.to_be_bytes());
    let bytes = fixture.finish(&[], &[]);
    let class = ClassFile::parse(&bytes).unwrap();
    let text = class.pool.utf8(plain).unwrap();
    let input_slice = bytes
        .windows(text.len())
        .find(|window| *window == text.as_bytes())
        .unwrap();
    assert!(std::ptr::eq(input_slice, text.as_bytes()));
    assert_eq!(class.pool.utf8(paired).unwrap(), "\0😀");
    assert_eq!(&*class.pool.utf16(paired).unwrap(), &[0, 0xd83d, 0xde00]);
    assert!(
        matches!(class.pool.utf8(unpaired), Err(ClassError::UnpairedSurrogate(index)) if index == unpaired)
    );
    assert_eq!(
        class.pool.utf16(unpaired).unwrap(),
        Cow::Borrowed(&[0xdc00u16, 120, 0xd800][..])
    );
    assert!(
        matches!(class.pool.get(literal).unwrap(), Constant::String(index) if *index == unpaired)
    );
}

#[test]
fn modified_utf8_rejects_invalid_sequences() {
    for data in [
        &[0][..],
        &[0xc0, 0xaf],
        &[0xc1, 0x80],
        &[0xe0, 0x80, 0x80],
        &[0xf0, 0x9f, 0x98, 0x80],
        &[0xed, 0xa0],
        &[0x80],
        &[0xed, 0xa0, 0x80, 0xe0, 0x9f, 0xbf],
    ] {
        let mut fixture = Fixture::new();
        let index = fixture.utf8(data);
        let bytes = fixture.finish(&[], &[]);
        assert!(
            matches!(ClassFile::parse(&bytes), Err(ClassError::InvalidModifiedUtf8 {index: got, ..}) if got == index)
        );
    }
}

#[test]
fn constant_pool_handles_double_slots_and_forward_references() {
    let mut fixture = Fixture::new();
    let wide = fixture.cp(5, &(-12i64).to_be_bytes());
    let double = fixture.cp(6, &0x7ff8_0000_0000_0003u64.to_be_bytes());
    let member = fixture.cp(10, &words(&[2, 8]));
    let name_and_type = fixture.cp(12, &words(&[9, 10]));
    fixture.utf8(b"run");
    fixture.utf8(b"()V");
    let bytes = fixture.finish(&[], &[]);
    let class = ClassFile::parse(&bytes).unwrap();
    assert!(matches!(class.pool.get(wide).unwrap(), Constant::Long(-12)));
    assert!(
        matches!(class.pool.get(double).unwrap(), Constant::Double(value) if value.to_bits() == 0x7ff8_0000_0000_0003)
    );
    for index in [0, wide + 1, double + 1, 11] {
        assert!(
            matches!(class.pool.get(index), Err(ClassError::InvalidConstantIndex(got)) if index == got)
        );
    }
    assert_eq!(class.pool.iter().count(), 8);
    assert_eq!(
        class.pool.member_ref(member).unwrap(),
        ("example/Fixture", "run", "()V")
    );
    assert_eq!(
        class.pool.name_and_type(name_and_type).unwrap(),
        ("run", "()V")
    );
    assert!(matches!(
        class.pool.utf8(member),
        Err(ClassError::WrongConstantType {
            expected: "Utf8",
            ..
        })
    ));

    let mut fixture = Fixture::new();
    let last = fixture.cp(6, &0f64.to_be_bytes());
    fixture.count -= 1;
    assert!(
        matches!(ClassFile::parse(&fixture.finish(&[], &[])), Err(ClassError::MissingWideSlot(index)) if index == last)
    );
}

#[test]
fn attributes_are_bounded_and_preserve_unknown_data() {
    let mut fixture = Fixture::new();
    let unknown = fixture.utf8(&[0xed, 0xa0, 0x80]);
    let signature = fixture.utf8(b"Signature");
    let value = fixture.utf8(b"Lexample/Fixture;");
    let bytes = fixture.finish(
        &[],
        &[
            attribute(unknown, &[1, 2, 3]),
            attribute(signature, &words(&[value])),
        ],
    );
    let class = ClassFile::parse(&bytes).unwrap();
    assert!(std::ptr::eq(
        class.attributes[0].data,
        &bytes[bytes.len() - 11..bytes.len() - 8]
    ));
    assert_eq!(class.signature().unwrap(), Some("Lexample/Fixture;"));
    for end in 0..bytes.len() {
        assert!(
            ClassFile::parse(&bytes[..end]).is_err(),
            "prefix of length {end}"
        );
    }
    let mut trailing = bytes;
    trailing.push(0);
    assert!(matches!(
        ClassFile::parse(&trailing),
        Err(ClassError::TrailingBytes {
            context: "class file",
            ..
        })
    ));

    let mut fixture = Fixture::new();
    let signature = fixture.utf8(b"Signature");
    let value = fixture.utf8(b"Lexample/Fixture;");
    let bad_length = fixture.finish(&[], &[attribute(signature, &words(&[value, 0]))]);
    let class = ClassFile::parse(&bad_length).unwrap();
    assert!(matches!(
        class.signature(),
        Err(ClassError::TrailingBytes {
            context: "Signature",
            ..
        })
    ));

    let mut fixture = Fixture::new();
    let unknown = fixture.utf8(b"Unsupported");
    let mut huge_length = unknown.to_be_bytes().to_vec();
    huge_length.extend(u32::MAX.to_be_bytes());
    assert!(
        matches!(ClassFile::parse(&fixture.finish(&[], &[huge_length])), Err(ClassError::UnexpectedEof { needed, .. }) if needed == u32::MAX as usize)
    );
}

#[test]
fn code_supports_oak_and_modern_headers() {
    for (major, minor, oak) in [(65, 0, false), (45, 3, false), (45, 2, true)] {
        let mut fixture = Fixture::new();
        fixture.major = major;
        fixture.minor = minor;
        let name = fixture.utf8(b"run");
        let descriptor = fixture.utf8(b"()V");
        let code = fixture.utf8(b"Code");
        let lines = fixture.utf8(b"LineNumberTable");
        let locals = fixture.utf8(b"LocalVariableTable");
        let var_name = fixture.utf8(b"arg");
        let var_descriptor = fixture.utf8(b"I");
        let mut data = if oak {
            vec![2, 3, 0, 2]
        } else {
            vec![0, 2, 0, 3, 0, 0, 0, 2]
        };
        data.extend([0x00, 0xb1]);
        data.extend(words(&[1, 0, 1, 1, 0])); // catch-all [0,1) -> 1
        write_table(
            &mut data,
            &[
                attribute(lines, &words(&[1, 0, 123])),
                attribute(lines, &words(&[1, 1, 456])),
                attribute(locals, &words(&[1, 0, 2, var_name, var_descriptor, 1])),
            ],
        );
        let bytes = fixture.finish(&[member(name, descriptor, &[attribute(code, &data)])], &[]);
        let class = ClassFile::parse(&bytes).unwrap();
        let code = class.methods[0].code(&class.pool).unwrap().unwrap();
        assert_eq!((code.max_stack, code.max_locals), (2, 3));
        assert_eq!(code.bytes, &[0, 0xb1]);
        assert_eq!(
            code.exceptions,
            [ExceptionHandler {
                start_pc: 0,
                end_pc: 1,
                handler_pc: 1,
                catch_type: 0
            }]
        );
        assert_eq!(
            code.line_numbers(&class.pool).unwrap(),
            [(0, 123), (1, 456)]
        );
        assert_eq!(
            code.local_variables(&class.pool).unwrap(),
            [LocalVariable {
                start_pc: 0,
                length: 2,
                index: 1,
                name: "arg",
                descriptor: "I"
            }]
        );
    }
}

#[test]
fn ordered_metadata_and_nested_annotations() {
    let mut fixture = Fixture::new();
    let annotation_name = fixture.utf8(b"RuntimeVisibleAnnotations");
    let annotation_type = fixture.utf8(b"Lexample/Anno;");
    let element_name = fixture.utf8(b"value");
    let element_text = fixture.utf8(&[0xed, 0xa0, 0x80]);
    let inner_classes = fixture.utf8(b"InnerClasses");
    let record = fixture.utf8(b"Record");
    let signature = fixture.utf8(b"Signature");
    let signature_value = fixture.utf8(b"TT;");
    let descriptor = fixture.utf8(b"Ljava/lang/Object;");
    let mut annotation = words(&[1, annotation_type, 1, element_name]);
    annotation.extend([b'[', 0, 2, b's']);
    annotation.extend(words(&[element_text]));
    annotation.push(b'@');
    annotation.extend(words(&[annotation_type, 0]));
    let mut components = words(&[1, element_name, descriptor]);
    write_table(
        &mut components,
        &[attribute(signature, &words(&[signature_value]))],
    );
    let bytes = fixture.finish(
        &[],
        &[
            attribute(inner_classes, &words(&[1, 2, 0, 0, 0x21])),
            attribute(annotation_name, &annotation),
            attribute(record, &components),
        ],
    );
    let class = ClassFile::parse(&bytes).unwrap();
    assert_eq!(
        class.inner_classes().unwrap(),
        [InnerClass {
            inner_class: 2,
            outer_class: 0,
            inner_name: 0,
            access_flags: 0x21
        }]
    );
    assert_eq!(
        class.annotations(true).unwrap(),
        [Annotation {
            type_index: annotation_type,
            elements: vec![(
                element_name,
                ElementValue::Array(vec![
                    ElementValue::Constant {
                        tag: b's',
                        index: element_text
                    },
                    ElementValue::Annotation(Box::new(Annotation {
                        type_index: annotation_type,
                        elements: vec![]
                    })),
                ])
            )],
        }]
    );
    assert!(class.annotations(false).unwrap().is_empty());
    let components = class.record_components().unwrap().unwrap();
    assert_eq!(components[0].signature(&class.pool).unwrap(), Some("TT;"));
}

#[test]
fn bootstrap_and_method_metadata_resolve_checked_pool_entries() {
    let mut fixture = Fixture::new();
    let name = fixture.utf8(b"run");
    let descriptor = fixture.utf8(b"(I)V");
    let name_and_type = fixture.cp(12, &words(&[name, descriptor]));
    let target = fixture.cp(10, &words(&[2, name_and_type]));
    let [target_hi, target_lo] = target.to_be_bytes();
    let handle = fixture.cp(15, &[6, target_hi, target_lo]);
    let integer = fixture.cp(3, &3i32.to_be_bytes());
    let bootstrap = fixture.utf8(b"BootstrapMethods");
    let exceptions = fixture.utf8(b"Exceptions");
    let parameters = fixture.utf8(b"MethodParameters");
    let default = fixture.utf8(b"AnnotationDefault");
    let mut default_value = vec![b'I'];
    default_value.extend(integer.to_be_bytes());
    let bytes = fixture.finish(
        &[member(
            name,
            descriptor,
            &[
                attribute(exceptions, &words(&[1, 2])),
                attribute(parameters, &[1, 0, 0, 0, 0x10]),
                attribute(default, &default_value),
            ],
        )],
        &[attribute(bootstrap, &words(&[1, handle, 1, integer]))],
    );
    let class = ClassFile::parse(&bytes).unwrap();
    assert_eq!(
        class.bootstrap_methods().unwrap(),
        [BootstrapMethod {
            method_ref: handle,
            arguments: vec![integer]
        },]
    );
    assert_eq!(class.methods[0].exceptions(&class.pool).unwrap(), [2]);
    assert_eq!(
        class.methods[0].method_parameters(&class.pool).unwrap(),
        [MethodParameter {
            name_index: 0,
            access_flags: 0x10
        },]
    );
    assert_eq!(
        class.methods[0].annotation_default(&class.pool).unwrap(),
        Some(ElementValue::Constant {
            tag: b'I',
            index: integer
        },)
    );
}
