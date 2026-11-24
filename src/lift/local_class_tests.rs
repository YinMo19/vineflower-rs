// Copyright 2000-2021 JetBrains s.r.o. (Apache-2.0).
use crate::{Options, decompile_group};

const LOCAL: &str = "CaptureLocal$1Local";

#[test]
fn local_class_captures_parameter_and_local_through_delegating_constructor() {
    let (outer, local) = inputs(false);
    let result = decompile_group(&outer, [&local[..]], &Options::default()).unwrap();
    let text = result.text;
    let outside = text.find("int extra = base + 3;").unwrap();
    let declaration = text.find("class Local {").unwrap();
    assert!(outside < declaration);
    assert!(
        text.contains("         Local() {\n            this(1);"),
        "{text}"
    );
    assert!(text.contains("Local(int ignored)"));
    assert!(text.contains("return base + extra;"));
    assert!(text.contains("return new Local().value();"));
    assert!(!text.contains("val$"));
}

#[test]
fn local_class_marks_its_declaration_without_changing_captured_names() {
    let (outer, local) = inputs(false);
    let options = Options {
        mark_corresponding_synthetics: true,
        dump_text_tokens: true,
        ..Options::default()
    };
    let text = decompile_group(&outer, [&local[..]], &options).unwrap().text;
    assert!(text.contains("class Local /* CaptureLocal$1Local */ {"), "{text}");
    assert!(text.contains("return base + extra;"), "{text}");
    assert!(text.contains("return new Local().value();"), "{text}");
    assert_eq!(text.matches("/* CaptureLocal$1Local */").count(), 1, "{text}");
    assert!(text.contains("class [declaration] CaptureLocal$1Local\n"), "{text}");
}

#[test]
fn local_class_cannot_recover_a_capture_from_a_mutating_slot() {
    let (outer, local) = inputs(true);
    let error = decompile_group(&outer, [&local[..]], &Options::default()).unwrap_err();
    assert!(error.to_string().contains("effectively final"));
}

#[test]
fn qualified_new_checks_receiver_before_evaluating_explicit_arguments() {
    let (outer, inner) = qualified_inputs();
    let source = decompile_group(&outer, [&inner[..]], &Options::default()).unwrap();

    assert!(source.text.contains("return outer.new Inner(Outer.argument());"), "{}", source.text);
    assert!(!source.text.contains("requireNonNull"), "{}", source.text);
}

#[test]
fn qualified_new_proof_does_not_cross_an_exception_boundary_or_a_receiver_replacement() {
    use crate::{ClassGroup, bytecode::decode, classfile::ExceptionHandler};
    use crate::lift::qualified_new::mask_guards;
    let (outer, inner) = qualified_inputs();
    let group = ClassGroup::new([&outer[..], &inner[..]]).unwrap();
    let class = group.get("Outer").unwrap();
    let method = &class.methods[0];
    let code = method.code(&class.pool).unwrap().unwrap();
    let original = decode(code.bytes).unwrap();

    let mut protected = original.clone();
    let call = u16::try_from(original[4].offset).unwrap();
    let ret = u16::try_from(original.last().unwrap().offset).unwrap();
    let handlers = [ExceptionHandler { start_pc: call, end_pc: ret, handler_pc: ret, catch_type: 0 }];
    mask_guards(class, method, &group, &mut protected, &handlers).unwrap();
    assert_eq!(protected, original);

    // Pop the checked qualifier and replace it independently. The method's
    // constructor still has a well-formed operand stack, but its guard is
    // independent of the actual enclosing instance.
    let replaced_at = original[6].offset as usize;
    let mut bytes = code.bytes[..replaced_at].to_vec();
    bytes.extend([0x57, 0x01]); // pop; aconst_null
    bytes.extend(&code.bytes[replaced_at..]);
    let mut changed = decode(&bytes).unwrap();
    mask_guards(class, method, &group, &mut changed, &[]).unwrap();
    assert_eq!(changed[3].opcode, 0x59);
    assert_eq!(changed[4].opcode, 0xb8);
}

fn qualified_inputs() -> (Vec<u8>, Vec<u8>) {
    let mut outer = Pool::default();
    let class = outer.class("Outer");
    let object = outer.class("java/lang/Object");
    let inner = outer.class("Outer$Inner");
    let objects = outer.class("java/util/Objects");
    let constructor = outer.member(10, inner, "<init>", "(LOuter;I)V");
    let require_nonnull = outer.member(10, objects, "requireNonNull", "(Ljava/lang/Object;)Ljava/lang/Object;");
    let argument = outer.member(10, class, "argument", "()I");
    let mut body = Vec::new();
    push_op(&mut body, 0xbb, inner);
    body.extend([0x59, 0x2a, 0x59]);
    push_op(&mut body, 0xb8, require_nonnull);
    body.push(0x57);
    push_op(&mut body, 0xb8, argument);
    push_op(&mut body, 0xb7, constructor);
    body.push(0xb0);
    let parameter = outer.utf8("outer");
    let parameter_type = outer.utf8("LOuter;");
    let variables = outer.attribute("LocalVariableTable", &words(&[1, 0, body.len() as u16, parameter, parameter_type, 0]));
    let make_code = outer.code(4, 1, &body, &[variables]);
    let make_name = outer.utf8("make");
    let make_type = outer.utf8("(LOuter;)LOuter$Inner;");
    let argument_name = outer.utf8("argument");
    let argument_type = outer.utf8("()I");
    let argument_code = outer.code(1, 0, &[0x10, 7, 0xac], &[]);
    let simple = outer.utf8("Inner");
    let relationship = outer.attribute("InnerClasses", &words(&[1, inner, class, simple, 1]));
    let outer = outer.classfile(class, object, &[], &[
        member(0x0008, make_name, make_type, &[make_code]),
        member(0x0008, argument_name, argument_type, &[argument_code]),
    ], &[relationship]);

    let mut inner = Pool::default();
    let class = inner.class("Outer$Inner");
    let enclosing = inner.class("Outer");
    let object = inner.class("java/lang/Object");
    let init = inner.member(10, object, "<init>", "()V");
    let mut body = vec![0x2a];
    push_op(&mut body, 0xb7, init);
    body.push(0xb1);
    let code = inner.code(1, 3, &body, &[]);
    let name = inner.utf8("<init>");
    let ty = inner.utf8("(LOuter;I)V");
    let simple = inner.utf8("Inner");
    let relationship = inner.attribute("InnerClasses", &words(&[1, class, enclosing, simple, 1]));
    let inner = inner.classfile(class, object, &[], &[member(1, name, ty, &[code])], &[relationship]);
    (outer, inner)
}

fn inputs(mutate: bool) -> (Vec<u8>, Vec<u8>) {
    let mut outer = Pool::default();
    let class = outer.class("CaptureLocal");
    let object = outer.class("java/lang/Object");
    let local_class = outer.class(LOCAL);
    let constructor = outer.member(10, local_class, "<init>", "(II)V");
    let value = outer.member(10, local_class, "value", "()I");
    let read = outer.utf8("read");
    let read_type = outer.utf8("(I)I");
    let mut body = vec![0x1a, 0x06, 0x60, 0x3c];
    let local_scope = body.len() as u16;
    if mutate {
        body.extend([0x84, 1, 1]);
    }
    push_op(&mut body, 0xbb, local_class);
    body.extend([0x59, 0x1a, 0x1b]);
    push_op(&mut body, 0xb7, constructor);
    push_op(&mut body, 0xb6, value);
    body.push(0xac);
    let finish = body.len() as u16;
    let base = outer.utf8("base");
    let extra = outer.utf8("extra");
    let int = outer.utf8("I");
    let local_vars = outer.attribute(
        "LocalVariableTable",
        &words(&[
            2,
            0,
            finish,
            base,
            int,
            0,
            local_scope,
            finish - local_scope,
            extra,
            int,
            1,
        ]),
    );
    let code = outer.code(4, 2, &body, &[local_vars]);
    let simple = outer.utf8("Local");
    let inner = outer.attribute("InnerClasses", &words(&[1, local_class, 0, simple, 0]));
    let outer = outer.classfile(
        class,
        object,
        &[],
        &[member(0x0008, read, read_type, &[code])],
        &[inner],
    );

    let mut local = Pool::default();
    let class = local.class(LOCAL);
    let object = local.class("java/lang/Object");
    let enclosing = local.class("CaptureLocal");
    let read = local.name_and_type("read", "(I)I");
    let enclosing_method = local.attribute("EnclosingMethod", &words(&[enclosing, read]));
    let simple = local.utf8("Local");
    let inner = local.attribute("InnerClasses", &words(&[1, class, 0, simple, 0]));
    let init = local.utf8("<init>");
    let empty = local.member(10, object, "<init>", "()V");
    let explicit = local.member(10, class, "<init>", "(III)V");
    let base = local.member(9, class, "val$base", "I");
    let extra = local.member(9, class, "val$extra", "I");
    let mut primary = vec![0x2a, 0x1c];
    push_op(&mut primary, 0xb5, base);
    primary.extend([0x2a, 0x1d]);
    push_op(&mut primary, 0xb5, extra);
    primary.push(0x2a);
    push_op(&mut primary, 0xb7, empty);
    primary.push(0xb1);
    let ignored = local.utf8("ignored");
    let int = local.utf8("I");
    let local_vars = local.attribute(
        "LocalVariableTable",
        &words(&[1, 0, primary.len() as u16, ignored, int, 1]),
    );
    let primary_code = local.code(2, 4, &primary, &[local_vars]);
    let primary_type = local.utf8("(III)V");
    let mut delegate = vec![0x2a, 0x04, 0x1b, 0x1c];
    push_op(&mut delegate, 0xb7, explicit);
    delegate.push(0xb1);
    let delegate_code = local.code(4, 3, &delegate, &[]);
    let delegate_type = local.utf8("(II)V");
    let mut getter = vec![0x2a];
    push_op(&mut getter, 0xb4, base);
    getter.push(0x2a);
    push_op(&mut getter, 0xb4, extra);
    getter.extend([0x60, 0xac]);
    let getter_code = local.code(2, 1, &getter, &[]);
    let getter_name = local.utf8("value");
    let getter_type = local.utf8("()I");
    let base_name = local.utf8("val$base");
    let extra_name = local.utf8("val$extra");
    let fields = [
        member(0x1010, base_name, int, &[]),
        member(0x1010, extra_name, int, &[]),
    ];
    let methods = [
        member(0, init, delegate_type, &[delegate_code]),
        member(0, init, primary_type, &[primary_code]),
        member(0, getter_name, getter_type, &[getter_code]),
    ];
    let local = local.classfile(class, object, &fields, &methods, &[inner, enclosing_method]);
    (outer, local)
}

#[derive(Default)]
struct Pool {
    count: u16,
    data: Vec<u8>,
}

impl Pool {
    fn item(&mut self, tag: u8, payload: &[u8]) -> u16 {
        self.count += 1;
        self.data.push(tag);
        self.data.extend(payload);
        self.count
    }

    fn utf8(&mut self, text: &str) -> u16 {
        let mut payload = words(&[text.len() as u16]);
        payload.extend(text.bytes());
        self.item(1, &payload)
    }

    fn class(&mut self, name: &str) -> u16 {
        let index = self.utf8(name);
        self.item(7, &index.to_be_bytes())
    }

    fn name_and_type(&mut self, name: &str, ty: &str) -> u16 {
        let name = self.utf8(name);
        let ty = self.utf8(ty);
        self.item(12, &words(&[name, ty]))
    }

    fn member(&mut self, tag: u8, owner: u16, name: &str, ty: &str) -> u16 {
        let name_and_type = self.name_and_type(name, ty);
        self.item(tag, &words(&[owner, name_and_type]))
    }

    fn attribute(&mut self, name: &str, payload: &[u8]) -> Vec<u8> {
        let mut result = words(&[self.utf8(name)]);
        result.extend((payload.len() as u32).to_be_bytes());
        result.extend(payload);
        result
    }

    fn code(&mut self, stack: u16, locals: u16, bytes: &[u8], attributes: &[Vec<u8>]) -> Vec<u8> {
        let mut payload = words(&[stack, locals]);
        payload.extend((bytes.len() as u32).to_be_bytes());
        payload.extend(bytes);
        payload.extend(words(&[0]));
        table(&mut payload, attributes);
        self.attribute("Code", &payload)
    }

    fn classfile(
        self,
        class: u16,
        object: u16,
        fields: &[Vec<u8>],
        methods: &[Vec<u8>],
        attributes: &[Vec<u8>],
    ) -> Vec<u8> {
        let mut out = vec![0xca, 0xfe, 0xba, 0xbe];
        out.extend(words(&[0, 52, self.count + 1]));
        out.extend(self.data);
        out.extend(words(&[0x0020, class, object, 0]));
        table(&mut out, fields);
        table(&mut out, methods);
        table(&mut out, attributes);
        out
    }
}

fn table(out: &mut Vec<u8>, entries: &[Vec<u8>]) {
    out.extend(words(&[entries.len() as u16]));
    for entry in entries {
        out.extend(entry);
    }
}

fn member(flags: u16, name: u16, ty: u16, attributes: &[Vec<u8>]) -> Vec<u8> {
    let mut bytes = words(&[flags, name, ty]);
    table(&mut bytes, attributes);
    bytes
}

fn words(values: &[u16]) -> Vec<u8> {
    values.iter().flat_map(|word| word.to_be_bytes()).collect()
}

fn push_op(out: &mut Vec<u8>, op: u8, operand: u16) {
    out.push(op);
    out.extend(operand.to_be_bytes());
}
