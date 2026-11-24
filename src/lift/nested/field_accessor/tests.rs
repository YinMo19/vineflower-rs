use crate::{
    bytecode::decode,
    descriptor::Primitive,
    lift::expr::Order,
    options::Options,
};

use super::*;

const CLASS: &[u8] = include_bytes!("../../../../tests/smoke/java8/TestSyntheticAccess.class");
const OWNER: &str = "pkg/TestSyntheticAccess";
const SETTER: &str = "(Lpkg/TestSyntheticAccess;I)I";
const UPDATE: &str = "(Lpkg/TestSyntheticAccess;)I";

fn prove(class: &ClassFile<'_>, owner: &str, signature: &str, ops: &[u8]) -> Option<Action> {
    FieldAccessor::recognize(
        class,
        owner,
        &MethodDescriptor::parse(signature).unwrap(),
        &decode(ops).unwrap(),
        5,
    )
    .unwrap()
    .map(|field| field.action)
}

#[test]
fn retained_value_must_be_the_exact_field_store_operand() {
    let mut class = ClassFile::parse(CLASS).unwrap();
    let setter = [0x2a, 0x1b, 0x5a, 0xb5, 0, 2]; // i:I from the exact Java 8 input
    assert!(matches!(prove(&class, OWNER, SETTER, &setter), Some(Action::WriteValue(Form::Assign))));
    assert!(prove(&class, "pkg/Other", SETTER, &setter).is_none());
    assert!(prove(&class, OWNER, "(Lpkg/TestSyntheticAccess;S)I", &setter).is_none());
    assert!(prove(&class, OWNER, "(Lpkg/TestSyntheticAccess;I)V", &setter).is_none());
    assert!(prove(&class, OWNER, SETTER, &[0x2a, 0x1a, 0x5a, 0xb5, 0, 2]).is_none());
    assert!(prove(&class, OWNER, SETTER, &[0x2a, 0x1b, 0x59, 0xb5, 0, 2]).is_none());

    let field = class.fields.iter_mut().find(|field| class.pool.utf8(field.name_index).unwrap() == "i").unwrap();
    field.access_flags |= 0x0010;
    assert!(prove(&class, OWNER, SETTER, &setter).is_none());
}

#[test]
fn leading_and_trailing_dup_return_old_and_new_value_respectively() {
    let class = ClassFile::parse(CLASS).unwrap();
    let postfix = [0x2a, 0x59, 0xb4, 0, 2, 0x5a, 0x04, 0x60, 0xb5, 0, 2];
    let prefix = [0x2a, 0x59, 0xb4, 0, 2, 0x04, 0x60, 0x5a, 0xb5, 0, 2];
    for (expected, mut body) in [(true, postfix), (false, prefix)] {
        assert!(matches!(prove(&class, OWNER, UPDATE, &body),
            Some(Action::WriteValue(Form::Increment { text: "++", postfix })) if postfix == expected));
        body[4] = 1; // s:I is not the field being written
        assert!(prove(&class, OWNER, UPDATE, &body).is_none());
    }
}

#[test]
fn update_needs_the_typed_dup_literal_and_narrowing() {
    let class = ClassFile::parse(CLASS).unwrap();
    let int = Type::Primitive(Primitive::Int);
    let byte = Type::Primitive(Primitive::Byte);
    let long = Type::Primitive(Primitive::Long);
    for (ty, body, expected) in [
        (&byte, &[0x04, 0x64, 0x91, 0x5a][..], true),
        (&byte, &[0x04, 0x64, 0x92, 0x5a][..], false),
        (&byte, &[0x04, 0x64, 0x5a][..], false),
        (&int, &[0x05, 0x64, 0x5a][..], false),
        (&int, &[0x04, 0x64, 0x5a, 0x00][..], false),
        (&long, &[0x0a, 0x65, 0x5d][..], true),
        (&long, &[0x0a, 0x65, 0x5a][..], false),
    ] {
        assert_eq!(increment(&class.pool, ty, 1, &decode(body).unwrap(), 5).is_some(), expected);
    }
}

#[test]
fn retained_assignment_keeps_one_receiver_and_evaluates_it_before_rhs() {
    let class = ClassFile::parse(CLASS).unwrap();
    let method = class
        .methods
        .iter()
        .find(|method| class.pool.utf8(method.name_index).unwrap() == "access$002")
        .unwrap();
    let code = method.code(&class.pool).unwrap().unwrap();
    let signature = MethodDescriptor::parse(SETTER).unwrap();
    let options = Options::default();
    let mut machine = Machine::new(&class, method, &code, &signature, &options, &str::to_owned)
        .unwrap();
    machine.offset = 10;
    let instructions = decode(code.bytes).unwrap();
    let recognize = || {
        FieldAccessor::recognize(
            &class, OWNER, &signature, &instructions[..instructions.len() - 1], code.max_stack,
        ).unwrap().unwrap()
    };
    let args = [
        Expr {
            order: Some(Order::at(2)),
            observable: true,
            ..Expr::atom(signature.parameters[0].clone(), "receiver()".into())
        },
        Expr {
            order: Some(Order::at(5)),
            observable: true,
            ..Expr::atom(signature.parameters[1].clone(), "rhs()".into())
        },
    ];
    assert!(matches!(
        machine.emit_field_accessor(OWNER, &signature, &args, recognize()).unwrap(),
        Effect::None
    ));
    let value = machine.pop_raw().unwrap();
    assert_eq!(value.text.as_str(), "receiver().i = rhs()");
    assert_eq!(value.ty, signature.return_type);
    assert!(value.observable && value.statement);

    let mut args = args;
    args[0].order = Some(Order::at(6));
    assert!(machine.emit_field_accessor(OWNER, &signature, &args, recognize()).is_err());
}
