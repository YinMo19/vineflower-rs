use std::{io, sync::Arc};

use crate::{
    ClassGroup, Options,
    classfile::Code,
    classpath::{ClassDataProvider, ClassPath},
    descriptor::Primitive,
    naming::MemberRenames,
};

use super::*;

const CALLER: &str = "fixture/Caller";
const PARENT: &str = "fixture/Parent";
const OBJECT_ARG: &str = "(Ljava/lang/Object;)V";
const STRING_ARG: &str = "(Ljava/lang/String;)V";
const STATIC_PUBLIC: u16 = STATIC | 1;

type Method<'a> = (u16, &'a str, &'a str, Option<&'a str>);

fn class(name: &str, parent: Option<&str>, flags: u16, methods: &[Method<'_>]) -> Vec<u8> {
    fn words(bytes: &mut Vec<u8>, values: &[u16]) {
        for value in values {
            bytes.extend(value.to_be_bytes());
        }
    }
    fn utf8(pool: &mut Vec<u8>, count: &mut u16, text: &str) -> u16 {
        let index = *count;
        *count += 1;
        pool.push(1);
        words(pool, &[text.len().try_into().unwrap()]);
        pool.extend(text.as_bytes());
        index
    }
    fn classname(pool: &mut Vec<u8>, count: &mut u16, name: &str) -> u16 {
        let text = utf8(pool, count, name);
        let index = *count;
        *count += 1;
        pool.push(7);
        words(pool, &[text]);
        index
    }
    let mut pool = Vec::new();
    let mut count = 1;
    let this = classname(&mut pool, &mut count, name);
    let parent = parent.map_or(0, |parent| classname(&mut pool, &mut count, parent));
    let mut declarations = Vec::new();
    for &(flags, name, descriptor, signature) in methods {
        let name = utf8(&mut pool, &mut count, name);
        let descriptor = utf8(&mut pool, &mut count, descriptor);
        words(
            &mut declarations,
            &[flags, name, descriptor, u16::from(signature.is_some())],
        );
        if let Some(signature) = signature {
            let attribute = utf8(&mut pool, &mut count, "Signature");
            let signature = utf8(&mut pool, &mut count, signature);
            words(&mut declarations, &[attribute, 0, 2, signature]);
        }
    }
    let mut bytes = 0xcafebabeu32.to_be_bytes().to_vec();
    words(&mut bytes, &[0, 52, count]);
    bytes.extend(pool);
    words(
        &mut bytes,
        &[
            flags | 0x0021,
            this,
            parent,
            0,
            0,
            methods.len().try_into().unwrap(),
        ],
    );
    bytes.extend(declarations);
    words(&mut bytes, &[0]);
    bytes
}

fn with_machine(classes: &[&[u8]], options: &Options, check: impl FnOnce(Machine<'_, '_>)) {
    let caller = class(
        CALLER,
        Some(OBJECT),
        0,
        &[(STATIC_PUBLIC, "test", "()V", None)],
    );
    let group =
        ClassGroup::new(std::iter::once(caller.as_slice()).chain(classes.iter().copied())).unwrap();
    let caller = group.get(CALLER).unwrap();
    let renames = MemberRenames::build(&group, options).unwrap();
    let code = Code {
        max_stack: 8,
        max_locals: 8,
        bytes: &[],
        exceptions: vec![],
        attributes: vec![],
    };
    let descriptor = MethodDescriptor::parse("()V").unwrap();
    let mut machine = Machine::new(
        caller,
        &caller.methods[0],
        &code,
        &descriptor,
        options,
        &str::to_owned,
    )
    .unwrap()
    .with_group(&group);
    machine.set_member_renames(&renames);
    check(machine);
}

fn reference(name: &str) -> Expr {
    Expr::atom(Type::Object(name.into()), "argument".into())
}

fn omit(
    machine: &Machine<'_, '_>,
    lookup: &str,
    owner: &str,
    name: &str,
    desc: &str,
    args: &[Expr],
    opcode: u8,
) -> bool {
    machine.omit_invocation_casts(
        lookup,
        (owner, name, desc),
        &MethodDescriptor::parse(desc).unwrap(),
        args,
        opcode,
    )
}

#[test]
fn string_equals_uses_platform_contract_only_without_a_definition() {
    let options = Options::default();
    let args = [reference(STRING)];
    let equals = |machine: Machine<'_, '_>| {
        assert!(omit(
            &machine, STRING, STRING, "equals", EQUALS, &args, 0xb6
        ))
    };
    with_machine(&[], &options, equals);

    let object = class(OBJECT, None, 0, &[(1, "equals", EQUALS, None)]);
    let string = class(STRING, Some(OBJECT), FINAL, &[(1, "equals", EQUALS, None)]);
    with_machine(&[&object, &string], &options, equals);
    let string = class(
        STRING,
        Some(OBJECT),
        FINAL,
        &[
            (1, "equals", EQUALS, None),
            (1, "equals", "(Ljava/lang/String;)Z", None),
        ],
    );
    with_machine(&[&object, &string], &options, |machine| {
        assert!(!omit(
            &machine, STRING, STRING, "equals", EQUALS, &args, 0xb6
        ));
    });
    let object = class(
        OBJECT,
        None,
        0,
        &[
            (1, "equals", EQUALS, None),
            (1, "equals", "(Ljava/lang/String;)Z", None),
        ],
    );
    with_machine(&[&object], &options, |machine| {
        assert!(!omit(
            &machine, STRING, STRING, "equals", EQUALS, &args, 0xb6
        ));
    });
}

#[test]
fn uses_the_rendered_receiver_hierarchy_and_checks_exact_arity() {
    let child = "fixture/Child";
    let parent = class(PARENT, Some(OBJECT), 0, &[(1, "accept", OBJECT_ARG, None)]);
    let mut children = Vec::new();
    children.push((
        class(child, Some(PARENT), 0, &[(1, "accept", STRING_ARG, None)]),
        false,
    ));
    children.push((
        class(child, Some(PARENT), 0, &[(1, "accept", "()V", None)]),
        true,
    ));
    for (child_bytes, expected) in children {
        with_machine(&[&parent, &child_bytes], &Options::default(), |machine| {
            assert_eq!(
                omit(
                    &machine,
                    child,
                    PARENT,
                    "accept",
                    OBJECT_ARG,
                    &[reference(STRING)],
                    0xb6
                ),
                expected
            );
        });
    }
    let child_bytes = class(child, Some(PARENT), 0, &[(1, "accept", OBJECT_ARG, None)]);
    with_machine(&[&child_bytes], &Options::default(), |machine| {
        assert!(!omit(
            &machine,
            child,
            child,
            "accept",
            OBJECT_ARG,
            &[reference(STRING)],
            0xb6
        ));
    });
}

#[test]
fn checks_strict_applicability_without_removing_other_conversions() {
    let boxed = "java/lang/Integer";
    let boxed_class = class(boxed, Some(OBJECT), FINAL, &[]);
    let methods = [
        (STATIC_PUBLIC, "accept", OBJECT_ARG, None),
        (STATIC_PUBLIC, "accept", "(I)V", None),
        (STATIC_PUBLIC, "accept", "(Ljava/lang/Integer;)V", None),
        (
            STATIC_PUBLIC | VARARGS,
            "accept",
            "(Ljava/lang/String;[Ljava/lang/Object;)V",
            None,
        ),
    ];
    let parent = class(PARENT, Some(OBJECT), 0, &methods);
    with_machine(&[&boxed_class, &parent], &Options::default(), |machine| {
        let call = |value| {
            omit(
                &machine,
                PARENT,
                PARENT,
                "accept",
                OBJECT_ARG,
                &[value],
                0xb8,
            )
        };
        assert!(call(reference(STRING))); // Other final class and primitive are inapplicable.
        assert!(!call(reference(boxed))); // Explicit boxing must still select accept(Object).
        let null = Expr {
            source: Source::Null,
            ..reference(OBJECT)
        };
        assert!(!call(null));
        assert!(
            !machine.can_pass_argument_implicitly(&reference(OBJECT), &Type::Object(STRING.into()))
        );
        assert!(
            !machine
                .can_pass_argument_implicitly(&Expr::integer(1), &Type::Primitive(Primitive::Long))
        );
    });
}

#[test]
fn checks_the_type_before_the_final_widening_and_keeps_typed_null_for_overloads() {
    let parent = class(
        PARENT,
        Some(OBJECT),
        0,
        &[
            (STATIC_PUBLIC, "only", "(D)V", None),
            (STATIC_PUBLIC, "overloaded", "(D)V", None),
            (STATIC_PUBLIC, "overloaded", "(F)V", None),
            (STATIC_PUBLIC, "reference", STRING_ARG, None),
        ],
    );
    with_machine(&[&parent], &Options::default(), |machine| {
        let double = Type::Primitive(Primitive::Double);
        let mut value = Expr {
            source: Source::WidenedPrimitive {
                operand_type: Primitive::Float,
                operand_precedence: super::super::expr::UNARY,
            },
            ..Expr::atom(double.clone(), "(double)(float)input".into())
        };
        for (name, expected) in [("only", true), ("overloaded", false)] {
            assert_eq!(
                omit(&machine, PARENT, PARENT, name, "(D)V", std::slice::from_ref(&value), 0xb8),
                expected
            );
        }
        assert!(value.elide_final_widening(&double));
        assert_eq!(value.text.as_flat(), "(float)input");

        let null = Expr { source: Source::Null, ..Expr::atom(Type::Object(OBJECT.into()), "null".into()) };
        let args = [null];
        assert!(omit(&machine, PARENT, PARENT, "reference", STRING_ARG, &args, 0xb8));
        assert!(!omit(
            &machine, STRING, STRING, "valueOf",
            "(Ljava/lang/Object;)Ljava/lang/String;", &args, 0xb8
        ));
    });
}

#[test]
fn preserves_varargs_selection_and_removes_casts_to_a_more_specific_fixed_overload() {
    let parent = class(
        PARENT,
        Some(OBJECT),
        0,
        &[
            (STATIC_PUBLIC, "accept", OBJECT_ARG, None),
            (
                STATIC_PUBLIC | VARARGS,
                "accept",
                "([Ljava/lang/Object;)V",
                None,
            ),
            (STATIC_PUBLIC, "prefer", "([Ljava/lang/Object;)V", None),
            (STATIC_PUBLIC, "prefer", OBJECT_ARG, None),
        ],
    );
    let strings = || {
        Expr::atom(
            Type::parse("[Ljava/lang/String;").unwrap(),
            "strings".into(),
        )
    };
    with_machine(&[&parent], &Options::default(), |machine| {
        assert!(!omit(
            &machine,
            PARENT,
            PARENT,
            "accept",
            OBJECT_ARG,
            &[strings()],
            0xb8
        ));
        assert!(!omit(
            &machine,
            PARENT,
            PARENT,
            "accept",
            "([Ljava/lang/Object;)V",
            &[strings()],
            0xb8
        ));
        assert!(omit(
            &machine,
            PARENT,
            PARENT,
            "prefer",
            "([Ljava/lang/Object;)V",
            &[strings()],
            0xb8
        ));
    });
}

#[test]
fn follows_source_aliases_and_does_not_guess_generic_formals() {
    let parent = class(
        PARENT,
        Some(OBJECT),
        0,
        &[
            (STATIC_PUBLIC, "a", OBJECT_ARG, None),
            (STATIC_PUBLIC, "a", STRING_ARG, None),
            (
                STATIC_PUBLIC,
                "accept",
                OBJECT_ARG,
                Some("<T:Ljava/lang/Object;>(TT;)V"),
            ),
            (
                1,
                "lookup",
                "(Ljava/lang/Object;)Ljava/lang/Object;",
                Some("(Ljava/lang/Object;)TT;"),
            ),
        ],
    );
    let check = |machine: Machine<'_, '_>, expected| {
        let args = [reference(STRING)];
        assert_eq!(
            omit(&machine, PARENT, PARENT, "a", OBJECT_ARG, &args, 0xb8),
            expected
        );
        assert!(!omit(
            &machine, PARENT, PARENT, "accept", OBJECT_ARG, &args, 0xb8
        ));
        assert!(omit(
            &machine,
            PARENT,
            PARENT,
            "lookup",
            "(Ljava/lang/Object;)Ljava/lang/Object;",
            &args,
            0xb6
        ));
    };
    with_machine(&[&parent], &Options::default(), |machine| {
        check(machine, false)
    });
    let options = Options {
        rename_members: true,
        ..Options::default()
    };
    with_machine(&[&parent], &options, |machine| check(machine, true));
}

#[derive(Debug)]
struct Library {
    name: &'static str,
    bytes: Arc<[u8]>,
}

impl ClassDataProvider for Library {
    fn load(&self, name: &str) -> io::Result<Option<Arc<[u8]>>> {
        Ok((name == self.name).then(|| Arc::clone(&self.bytes)))
    }
}

#[test]
fn classpath_availability_and_read_errors_are_distinct() {
    let mut path = ClassPath::new();
    path.add_provider(Library {
        name: PARENT,
        bytes: class(
            PARENT,
            Some(OBJECT),
            0,
            &[(STATIC_PUBLIC, "accept", OBJECT_ARG, None)],
        )
        .into(),
    });
    path.add_provider(Library {
        name: STRING,
        bytes: Arc::from(&b"invalid"[..]),
    });
    let options = Options {
        library_classpath: Some(Arc::new(path)),
        ..Options::default()
    };
    with_machine(&[], &options, |machine| {
        let args = [reference(STRING)];
        assert!(omit(
            &machine, PARENT, PARENT, "accept", OBJECT_ARG, &args, 0xb8
        ));
        assert!(!omit(
            &machine, STRING, STRING, "equals", EQUALS, &args, 0xb6
        ));
    });
}
