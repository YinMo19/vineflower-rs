// Based on the Vineflower ConverterHelper and IdentifierConverter contracts (Apache-2.0).

use super::*;
use crate::ClassGroupBuilder;

const OBJECT: &str = "java/lang/Object";
const ABSTRACT: u16 = 0x0400;
const SUPER: u16 = 0x0020;

type MemberSpec<'a> = (&'a str, &'a str, u16);

#[derive(Default)]
struct ClassSpec<'a> {
    name: &'a str,
    parent: Option<&'a str>,
    flags: u16,
    interfaces: &'a [&'a str],
    fields: &'a [MemberSpec<'a>],
    methods: &'a [MemberSpec<'a>],
    inner: &'a [(&'a str, &'a str, &'a str)],
}

impl<'a> ClassSpec<'a> {
    fn named(name: &'a str) -> Self {
        Self {
            name,
            parent: Some(OBJECT),
            flags: PUBLIC | SUPER,
            ..Self::default()
        }
    }

    fn bytes(&self) -> Vec<u8> {
        #[derive(Default)]
        struct Pool {
            count: u16,
            bytes: Vec<u8>,
        }
        impl Pool {
            fn utf8(&mut self, value: &str) -> u16 {
                self.count += 1;
                self.bytes.push(1);
                word(&mut self.bytes, value.len() as u16);
                self.bytes.extend(value.bytes());
                self.count
            }
            fn class(&mut self, name: &str) -> u16 {
                let utf8 = self.utf8(name);
                self.count += 1;
                self.bytes.push(7);
                word(&mut self.bytes, utf8);
                self.count
            }
            fn members(&mut self, values: &[MemberSpec<'_>], bytes: &mut Vec<u8>) {
                word(bytes, values.len() as u16);
                for &(name, descriptor, flags) in values {
                    word(bytes, flags);
                    word(bytes, self.utf8(name));
                    word(bytes, self.utf8(descriptor));
                    word(bytes, 0);
                }
            }
        }
        fn word(output: &mut Vec<u8>, n: u16) {
            output.extend(n.to_be_bytes());
        }
        let mut pool = Pool::default();
        let mut body = Vec::new();
        word(&mut body, self.flags);
        word(&mut body, pool.class(self.name));
        word(
            &mut body,
            self.parent.map_or(0, |parent| pool.class(parent)),
        );
        word(&mut body, self.interfaces.len() as u16);
        for interface in self.interfaces {
            word(&mut body, pool.class(interface));
        }
        pool.members(self.fields, &mut body);
        pool.members(self.methods, &mut body);
        if self.inner.is_empty() {
            word(&mut body, 0);
        } else {
            word(&mut body, 1);
            word(&mut body, pool.utf8("InnerClasses"));
            body.extend((2 + 8 * self.inner.len() as u32).to_be_bytes());
            word(&mut body, self.inner.len() as u16);
            for &(inner, outer, leaf) in self.inner {
                word(&mut body, pool.class(inner));
                word(&mut body, pool.class(outer));
                word(&mut body, pool.utf8(leaf));
                word(&mut body, PUBLIC | STATIC);
            }
        }
        let mut class = b"\xca\xfe\xba\xbe\0\0\0\x34".to_vec();
        word(&mut class, pool.count + 1);
        class.extend(pool.bytes);
        class.extend(body);
        class
    }
}

fn options() -> Options {
    Options {
        rename_members: true,
        ..Options::default()
    }
}

#[test]
fn aliases_follow_typed_references_and_do_not_collide_in_derived_scopes() {
    let base = ClassSpec {
        fields: &[("a", "I", PUBLIC), ("a", "J", PUBLIC)],
        methods: &[("a", "()V", PUBLIC), ("a", "(I)V", PUBLIC)],
        ..ClassSpec::named("pkg/BaseClass")
    }
    .bytes();
    let child = ClassSpec {
        parent: Some("pkg/BaseClass"),
        fields: &[("field_0", "I", PUBLIC), ("a", "J", PUBLIC)],
        methods: &[("method_0", "()V", PUBLIC), ("a", "()V", PUBLIC)],
        ..ClassSpec::named("pkg/ChildClass")
    }
    .bytes();
    let group = ClassGroup::new([base.as_slice(), child.as_slice()]).unwrap();
    let renames = MemberRenames::build(&group, &options()).unwrap();
    assert_eq!(
        renames.field_alias("pkg/BaseClass", "a", "I"),
        Some("field_1")
    );
    assert_eq!(
        renames.field_alias("pkg/BaseClass", "a", "J"),
        Some("field_2")
    );
    assert_eq!(renames.field_alias("pkg/ChildClass", "a", "I"), None);
    assert_eq!(renames.field_name("pkg/ChildClass", "a", "I"), "field_1");
    assert_eq!(renames.field_name("pkg/ChildClass", "a", "J"), "field_3");
    assert_eq!(
        renames.method_alias("pkg/BaseClass", "a", "()V"),
        Some("method_1")
    );
    assert_eq!(
        renames.method_alias("pkg/ChildClass", "a", "()V"),
        Some("method_1")
    );
    assert_eq!(renames.method_alias("pkg/ChildClass", "a", "(I)V"), None);
    assert_eq!(
        renames.method_name("pkg/ChildClass", "a", "(I)V"),
        "method_2"
    );
    assert_eq!(renames.method_name("pkg/UnknownClass", "a", "()V"), "a");
    assert_eq!(
        MemberRenames::default().field_alias("pkg/ChildClass", "a", "I"),
        None
    );
}

#[test]
fn virtual_families_share_interface_names_and_keep_external_or_native_contracts() {
    let first = ClassSpec {
        flags: PUBLIC | INTERFACE | ABSTRACT,
        fields: &[("a", "I", PUBLIC | STATIC)],
        methods: &[
            ("v", "()V", PUBLIC | ABSTRACT),
            ("x", "()V", PUBLIC | ABSTRACT),
        ],
        ..ClassSpec::named("pkg/FirstInterface")
    }
    .bytes();
    let second = ClassSpec {
        flags: PUBLIC | INTERFACE | ABSTRACT,
        methods: &[("v", "()V", PUBLIC | ABSTRACT)],
        ..ClassSpec::named("pkg/SecondInterface")
    }
    .bytes();
    let library = ClassSpec {
        fields: &[("a", "I", PUBLIC)],
        methods: &[("x", "()V", PUBLIC)],
        ..ClassSpec::named("library/ExternalBase")
    }
    .bytes();
    let concrete = ClassSpec {
        parent: Some("library/ExternalBase"),
        interfaces: &["pkg/FirstInterface", "pkg/SecondInterface"],
        methods: &[
            ("v", "()V", PUBLIC),
            ("n", "()V", PUBLIC | NATIVE),
            ("a", "()V", PRIVATE),
        ],
        ..ClassSpec::named("pkg/ConcreteClass")
    }
    .bytes();
    let child = ClassSpec {
        parent: Some("pkg/ConcreteClass"),
        methods: &[("n", "()V", PUBLIC), ("a", "()V", PRIVATE)],
        ..ClassSpec::named("pkg/ChildClass")
    }
    .bytes();
    let mut builder = ClassGroupBuilder::new();
    for source in [&first, &second, &concrete, &child] {
        builder.add(source).unwrap();
    }
    builder.add_library(&library).unwrap();
    let group = builder.build().unwrap();
    let renames = MemberRenames::build(&group, &options()).unwrap();
    for class in [
        "pkg/FirstInterface",
        "pkg/SecondInterface",
        "pkg/ConcreteClass",
        "pkg/ChildClass",
    ] {
        assert_eq!(renames.method_name(class, "v", "()V"), "method_0");
    }
    assert_eq!(renames.method_alias("pkg/FirstInterface", "x", "()V"), None);
    assert_eq!(renames.method_alias("pkg/ConcreteClass", "n", "()V"), None);
    assert_eq!(renames.method_alias("pkg/ChildClass", "n", "()V"), None);
    assert_eq!(
        renames.method_alias("pkg/ConcreteClass", "a", "()V"),
        Some("method_1")
    );
    assert_eq!(
        renames.method_alias("pkg/ChildClass", "a", "()V"),
        Some("method_2")
    );
    assert_eq!(renames.field_alias("library/ExternalBase", "a", "I"), None);
    assert_eq!(renames.field_name("pkg/ConcreteClass", "a", "I"), "field_0");
}

#[test]
fn member_class_alias_order_is_independent_of_method_allocation_order() {
    let alpha = ClassSpec {
        methods: &[("a", "()V", PUBLIC)],
        ..ClassSpec::named("pkg/Owner$a")
    }
    .bytes();
    let beta = ClassSpec {
        methods: &[("a", "()V", PUBLIC)],
        ..ClassSpec::named("pkg/Owner$b")
    }
    .bytes();
    let owner = ClassSpec {
        inner: &[
            ("pkg/Owner$b", "pkg/Owner", "b"),
            ("pkg/Owner$a", "pkg/Owner", "a"),
        ],
        ..ClassSpec::named("pkg/Owner")
    }
    .bytes();
    let group = ClassGroup::new([alpha.as_slice(), beta.as_slice(), owner.as_slice()]).unwrap();
    let renames = MemberRenames::build(&group, &options()).unwrap();
    assert_eq!(renames.simple_class_alias("pkg/Owner$a"), Some("class_1"));
    assert_eq!(renames.class_name("pkg/Owner$a"), "pkg/Owner$class_1");
    assert_eq!(
        renames.method_alias("pkg/Owner$a", "a", "()V"),
        Some("method_0")
    );
    assert_eq!(renames.simple_class_alias("pkg/Owner$b"), Some("class_0"));
    assert_eq!(
        renames.method_alias("pkg/Owner$b", "a", "()V"),
        Some("method_1")
    );
}

#[test]
fn enclosing_binary_alias_is_reused_even_when_nested_leaf_does_not_change() {
    let child = ClassSpec::named("pkg/a$Readable").bytes();
    let owner = ClassSpec {
        inner: &[("pkg/a$Readable", "pkg/a", "Readable")],
        ..ClassSpec::named("pkg/a")
    }
    .bytes();
    let occupied = ClassSpec::named("pkg/class_0").bytes();
    let group = ClassGroup::new([child.as_slice(), owner.as_slice(), occupied.as_slice()]).unwrap();
    let renames = MemberRenames::build(&group, &options()).unwrap();
    assert_eq!(renames.simple_class_alias("pkg/a"), Some("class_1"));
    assert_eq!(renames.simple_class_alias("pkg/a$Readable"), None);
    assert_eq!(renames.class_name("pkg/a$Readable"), "pkg/class_1$Readable");
}
