// SPDX-License-Identifier: Apache-2.0

use std::fmt::Write;
use std::sync::Arc;

use vineflower_rs::{
    code::code_constants::{CONSTANT_FIELDREF, CONSTANT_INTERFACEMETHODREF, CONSTANT_METHODREF},
    engine::{Cx, Options, class_nodes::load_classes},
    renamer::{ConverterHelper, IdentifierKind, IdentifierRenamer, rename, rename_inner_class},
    structs::{StructContext, consts::PooledConstant},
};

use crate::upstream_reference;

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn identifier_rename_matches_upstream_hierarchy_and_pool() {
    let scratch = tempfile::tempdir().unwrap();
    let oracle = upstream_reference::Corpus::discover().run(
        "IdentifierRenameReference",
        &[],
        scratch.path(),
    );
    let options = Arc::new(Options::default());
    let mut context = StructContext::new(Arc::clone(&options), None);
    context
        .add_file(&scratch.path().join("library.jar"), false)
        .unwrap();
    context
        .add_file(&scratch.path().join("source.jar"), true)
        .unwrap();
    let originals = context.get_own_classes();
    let mut helper = Trace::default();
    rename(&mut context, &mut helper).unwrap();
    let mut cx = Cx::new(Arc::new(context));
    cx.class_nodes = load_classes(
        &cx.struct_context,
        &options,
        |_| true,
        |_| true,
        |owner, simple| rename_inner_class(&mut helper, owner, simple),
    );
    let interceptor = cx.pool_interceptor.as_ref().unwrap();
    let mut actual = helper.calls;
    let mapping = |actual: &mut String, original: &str| {
        if let Some(renamed) = interceptor.get_name(original) {
            writeln!(actual, "mapping|{original}|{renamed}").unwrap();
            assert_eq!(interceptor.get_old_name(renamed), Some(original));
        }
    };
    for class in originals {
        let owner = &class.qualified_name;
        mapping(&mut actual, owner);
        for method in &class.methods {
            mapping(
                &mut actual,
                &format!("{owner} {} {}", method.name, method.descriptor),
            );
        }
        for field in &class.fields {
            mapping(
                &mut actual,
                &format!("{owner} {} {}", field.name, field.descriptor),
            );
        }
        let renamed = cx.struct_context.get_class(owner).unwrap();
        assert!(Arc::ptr_eq(
            &renamed,
            &cx.struct_context
                .get_class(&renamed.qualified_name)
                .unwrap()
        ));
        writeln!(actual, "class|{owner}|{}", renamed.qualified_name).unwrap();
        for method in &renamed.methods {
            writeln!(actual, "method|{}|{}", method.name, method.descriptor).unwrap();
        }
        for field in &renamed.fields {
            writeln!(actual, "field|{}|{}", field.name, field.descriptor).unwrap();
        }
        for (i, constant) in renamed.pool.get_pool().iter().enumerate().skip(1) {
            if let Some(PooledConstant::Link(link)) = constant
                && matches!(
                    link.ty,
                    CONSTANT_FIELDREF | CONSTANT_METHODREF | CONSTANT_INTERFACEMETHODREF
                )
            {
                let mapped = renamed.pool.get_link_constant(i as i32).unwrap();
                let owner = mapped.classname.as_deref().unwrap_or("null");
                writeln!(
                    actual,
                    "link|{i}|{owner}|{}|{}",
                    mapped.elementname, mapped.descriptor
                )
                .unwrap();
            }
        }
    }
    let mut nodes: Vec<_> = cx.class_nodes.iter().collect();
    nodes.sort_unstable_by_key(|(name, _)| *name);
    for (name, node) in nodes {
        let simple = node.simple_name.as_deref().unwrap_or("null");
        let parent = node.parent.map_or("null", |id| {
            cx.class_nodes[id].class.qualified_name.as_str()
        });
        writeln!(
            actual,
            "node|{name}|{simple}|{}|{parent}",
            format!("{:?}", node.kind).to_ascii_uppercase()
        )
        .unwrap();
    }

    for (i, (actual, expected)) in actual.lines().zip(oracle.lines()).enumerate() {
        assert_eq!(actual, expected, "rename snapshot row {}", i + 1);
    }
    assert_eq!(actual.lines().count(), oracle.lines().count());
}

#[derive(Default)]
struct Trace {
    helper: ConverterHelper,
    calls: String,
}

impl IdentifierRenamer for Trace {
    fn to_be_renamed(
        &mut self,
        kind: IdentifierKind,
        owner: &str,
        name: Option<&str>,
        descriptor: Option<&str>,
    ) -> bool {
        let result = self.helper.to_be_renamed(kind, owner, name, descriptor);
        let kind = format!("{kind:?}").to_ascii_uppercase();
        let name = name.unwrap_or("null");
        let descriptor = descriptor.unwrap_or("null");
        writeln!(
            self.calls,
            "check|{kind}|{owner}|{name}|{descriptor}|{result}"
        )
        .unwrap();
        result
    }

    fn next_class_name(&mut self, owner: &str, simple: Option<&str>) -> String {
        let result = self.helper.next_class_name(owner, simple);
        let simple = simple.unwrap_or("null");
        writeln!(self.calls, "new|CLASS|{owner}|{simple}|{result}").unwrap();
        result
    }

    fn next_field_name(&mut self, owner: &str, name: &str, descriptor: &str) -> String {
        let result = self.helper.next_field_name(owner, name, descriptor);
        writeln!(self.calls, "new|FIELD|{owner}|{name}|{descriptor}|{result}").unwrap();
        result
    }

    fn next_method_name(&mut self, owner: &str, name: &str, descriptor: &str) -> String {
        let result = self.helper.next_method_name(owner, name, descriptor);
        writeln!(
            self.calls,
            "new|METHOD|{owner}|{name}|{descriptor}|{result}"
        )
        .unwrap();
        result
    }
}
