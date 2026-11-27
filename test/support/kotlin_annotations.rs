use crate::upstream_reference::{Corpus, upstream_root};
use std::{fmt::Write, fs, sync::Arc};
use vineflower_rs::{
    code::code_constants::ACC_INTERFACE,
    engine::{Cx, Options, class_nodes::load_classes, import_collector::ImportCollector},
    kotlin::{
        imports,
        members::{self, ClassElement},
        writer::{annotations, write_header},
    },
    structs::{StructClass, StructContext, StructMember, attr::TypeAnnotationData as Target},
    util::text_buffer::TextBuffer,
};

#[test]
#[ignore = "compares the original Kotlin writer on compiled classes"]
fn annotations_defaults_and_file_headers_match_upstream() {
    let corpus = Corpus::discover();
    let scratch = tempfile::tempdir().unwrap();
    for (source, families) in [
        (
            upstream_root().join("plugins/kotlin/testData/classes/kt/pkg"),
            &["TestAnnotations", "TestMultifile", "TestPropertyAccess"][..],
        ),
        (
            corpus.root.join("java8/pkg"),
            &[
                "MoreAnnotations",
                "TypeAnnotations",
                "TestAnnotationFormatting",
            ][..],
        ),
    ] {
        for entry in fs::read_dir(source).unwrap().map(Result::unwrap) {
            let file = entry.file_name();
            if file
                .to_str()
                .is_some_and(|name| families.iter().any(|prefix| name.starts_with(prefix)))
            {
                fs::copy(entry.path(), scratch.path().join(file)).unwrap();
            }
        }
    }
    let reference = corpus.run_with_kotlin("KotlinAnnotationsReference", &[], scratch.path());
    let mut options = Options::default();
    options.preferred_line_length = 36;
    let options = Arc::new(options);
    let mut context = StructContext::new(options.clone(), None);
    context.add_file(scratch.path(), true).unwrap();
    let mut cx = Cx::new(Arc::new(context));
    cx.class_nodes = load_classes(
        &cx.struct_context,
        &options,
        |_| true,
        |_| true,
        |_, _| None,
    );
    let mut names: Vec<_> = cx
        .class_nodes
        .iter()
        .map(|(name, _)| name.clone())
        .collect();
    names.sort();
    let mut actual = String::new();
    for name in names {
        let id = cx.class_nodes.id(&name).unwrap();
        let node = &cx.class_nodes[id];
        let class = node.class.clone();
        cx.imports = imports::from_parent(&ImportCollector::for_root(
            &cx.struct_context,
            &cx.class_nodes,
            node,
        ));
        members::parse_metadata_for(&mut cx, &class);
        let mut body = TextBuffer::new(&cx);
        append(
            &mut cx,
            &mut body,
            &class,
            class.as_ref(),
            Target::CLASS_TYPE_PARAMETER,
        );
        for field in &class.fields {
            append(&mut cx, &mut body, &class, field.as_ref(), Target::FIELD);
        }
        for method in &class.methods {
            append(
                &mut cx,
                &mut body,
                &class,
                method.as_ref(),
                Target::METHOD_RETURN_TYPE,
            );
            for index in
                0..vineflower_rs::types::MethodDescriptor::parse_descriptor(&method.descriptor)
                    .params
                    .len()
            {
                let nullable =
                    annotations::parameter(&mut cx, &mut body, &method.attributes, index).unwrap();
                body.append(if nullable { "true" } else { "false" })
                    .append_line_separator();
            }
            if let Some(default) = &method.attributes.annotation_default {
                body.append_buffer(
                    &annotations::render_element(&mut cx, &default.default_value.value, 1).unwrap(),
                )
                .append_line_separator();
            }
        }
        body.reformat();
        let mut header = TextBuffer::new(&cx);
        write_header(&mut cx, &class, &mut header).unwrap();
        writeln!(actual, "{name}").unwrap();
        actual.push_str(&header.convert_to_string_and_allow_data_discard());
        actual.push_str(&body.convert_to_string_and_allow_data_discard());
    }
    assert_eq!(actual, reference);
}

fn append(
    cx: &mut Cx,
    buffer: &mut TextBuffer,
    class: &StructClass,
    member: &impl StructMember,
    target: i32,
) {
    let is_in_file = matches!(
        cx.kotlin_members().and_then(|m| m.class(class)),
        Some(ClassElement::File(_))
    );
    annotations::append(
        cx,
        buffer,
        1,
        member,
        if target == Target::CLASS_TYPE_PARAMETER {
            -1
        } else {
            target
        },
    )
    .unwrap();
    annotations::append_jvm(
        buffer,
        1,
        member,
        class.has_modifier(ACC_INTERFACE),
        is_in_file,
        &class.pool,
        target,
    )
    .unwrap();
}
