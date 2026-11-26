// SPDX-License-Identifier: Apache-2.0

use std::sync::Arc;

use vineflower_rs::{
    engine::{
        Cx, Options,
        class_nodes::load_classes,
        class_processor::process_class,
        class_writer::{
            javadoc::{JavadocProvider, JavadocStyle},
            prepare_class_for_writing,
        },
    },
    kotlin::{imports, writer::fallback},
    renamer::pool_interceptor::PoolInterceptor,
    structs::{StructClass, StructContext, StructField, StructMember, StructMethod},
    util::text_buffer::TextBuffer,
};

use super::{upstream_reference::Corpus, writer_snapshot::compare_snapshot};

struct Documentation;

impl JavadocProvider for Documentation {
    fn class_style(&self, _class: &StructClass) -> JavadocStyle {
        JavadocStyle::Markdown
    }
    fn field_doc(&self, _class: &StructClass, field: &StructField) -> Option<String> {
        (field.name == "values").then(|| "Field info\nSecond line\n".into())
    }
    fn method_doc(&self, _class: &StructClass, method: &StructMethod) -> Option<String> {
        (method.name == "abstractWide").then(|| "Method info".into())
    }
}

#[test]
#[ignore = "requires the upstream Kotlin plugin and JDK 17+"]
fn kotlin_fallback_matches_upstream() {
    let scratch = tempfile::tempdir().unwrap();
    let expected = Corpus::discover().run_with_kotlin(
        "KotlinFallbackReference",
        &["WrapperStages", "WriterSnapshot"],
        scratch.path(),
    );
    let mut options = Options::default();
    options.decompile_kotlin = true;
    options.preferred_line_length = 35;
    options.rename_members = true;
    let options = Arc::new(options);
    let mut context = StructContext::new(options.clone(), None);
    context
        .add_file(&scratch.path().join("classes"), true)
        .unwrap();
    context.load_abstract_metadata(
        "fallback/FallbackSubject nativeWide (J[Ljava/lang/String;)I height tail",
    );
    let mut cx = Cx::new(Arc::new(context));
    cx.class_nodes = load_classes(
        &cx.struct_context,
        &options,
        |_| true,
        |_| true,
        |_, _| None,
    );
    cx.javadoc = Some(Arc::new(Documentation));
    for name in [
        "fallback/FallbackSubject",
        "fallback/Face",
        "fallback/SampleEnum",
    ] {
        let node = cx.class_nodes.id(name).unwrap();
        process_class(&mut cx, node).unwrap();
        cx.current_class_node = Some(name.into());
        cx.imports = imports::from_parent(&cx.imports);
        prepare_class_for_writing(&mut cx, node).unwrap();
        if name.ends_with("FallbackSubject") {
            let mut pool = PoolInterceptor::default();
            pool.add_name(
                "fallback/FallbackSubject values Ljava/util/List;",
                "fallback/FallbackSubject listValues Ljava/util/List;",
            );
            pool.add_name(
                "fallback/FallbackSubject receiver (Ljava/lang/String;I)I",
                "fallback/FallbackSubject when (Ljava/lang/String;I)I",
            );
            cx.pool_interceptor = Some(Arc::new(pool));
        }
        let class = cx.class_nodes[node].class.clone();
        for field in class.fields.iter().filter(|field| !field.is_synthetic()) {
            let mut text = TextBuffer::new(&cx);
            fallback::write_field(&mut cx, node, field, &mut text, 1).unwrap();
            compare_snapshot(
                &expected,
                &format!("35|field|{name}|{}", field.name),
                &mut text,
            );
        }
        for (index, method) in class.methods.iter().enumerate() {
            if name.ends_with("SampleEnum")
                && !matches!(method.name.as_str(), "<init>" | "<clinit>")
            {
                continue;
            }
            let mut text = TextBuffer::new(&cx);
            let keep = fallback::write_method(&mut cx, node, index, method, &mut text, 1).unwrap();
            compare_snapshot(
                &expected,
                &format!(
                    "35|method|{name}|{}|{}|{keep}",
                    method.name, method.descriptor
                ),
                &mut text,
            );
        }
    }
}
