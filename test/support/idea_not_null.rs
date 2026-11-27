use std::sync::Arc;

use vineflower_rs::{
    engine::{
        Cx, Options, class_nodes::load_classes, class_processor::process_class,
        class_writer::write_class, context_source::RuntimeImage,
    },
    structs::StructContext,
    util::text_buffer::TextBuffer,
};

use crate::{upstream_reference, writer_snapshot};

#[test]
#[ignore = "requires the upstream +local.jar with IdeaNotNull and its instrumented class"]
fn idea_not_null_plugin_matches_upstream_with_checks_enabled_and_disabled() {
    let corpus = upstream_reference::Corpus::discover();
    let scratch = tempfile::tempdir().unwrap();
    let class = scratch.path().join("TestIdeaNotNull.class");
    std::fs::copy(corpus.root.join("custom/TestIdeaNotNull.class"), &class).unwrap();
    let oracle = corpus.run("IdeaNotNullReference", &["WriterSnapshot"], &class);
    let runtime = Arc::new(RuntimeImage::open(&upstream_reference::jdk_home()).unwrap());
    for enabled in [false, true] {
        let mut options = Options::default();
        options.idea_notnull = true;
        options.resugar_idea_notnull = enabled;
        let options = Arc::new(options);
        let mut context = StructContext::new(Arc::clone(&options), None);
        context.add_file(&class, true).unwrap();
        context.add_space(runtime.clone(), false);
        let mut cx = Cx::new(Arc::new(context));
        cx.class_nodes = load_classes(
            &cx.struct_context,
            &options,
            |_| true,
            |_| true,
            |_, _| None,
        );
        let root = cx.class_nodes.id("pkg/TestIdeaNotNull").unwrap();
        process_class(&mut cx, root).unwrap();
        let wrapper = cx.class_nodes[root].wrapper.as_ref().unwrap();
        for method in &wrapper.methods {
            assert!(
                method.decompile_error().is_none(),
                "{}: {:?}",
                method.method,
                method.decompile_error()
            );
        }
        let mut buffer = TextBuffer::new(&cx);
        write_class(&mut cx, root, &mut buffer, 0).unwrap();
        assert_eq!(
            buffer
                .convert_to_string_and_allow_data_discard()
                .contains("$$$reportNull$$$0("),
            !enabled,
        );
        writer_snapshot::compare_snapshot(
            &oracle,
            &format!("{}|class|pkg/TestIdeaNotNull", u8::from(enabled)),
            &mut buffer,
        );
    }
}
