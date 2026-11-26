// SPDX-License-Identifier: Apache-2.0

use std::sync::Arc;

use super::writer_snapshot::compare_snapshot;
use vineflower_rs::engine::{
    Cx, Options, class_nodes::load_classes, class_processor::process_class,
    class_writer::write_class_definition,
};
use vineflower_rs::structs::StructContext;
use vineflower_rs::util::text_buffer::TextBuffer;

use super::upstream_reference::Corpus;

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn type_annotation_headers_match_upstream_before_and_after_wrapping() {
    let scratch = tempfile::tempdir().unwrap();
    let oracle = Corpus::discover().run(
        "TypeAnnotationWriterReference",
        &["WriterSnapshot"],
        scratch.path(),
    );
    for width in [42, 120] {
        let mut options = Options::default();
        options.include_runtime = "0".into();
        options.use_method_parameters = true;
        options.preferred_line_length = width;
        let options = Arc::new(options);
        let mut classes = StructContext::new(Arc::clone(&options), None);
        classes
            .add_file(&scratch.path().join("classes"), true)
            .unwrap();
        let mut cx = Cx::new(Arc::new(classes));
        cx.class_nodes = load_classes(
            &cx.struct_context,
            &options,
            |_| true,
            |_| true,
            |_, _| None,
        );
        let root = cx.class_nodes.id("ann/Shapes").unwrap();
        process_class(&mut cx, root).unwrap();
        for (name, indent) in [("ann/Shapes", 0), ("ann/Shapes$R", 1), ("ann/Shapes$VR", 1)] {
            let node = cx.class_nodes.id(name).unwrap();
            let mut buffer = TextBuffer::new(&cx);
            write_class_definition(&mut cx, node, &mut buffer, indent).unwrap();
            compare_snapshot(&oracle, &format!("{width}|class|{name}"), &mut buffer);
        }
        process_class(&mut cx, root).unwrap();
        let record = cx.class_nodes.id("ann/Shapes$VR").unwrap();
        let mut repeated = TextBuffer::new(&cx);
        write_class_definition(&mut cx, record, &mut repeated, 1).unwrap();
        compare_snapshot(
            &oracle,
            &format!("{width}|repeat|ann/Shapes$VR"),
            &mut repeated,
        );
    }
}
