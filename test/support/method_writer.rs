use std::{io, sync::Arc};

use vineflower_rs::{
    engine::{
        Cx, Options,
        class_nodes::load_classes,
        class_processor::{process_class, process_class_methods},
        class_writer::write_class,
        context_source::RuntimeImage,
        method_processor::code_to_java,
    },
    structs::StructContext,
    util::text_buffer::TextBuffer,
};

use crate::{upstream_reference, writer_snapshot};

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn method_writing_matches_upstream_in_whole_classes() {
    let scratch = tempfile::tempdir().unwrap();
    let oracle = upstream_reference::Corpus::discover().run(
        "MethodWriterReference",
        &["WriterSnapshot"],
        scratch.path(),
    );
    let runtime = Arc::new(RuntimeImage::open(&upstream_reference::jdk_home()).unwrap());
    let names = [
        "methodwriter/MethodSubject",
        "methodwriter/Face",
        "methodwriter/Base",
        "methodwriter/Defaults",
        "methodwriter/Value",
        "methodwriter/Empty",
        "methodwriter/Failure",
    ];
    for width in [52, 132] {
        let mut options = Options::default();
        options.preferred_line_length = width;
        options.remove_bridge = width == 52;
        options.remove_synthetic = width == 52;
        options.use_method_parameters = width == 52;
        options.dump_exception_on_error = false;
        options.variable_renaming = (width == 132).then(|| "jad".into());
        options.rename_parameters = width == 132;
        let options = Arc::new(options);
        let mut context = StructContext::new(Arc::clone(&options), None);
        context
            .add_file(&scratch.path().join("classes"), true)
            .unwrap();
        context.add_space(runtime.clone(), false);
        let context = Arc::new(context);
        for name in names {
            let mut cx = Cx::new(Arc::clone(&context));
            cx.class_nodes = load_classes(
                &cx.struct_context,
                &options,
                |_| true,
                |_| true,
                |_, _| None,
            );
            let node = cx.class_nodes.id(name).unwrap();
            if name == "methodwriter/Failure" {
                process_class_methods(&mut cx, node, |cx, class, method| {
                    if method.name == "failed" {
                        Err(io::Error::other("exercise method bytecode dump"))
                    } else {
                        code_to_java(cx, class, method)
                    }
                })
                .unwrap();
            } else {
                process_class(&mut cx, node).unwrap();
            }
            let mut buffer = TextBuffer::new(&cx);
            write_class(&mut cx, node, &mut buffer, 0).unwrap();
            writer_snapshot::compare_snapshot(
                &oracle,
                &format!("{width}|class|{name}"),
                &mut buffer,
            );
        }
    }
}
