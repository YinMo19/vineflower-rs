// SPDX-License-Identifier: Apache-2.0

use super::upstream_reference::Corpus;
use std::{fs, sync::Arc};
use vineflower_rs::{
    engine::{
        Cx, Options,
        class_nodes::load_classes,
        class_processor::{process_class, write_class},
    },
    structs::StructContext,
    util::text_buffer::TextBuffer,
};

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn complete_compilation_units_and_source_maps_match_upstream() {
    let dir = tempfile::tempdir().unwrap();
    Corpus::discover().run("CompilationUnitReference", &["WrapperStages"], dir.path());
    for profile in 0..4 {
        let mut options = Options::default();
        options.include_runtime = "0".into();
        options.bytecode_source_mapping = true;
        options.unit_test_mode = true;
        options.dump_original_lines = profile == 2;
        options.preferred_line_length = if profile == 0 { 160 } else { 36 };
        options.lambda_to_anonymous_class = profile == 1;
        options.mark_corresponding_synthetics = profile == 2;
        options.sourcefile_comments = profile == 2;
        if profile == 3 {
            options.method_to_decompile = "nested()Lsource/Fn;".into();
        }
        let options = Arc::new(options);
        let mut context = StructContext::new(Arc::clone(&options), None);
        context.add_file(&dir.path().join("classes"), true).unwrap();
        let mut cx = Cx::new(Arc::new(context));
        cx.class_nodes = load_classes(
            &cx.struct_context,
            &options,
            |_| true,
            |_| true,
            |_, _| None,
        );
        for name in ["Fn", "Unit"] {
            let root = cx.class_nodes.id(&format!("source/{name}")).unwrap();
            let cl = Arc::clone(&cx.class_nodes[root].class);
            process_class(&mut cx, root).unwrap();
            let mut buffer = TextBuffer::new(&cx);
            write_class(&mut cx, &cl, &mut buffer).unwrap();
            let expected =
                fs::read_to_string(dir.path().join(format!("{profile}-{name}.java"))).unwrap();
            let actual = buffer.convert_to_string_and_allow_data_discard();
            if actual != expected {
                let i = actual
                    .lines()
                    .zip(expected.lines())
                    .position(|(a, b)| a != b)
                    .unwrap_or(actual.lines().count().min(expected.lines().count()));
                panic!(
                    "profile {profile} {name} line {}\nJava {:?}\nRust {:?}",
                    i + 1,
                    expected.lines().skip(i).take(4).collect::<Vec<_>>(),
                    actual.lines().skip(i).take(4).collect::<Vec<_>>()
                );
            }
            assert_eq!(
                format!("{:?}", cx.source_mapper.original_lines_mapping()),
                fs::read_to_string(dir.path().join(format!("{profile}-{name}.map"))).unwrap(),
                "{profile} {name} original line mapping"
            );
            assert!(cx.class_nodes[root].wrapper.is_none());
        }
    }
}
