use super::upstream_reference::Corpus;
use super::writer_snapshot::compare_snapshot;
use std::sync::Arc;
use vineflower_rs::engine::{
    Cx, Options,
    class_nodes::{ClassNodeId, load_classes},
    class_processor::process_class,
    class_writer::{
        javadoc::{JavadocProvider, JavadocStyle},
        write_class_definition,
    },
};
use vineflower_rs::structs::{StructClass, StructContext};
use vineflower_rs::util::text_buffer::TextBuffer;

struct Docs(JavadocStyle);
impl JavadocProvider for Docs {
    fn class_doc(&self, class: &StructClass) -> Option<String> {
        Some(format!("Doc {}\n\n第二行\n\n", class.qualified_name))
    }
    fn class_style(&self, _class: &StructClass) -> JavadocStyle {
        self.0
    }
}

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn class_declarations_follow_classfile_and_nesting_flags() {
    let scratch = tempfile::tempdir().unwrap();
    let oracle = Corpus::discover().run(
        "ClassDeclarationReference",
        &["WrapperStages", "WriterSnapshot"],
        scratch.path(),
    );
    for profile in 0..3 {
        let mut options = Options::default();
        options.include_runtime = "0".into();
        options.preferred_line_length = 32;
        options.decompile_generics = profile != 1;
        options.decompile_enums = profile != 2;
        options.mark_corresponding_synthetics = profile != 0;
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
        if profile > 0 {
            cx.javadoc = Some(Arc::new(Docs(if profile == 1 {
                JavadocStyle::Html
            } else {
                JavadocStyle::Markdown
            })));
        }
        let mut count = 0;
        for name in ["decl/Shape", "decl/Open", "decl/Fixed", "decl/Host"] {
            let root = cx.class_nodes.id(name).unwrap();
            process_class(&mut cx, root).unwrap();
            count += compare(&mut cx, &oracle, profile, root, 0);
        }
        assert_eq!(
            count,
            oracle
                .lines()
                .filter(|l| l.starts_with(&format!("section={profile}|")))
                .count()
        );
    }
}

fn compare(cx: &mut Cx, oracle: &str, profile: i32, node: ClassNodeId, indent: i32) -> usize {
    let mut buffer = TextBuffer::new(cx);
    write_class_definition(cx, node, &mut buffer, indent).unwrap();
    compare_snapshot(
        oracle,
        &format!(
            "{profile}|definition|{}",
            cx.class_nodes[node].class.qualified_name
        ),
        &mut buffer,
    );
    1 + cx.class_nodes[node]
        .nested
        .clone()
        .into_iter()
        .map(|n| compare(cx, oracle, profile, n, indent + 1))
        .sum::<usize>()
}
