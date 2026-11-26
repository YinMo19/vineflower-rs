// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn metadata_writer_matches_upstream() {
    use std::fmt::Write as _;
    use vineflower_rs::engine::class_processor::{prepare_class, write_metadata};
    use vineflower_rs::util::text_buffer::TextBuffer;
    use vineflower_rs::util::token::TokenKind;

    fn write_buffer_text(out: &mut String, label: &str, buffer: &TextBuffer) {
        write!(out, "{label}=").unwrap();
        for byte in buffer.convert_to_string_and_allow_data_discard().bytes() {
            write!(out, "{byte:02x}").unwrap();
        }
        out.push('\n');
    }

    fn write_tokens(output: &mut String, buffer: &TextBuffer) {
        for token in buffer.get_tokens() {
            write!(
                output,
                "{}|{}|{}|",
                token.start, token.length, token.declaration
            )
            .unwrap();
            match token.kind {
                TokenKind::Class { qualified_name } => writeln!(output, "class|{qualified_name}"),
                TokenKind::Method {
                    class_name,
                    name,
                    descriptor,
                } => {
                    writeln!(output, "method|{class_name}|{name}|{descriptor}")
                }
                TokenKind::Field {
                    class_name,
                    name,
                    descriptor,
                } => {
                    writeln!(
                        output,
                        "field|{class_name}|{name}|{}",
                        descriptor.descriptor_string
                    )
                }
                TokenKind::Variable { .. } => panic!("Unexpected token in class metadata"),
            }
            .unwrap();
        }
    }

    let scratch = tempfile::tempdir().unwrap();
    let reference =
        upstream_reference::Corpus::discover().run("MetadataWriterReference", &[], scratch.path());
    let fixtures = [
        ("package", "pkg/package-info"),
        ("module", "module-info"),
        ("open", "module-info"),
    ];
    let mut output = String::new();
    for profile in 0..3 {
        let mut options = Options::default();
        options.include_runtime = "0".into();
        options.ascii_strings = profile == 1;
        options.new_line_separator = profile != 1;
        options.indent_string = if profile == 1 { "  " } else { "   " }.into();
        options.preferred_line_length = 24;
        options.remove_imports = profile == 2;
        let options = Arc::new(options);
        for (index, (directory, name)) in fixtures.into_iter().enumerate() {
            let mut classes = StructContext::new(options.clone(), None);
            classes
                .add_file(&scratch.path().join(directory), true)
                .unwrap();
            if index == 0 {
                classes
                    .add_file(&scratch.path().join("foreign"), false)
                    .unwrap();
            }
            let mut cx = Cx::new(Arc::new(classes));
            cx.class_nodes = load_classes(
                &cx.struct_context,
                &options,
                |_| true,
                |_| true,
                |_, _| None,
            );
            let root = cx.class_nodes.id(name).unwrap();
            let class = cx.class_nodes[root].class.clone();
            prepare_class(&mut cx, root).unwrap();
            let mut buffer = TextBuffer::new(&cx);
            assert!(
                write_metadata(&mut cx, &class, &mut buffer).unwrap(),
                "{name}"
            );

            writeln!(output, "profile={profile},fixture={index},root={name}").unwrap();
            write_buffer_text(&mut output, "text", &buffer);
            writeln!(output, "imports={}", cx.imports.imports().join(",")).unwrap();
            write_tokens(&mut output, &buffer);
            buffer.reformat();
            write_buffer_text(&mut output, "wrapped", &buffer);
            write_tokens(&mut output, &buffer);

            if let Some(ordinary) = cx.class_nodes.get("meta/Meta") {
                let class = ordinary.class.clone();
                let mut empty = TextBuffer::new(&cx);
                assert!(!write_metadata(&mut cx, &class, &mut empty).unwrap());
                assert_eq!(empty.length(), 0);
            }
        }
    }
    let java: Vec<_> = reference.lines().collect();
    let rust: Vec<_> = output.lines().collect();
    let difference = java.iter().zip(&rust).position(|(java, rust)| java != rust);
    if let Some(index) = difference {
        let name = java[..index]
            .iter()
            .rev()
            .find(|line| line.starts_with("profile="));
        panic!(
            "metadata differs at line {} after {name:?}\nJava {}\nRust {}",
            index + 1,
            java[index],
            rust[index]
        );
    }
    assert_eq!(java.len(), rust.len());
}
