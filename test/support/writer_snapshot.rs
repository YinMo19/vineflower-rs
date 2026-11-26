// SPDX-License-Identifier: Apache-2.0

use vineflower_rs::util::{text_buffer::TextBuffer, token::TokenKind};

pub(super) fn compare_snapshot(oracle: &str, name: &str, actual: &mut TextBuffer) {
    let section = format!("section={name}");
    let mut rows = oracle
        .lines()
        .skip_while(|line| *line != section)
        .skip(1)
        .take_while(|line| !line.starts_with("section="))
        .peekable();
    for phase in ["raw", "wrapped"] {
        let line = rows.next().expect(&section);
        let hex = line.strip_prefix(&format!("{phase}=")).expect(line);
        let text: Vec<_> = hex
            .as_bytes()
            .chunks_exact(2)
            .map(|pair| u8::from_str_radix(std::str::from_utf8(pair).unwrap(), 16).unwrap())
            .collect();
        let text = String::from_utf8(text).unwrap();
        assert_eq!(
            actual.convert_to_string_and_allow_data_discard(),
            text,
            "{name} {phase}"
        );

        let expected: Vec<_> =
            std::iter::from_fn(|| rows.next_if(|line| !line.starts_with("wrapped="))).collect();
        let actual_tokens: Vec<_> = actual
            .get_tokens()
            .into_iter()
            .map(|token| {
                let label = match token.kind {
                    TokenKind::Class { qualified_name } => format!("class|{qualified_name}"),
                    TokenKind::Field { class_name, name, descriptor } => {
                        format!("field|{class_name}|{name}|{}", descriptor.descriptor_string)
                    }
                    TokenKind::Method { class_name, name, descriptor } => {
                        format!("method|{class_name}|{name}|{descriptor}")
                    }
                    TokenKind::Variable { parameter, class_name, method_name, method_descriptor, index, name } => {
                        format!("variable|{parameter}|{class_name}|{method_name}|{method_descriptor}|{index}|{name}")
                    }
                };
                format!("{}|{}|{}|{label}", token.start, token.length, token.declaration)
            })
            .collect();
        assert_eq!(actual_tokens, expected, "{name} {phase} tokens");
        if phase == "raw" {
            actual.reformat();
        }
    }
}
