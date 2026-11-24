// Based on Vineflower ClassWriter and TextBuffer (Apache-2.0).
use crate::source_text::{
    Document,
    tokens::{Token, TokenKind},
};

use super::Writer;

impl Writer<'_, '_> {
    pub(super) fn field_symbol(
        &self,
        out: &mut Document,
        visible: &str,
        name: &str,
        descriptor: &str,
    ) {
        if self.options.dump_text_tokens {
            out.token(
                visible,
                Token {
                    declaration: true,
                    kind: TokenKind::Field {
                        owner: self.owner.into(),
                        name: name.into(),
                        descriptor: descriptor.into(),
                    },
                },
            );
        } else {
            out.push_str(visible);
        }
    }
}

/// Record each named class component that is present in the rendered type.
/// An import can hide enclosing classes; package qualifiers do not represent
/// additional class symbols.
pub(crate) fn append_class(out: &mut Document, visible: &str, binary: &str, marked: bool) {
    let start = out.len();
    out.push_str(visible);
    if marked {
        class_ranges(out, start, visible, binary);
    }
}

pub(super) fn class_ranges(out: &mut Document, start: usize, visible: &str, binary: &str) {
    let simple = binary.rsplit('/').next().unwrap_or(binary);
    let nesting = simple.bytes().filter(|&b| b == b'$').count();
    let dots = visible.bytes().filter(|&b| b == b'.').count();
    let shown = dots.min(nesting);
    let package_len = binary.len() - simple.len();
    let mut inner = simple.match_indices('$').skip(nesting - shown);
    let prefix = if shown > 0 && dots > shown {
        visible
            .match_indices('.')
            .nth(dots - shown - 1)
            .map_or(0, |(dot, _)| dot + 1)
    } else {
        0
    };
    let mut remaining = &visible[prefix..];
    let mut at = start + prefix;
    for _ in 0..shown {
        let (end, _) = inner.next().expect("a class per visible nesting separator");
        let dot = remaining.find('.').expect("visible nested component");
        out.token_at(at..at + dot, class_token(&binary[..package_len + end]));
        remaining = &remaining[dot + 1..];
        at += dot + 1;
    }
    out.token_at(at..at + remaining.len(), class_token(binary));
}

fn class_token(binary: &str) -> Token {
    Token {
        declaration: false,
        kind: TokenKind::Class {
            name: binary.into(),
        },
    }
}
