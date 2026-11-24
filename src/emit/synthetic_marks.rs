// Based on Vineflower ClassWriter's corresponding synthetic markers (Apache-2.0).

use std::rc::Rc;

use crate::{
    Options,
    context::NestedKind,
    source_text::{
        Document,
        tokens::{Token, TokenKind, TokenPosition, TokenRange},
    },
};

use super::Writer;

const CLASS_MARK_START: &str = " /* ";
const CLASS_MARK_END: &str = " */";

impl Writer<'_, '_> {
    pub(super) fn append_local_synthetic_mark(&self, head: &mut Document) {
        if !self.options.mark_corresponding_synthetics
            || !self.has_lexical_owner()
            || !self.group.nested_class(self.owner).is_some_and(|node| {
                matches!(node.kind, NestedKind::Local(_))
            })
        {
            return;
        }
        let binary = self.names.renames().class_name(self.owner);
        let leaf = simple(binary);
        head.push_str(CLASS_MARK_START);
        if self.options.dump_text_tokens {
            head.token(leaf, class_declaration(binary));
        } else {
            head.push_str(leaf);
        }
        head.push_str(CLASS_MARK_END);
    }

    pub(super) fn append_anonymous_synthetic_mark(&mut self, original_binary: &str) {
        if !self.options.mark_corresponding_synthetics {
            return;
        }
        let binary = self.names.renames().class_name(original_binary);
        let leaf = simple(binary);
        self.body.push_str(CLASS_MARK_START);
        if self.options.dump_text_tokens {
            let last_line = self.body.rsplit('\n').next().unwrap_or_default();
            let start = TokenPosition { line: self.lines, column: last_line.encode_utf16().count() };
            let end = TokenPosition { column: start.column + leaf.encode_utf16().count(), ..start };
            self.tokens.push((Rc::new(class_declaration(binary)), TokenRange { start, end }));
        }
        self.body.push_str(leaf);
        self.body.push_str(CLASS_MARK_END);
    }
}

/// Append the original implementation method before a converted lambda body
/// or array-constructor reference. Call only for a proved synthetic implementation.
pub(crate) fn append_lambda_mark(
    out: &mut Document,
    options: &Options,
    owner: &str,
    name: &str,
    descriptor: &str,
) {
    if !options.mark_corresponding_synthetics {
        return;
    }
    out.push_str("/* ");
    if options.dump_text_tokens {
        out.token(name, Token {
            declaration: true,
            kind: TokenKind::Method { owner: owner.into(), name: name.into(), descriptor: descriptor.into() },
        });
    } else {
        out.push_str(name);
    }
    out.push_str(" */ ");
}

fn class_declaration(binary: &str) -> Token {
    Token { declaration: true, kind: TokenKind::Class { name: binary.into() } }
}

fn simple(binary: &str) -> &str {
    binary.rsplit('/').next().unwrap_or(binary)
}

#[cfg(test)]
mod tests;
