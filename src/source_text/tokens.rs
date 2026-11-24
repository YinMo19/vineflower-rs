// Based on Vineflower TextToken and TextTokenDumpVisitor (Apache-2.0).

use std::{fmt::Write, ops::Range, rc::Rc};

use super::{Document, Kind, units};

#[derive(Debug)]
pub(crate) struct Token {
    pub(crate) declaration: bool,
    pub(crate) kind: TokenKind,
}

#[derive(Debug)]
pub(crate) enum TokenKind {
    Class {
        name: String,
    },
    Field {
        owner: String,
        name: String,
        descriptor: String,
    },
    Method {
        owner: String,
        name: String,
        descriptor: String,
    },
    Variable {
        owner: String,
        method: String,
        descriptor: String,
        index: u32,
        name: String,
        parameter: bool,
    },
}

/// Zero-based physical line and UTF-16 column, before the dump's numbering.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct TokenPosition {
    pub(crate) line: usize,
    pub(crate) column: usize,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct TokenRange {
    pub(crate) start: TokenPosition,
    pub(crate) end: TokenPosition,
}

impl TokenRange {
    pub(crate) fn shift_lines(&mut self, lines: usize) {
        self.start.line += lines;
        self.end.line += lines;
    }

    pub(super) fn on_line(line: usize, column: usize, width: usize) -> Self {
        Self {
            start: TokenPosition { line, column },
            end: TokenPosition {
                line,
                column: column + width,
            },
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct Span {
    pub(super) token: Rc<Token>,
    pub(super) start: usize,
    end: usize,
    pub(super) width: usize,
}

impl Span {
    fn shift(&mut self, from: usize, to: usize) {
        self.start = self.start - from + to;
        self.end = self.end - from + to;
    }
}

fn token_width(text: &str) -> usize {
    assert!(
        !text.is_empty() && !text.contains(['\n', '\r']),
        "token must be nonempty literal text on one line",
    );
    units(text)
}

impl Document {
    /// Append literal source text and register its symbol for a token visitor.
    /// Call this only when token collection is enabled.
    pub(crate) fn token(&mut self, value: &str, token: impl Into<Rc<Token>>) {
        let width = token_width(value);
        let start = self.flat.len();
        self.flat.push_str(value);
        Rc::make_mut(self.tokens.get_or_insert_with(Rc::default)).push(Span {
            token: token.into(),
            start,
            end: self.flat.len(),
            width,
        });
    }

    /// Register a symbol over a literal UTF-8 byte range already in the document.
    /// The range must be nonempty and must not contain a possible line break.
    pub(crate) fn token_at(&mut self, range: Range<usize>, token: impl Into<Rc<Token>>) {
        let width = token_width(self.flat.get(range.clone()).expect("token range in source"));
        let first = self.events.partition_point(|event| event.at < range.start);
        if let Some(event) = self.events[..first].last()
            && let Kind::Break { len, .. } = event.kind
        {
            assert!(event.at + len <= range.start, "token overlaps a soft break");
        }
        assert!(
            self.events[first..]
                .iter()
                .take_while(|event| event.at < range.end)
                .all(|event| match event.kind {
                    Kind::HardLine { .. } => false,
                    Kind::Break { len, .. } => len == 0 && event.at == range.start,
                    _ => true,
                }),
            "token range crosses a line break",
        );
        let spans = Rc::make_mut(self.tokens.get_or_insert_with(Rc::default));
        let at = spans.partition_point(|span| span.start <= range.start);
        spans.insert(
            at,
            Span {
                token: token.into(),
                start: range.start,
                end: range.end,
                width,
            },
        );
    }

    pub(crate) fn has_tokens(&self) -> bool {
        self.tokens.is_some()
    }

    /// Token spans in the flat fragment, before layout or marker expansion.
    pub(crate) fn flat_tokens(&self) -> impl Iterator<Item = (Range<usize>, &Rc<Token>)> {
        self.token_spans()
            .iter()
            .map(|span| (span.start..span.end, &span.token))
    }

    pub(super) fn token_spans(&self) -> &[Span] {
        self.tokens.as_deref().map_or(&[], Vec::as_slice)
    }

    pub(super) fn append_tokens(&mut self, other: Option<Rc<Vec<Span>>>) {
        let Some(mut other) = other else { return };
        let offset = self.flat.len();
        if let Some(spans) = &mut self.tokens {
            let spans = Rc::make_mut(spans);
            let shifted = |mut span: Span| {
                span.shift(0, offset);
                span
            };
            match Rc::try_unwrap(other) {
                Ok(other) => spans.extend(other.into_iter().map(shifted)),
                Err(other) => spans.extend(other.iter().cloned().map(shifted)),
            }
        } else {
            if offset != 0 {
                for span in Rc::make_mut(&mut other) {
                    span.shift(0, offset);
                }
            }
            self.tokens = Some(other);
        }
    }

    pub(super) fn insert_tokens(&mut self, at: usize, len: usize) {
        self.edit_tokens(|span| {
            if span.start >= at {
                span.shift(0, len);
                true
            } else {
                // Inserting inside a token invalidates its symbol span.
                span.end <= at
            }
        });
    }

    pub(super) fn replace_prefix_tokens(&mut self, len: usize, new_len: usize) {
        if len == 0 && new_len == 0 {
            return;
        }
        self.edit_tokens(|span| {
            if span.start < len {
                false
            } else {
                span.shift(len, new_len);
                true
            }
        });
    }

    pub(super) fn truncate_tokens(&mut self, len: usize) {
        if self.token_spans().iter().any(|span| span.end > len) {
            self.edit_tokens(|span| span.end <= len);
        }
    }

    fn edit_tokens(&mut self, edit: impl FnMut(&mut Span) -> bool) {
        if let Some(spans) = &mut self.tokens {
            let spans = Rc::make_mut(spans);
            spans.retain_mut(edit);
            if spans.is_empty() {
                self.tokens = None;
            }
        }
    }
}

/// Append the same comment block as TextTokenDumpVisitor. Ranges must already
/// include any package/import/banner line offset. `out` uses internal LF lines.
pub(crate) fn dump(out: &mut String, tokens: &mut [(Rc<Token>, TokenRange)]) {
    if !tokens.is_sorted_by_key(|(_, range)| range.start) {
        tokens.sort_by_key(|(_, range)| range.start);
    }

    // TextBuffer.getPos uses Java String.split, which omits trailing empty
    // fields. At column zero after a newline this reports the most recent
    // nonempty line, not the physical line of the token. Only scan source if
    // there are positions at that boundary.
    let mut line_starts = Vec::new();
    let mut source = out.split('\n').enumerate();
    let mut next_line = 0;
    let mut previous_nonempty = 0;
    for (_, range) in tokens.iter() {
        if range.start.line == 0 || range.start.column != 0 {
            continue;
        }
        while next_line < range.start.line {
            let (index, line) = source.next().expect("token lies within source");
            next_line = index + 1;
            if !line.is_empty() {
                previous_nonempty = next_line;
            }
        }
        line_starts.push(previous_nonempty);
    }
    let mut line_starts = line_starts.into_iter();

    out.push_str("\n/*\nTokens:\n");
    for (token, range) in tokens {
        let start_line = if range.start.line != 0 && range.start.column == 0 {
            line_starts.next().expect("collected column-zero position")
        } else {
            range.start.line + 1
        };
        let start_column = range.start.column + 1;
        let end_column = range.end.column + 1;
        let role = if token.declaration {
            "declaration"
        } else {
            "reference"
        };
        let _ = write!(
            out,
            "({start_line}:{start_column}, {}:{end_column}) ",
            range.end.line + 1,
        );
        match &token.kind {
            TokenKind::Class { name } => {
                let _ = writeln!(out, "class [{role}] {name}");
            }
            TokenKind::Field {
                owner,
                name,
                descriptor,
            } => {
                let _ = writeln!(out, "field [{role}] {owner}#{name}:{descriptor}");
            }
            TokenKind::Method {
                owner,
                name,
                descriptor,
            } => {
                let _ = writeln!(out, "method [{role}] {owner}#{name}{descriptor}");
            }
            TokenKind::Variable {
                owner,
                method,
                descriptor,
                index,
                name,
                parameter,
            } => {
                let kind = if *parameter { "parameter" } else { "local" };
                let _ = writeln!(
                    out,
                    "{kind} [{role}] {owner}#{method}{descriptor}({index}:{name})"
                );
            }
        }
    }
    out.push_str("*/\n");
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn wrapped_supplementary_token_retains_utf16_range_after_staging() {
        let mut argument = Document::from("\"😀\" + ");
        let variable = Rc::new(Token {
            declaration: false,
            kind: TokenKind::Variable {
                owner: "example/Fixture".into(),
                method: "choose".into(),
                descriptor: "(Ljava/lang/String;)V".into(),
                index: 0,
                name: "𝔘".into(),
                parameter: true,
            },
        });
        argument.anchor(10..13);
        argument.token("𝔘", Rc::clone(&variable));

        let mut call = Document::from("choose");
        call.token_at(
            0..6,
            Token {
                declaration: false,
                kind: TokenKind::Method {
                    owner: "example/Fixture".into(),
                    name: "choose".into(),
                    descriptor: "(Ljava/lang/String;)V".into(),
                },
            },
        );
        call.append_relative_arguments([&argument]);
        let mut staged = Document::new();
        staged.append_ref(&call);
        staged.surround("return ", ";");

        let mut out = String::from("class Fixture {\n  ");
        let mut anchors = Vec::new();
        let mut tokens = Vec::new();
        assert_eq!(
            staged.render_with_tokens_at(
                &mut out,
                22,
                "  ",
                true,
                1,
                |range, line| anchors.push((range, line)),
                |token, mut range| {
                    range.shift_lines(1);
                    tokens.push((Rc::clone(token), range));
                },
            ),
            2,
        );
        assert_eq!(anchors, [(10..13, 1)]);
        assert_eq!(tokens[1].1, TokenRange::on_line(2, 11, 2));
        assert!(Rc::ptr_eq(&tokens[1].0, &variable));
        out.push_str("\n}\n");
        dump(&mut out, &mut tokens);
        assert_eq!(
            out,
            concat!(
                "class Fixture {\n",
                "  return choose(\n",
                "    \"😀\" + 𝔘\n",
                "  );\n",
                "}\n\n",
                "/*\n",
                "Tokens:\n",
                "(2:10, 2:16) method [reference] example/Fixture#choose(Ljava/lang/String;)V\n",
                "(3:12, 3:14) parameter [reference] example/Fixture#choose(Ljava/lang/String;)V(0:𝔘)\n",
                "*/\n",
            ),
        );
    }
}
