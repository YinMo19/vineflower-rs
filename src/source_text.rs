// Based on Vineflower TextBuffer, ClassWriter, RecordHelper, and the Java expression writers (Apache-2.0).

use std::{
    fmt,
    num::NonZeroUsize,
    ops::{Deref, Range},
    rc::Rc,
};

pub(crate) mod tokens;

use tokens::{Span, Token, TokenRange};

/// A flat Java fragment with possible line breaks registered by its producer.
/// Nested groups make separate fit decisions after earlier breaks have been applied.
#[derive(Clone, Debug, Default)]
pub(crate) struct Document {
    flat: String,
    events: Vec<Event>,
    open: Option<NonZeroUsize>,
    tokens: Option<Rc<Vec<Span>>>,
}

#[derive(Clone, Debug)]
struct Event {
    at: usize,
    kind: Kind,
}

#[derive(Clone, Debug)]
enum Kind {
    Begin {
        link: Link,
        base: BaseDepth,
        extra: usize,
        has_breaks: bool,
        qualifier: bool,
    },
    Break {
        len: usize,
        dedent: bool,
    },
    Anchor {
        start: u32,
        end: u32,
    },
    HardLine {
        delta: usize,
    },
    End,
}

#[derive(Clone, Copy, Debug)]
enum Link {
    Open { parent: Option<NonZeroUsize> },
    Closed { end: usize },
}

#[derive(Clone, Copy, Debug)]
enum BaseDepth {
    Depth(usize),
    Relative(usize),
    InlineAnnotation,
}

impl BaseDepth {
    fn with_extra(self, origin: usize, extra: usize) -> usize {
        match self {
            Self::Depth(base) => base + extra,
            Self::Relative(delta) => origin + delta + extra,
            // ClassWriter and RecordHelper pass -1 for inline annotations.
            Self::InlineAnnotation => extra.saturating_sub(1),
        }
    }
}

impl From<String> for Document {
    fn from(flat: String) -> Self {
        Self {
            flat,
            ..Self::default()
        }
    }
}

impl From<&str> for Document {
    fn from(flat: &str) -> Self {
        flat.to_owned().into()
    }
}

impl AsRef<str> for Document {
    fn as_ref(&self) -> &str {
        &self.flat
    }
}

impl Deref for Document {
    type Target = str;

    fn deref(&self) -> &str {
        &self.flat
    }
}

impl<T: AsRef<str> + ?Sized> PartialEq<T> for Document {
    fn eq(&self, other: &T) -> bool {
        self.flat == other.as_ref()
    }
}

impl Eq for Document {}

impl fmt::Display for Document {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&self.flat, f)
    }
}

impl fmt::Write for Document {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        self.push_str(text);
        Ok(())
    }

    fn write_char(&mut self, ch: char) -> fmt::Result {
        self.push(ch);
        Ok(())
    }
}

impl Document {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn push(&mut self, ch: char) {
        self.flat.push(ch);
    }

    pub(crate) fn push_str(&mut self, text: &str) {
        self.flat.push_str(text);
    }

    pub(crate) fn as_str(&self) -> &str {
        &self.flat
    }

    pub(crate) fn as_flat(&self) -> &str {
        &self.flat
    }

    pub(crate) fn has_layout(&self) -> bool {
        !self.events.is_empty()
    }

    pub(crate) fn prepend_str(&mut self, text: &str) {
        self.insert_str(0, text);
    }

    /// Replace the literal prefix before a composed expression, retaining its
    /// groups and source anchors. Existing anchors in the prefix stay on the
    /// first physical line.
    pub(crate) fn replace_literal_prefix(&mut self, len: usize, prefix: &str) {
        let first = self.events.partition_point(|event| event.at < len);
        assert!(
            self.events[..first]
                .iter()
                .all(|event| matches!(event.kind, Kind::Anchor { .. })),
            "cannot replace a prefix containing layout groups or breaks",
        );
        self.flat.replace_range(..len, prefix);
        self.replace_prefix_tokens(len, prefix.len());
        let (head, tail) = self.events.split_at_mut(first);
        for event in head {
            event.at = 0;
        }
        for event in tail {
            event.at = event.at - len + prefix.len();
        }
    }

    /// Insert literal source before the events registered at `at`.
    pub(crate) fn insert_str(&mut self, at: usize, text: &str) {
        if text.is_empty() {
            return;
        }
        let first = self.events.partition_point(|event| event.at < at);
        if let Some(event) = self.events[..first]
            .iter()
            .rev()
            .find(|event| matches!(event.kind, Kind::Break { .. }))
            && let Kind::Break { len, .. } = event.kind
        {
            assert!(at >= event.at + len, "cannot insert inside a soft break");
        }
        self.flat.insert_str(at, text);
        self.insert_tokens(at, text.len());
        for event in &mut self.events[first..] {
            event.at += text.len();
        }
    }

    /// Remove a literal suffix, such as a statement's semicolon. This cannot
    /// remove registered layout events or the flat alternatives of soft breaks.
    pub(crate) fn truncate(&mut self, len: usize) {
        if len >= self.flat.len() {
            return;
        }
        let first = self.events.partition_point(|event| event.at <= len);
        assert!(
            self.events[first..]
                .iter()
                .all(|event| matches!(event.kind, Kind::End | Kind::Anchor { .. })),
            "cannot truncate through registered layout events",
        );
        if let Some(event) = self.events[..first]
            .iter()
            .rev()
            .find(|event| matches!(event.kind, Kind::Break { .. } | Kind::HardLine { .. }))
        {
            let width = match event.kind {
                Kind::Break { len, .. } => len,
                Kind::HardLine { .. } => 1,
                _ => unreachable!("selected a registered line break"),
            };
            assert!(len >= event.at + width, "cannot truncate inside a break");
        }
        self.flat.truncate(len);
        self.truncate_tokens(len);
        for event in &mut self.events[first..] {
            event.at = len;
        }
    }

    pub(crate) fn pop(&mut self) -> Option<char> {
        let ch = self.flat.chars().next_back()?;
        self.truncate(self.flat.len() - ch.len_utf8());
        Some(ch)
    }

    pub(crate) fn surround(&mut self, prefix: &str, suffix: &str) {
        self.prepend_str(prefix);
        self.push_str(suffix);
    }

    pub(crate) fn append(&mut self, fragment: Self) {
        assert!(
            fragment.open.is_none(),
            "appended document has an open group"
        );
        if self.flat.is_empty() && self.events.is_empty() {
            *self = fragment;
            return;
        }
        self.append_tokens(fragment.tokens);
        self.extend(&fragment.flat, fragment.events);
    }

    pub(crate) fn append_ref(&mut self, fragment: &Self) {
        assert!(
            fragment.open.is_none(),
            "appended document has an open group"
        );
        self.append_tokens(fragment.tokens.clone());
        self.extend(&fragment.flat, fragment.events.iter().cloned());
    }

    fn extend(&mut self, flat: &str, events: impl IntoIterator<Item = Event>) {
        let offset = self.flat.len();
        let event_offset = self.events.len();
        self.flat.push_str(flat);
        self.events.extend(events.into_iter().map(|mut event| {
            event.at += offset;
            if let Kind::Begin {
                link: Link::Closed { end },
                ..
            } = &mut event.kind
            {
                *end += event_offset;
            }
            event
        }));
    }

    /// Begin a group at an absolute indentation depth. All of its own soft
    /// breaks are applied together; children make their own fit decisions.
    #[cfg(test)]
    pub(crate) fn begin_group(&mut self, base_depth: usize, extra_depth: usize) {
        self.begin_at(BaseDepth::Depth(base_depth), extra_depth);
    }

    /// A group whose base indentation is set by the enclosing statement.
    pub(crate) fn begin_relative_group(&mut self, base_delta: usize, extra_depth: usize) {
        self.begin_at(BaseDepth::Relative(base_delta), extra_depth);
    }

    fn begin_at(&mut self, base: BaseDepth, extra: usize) {
        let at = NonZeroUsize::new(self.events.len() + 1).expect("group index is one based");
        let parent = self.open.replace(at);
        self.events.push(Event {
            at: self.flat.len(),
            kind: Kind::Begin {
                link: Link::Open { parent },
                base,
                extra,
                has_breaks: false,
                qualifier: false,
            },
        });
    }

    /// Preserve the formatting of an embedded member chain without letting a
    /// containing non-member expression promote it into a later chain.
    pub(crate) fn seal_qualifier(&mut self) {
        if let Some(Event {
            at: 0,
            kind: Kind::Begin { qualifier, .. },
        }) = self.events.first_mut()
        {
            *qualifier = false;
        }
    }

    /// Open the group covering a qualified field/invocation, and register the
    /// empty break before its dot. A prior receiver's eligible chain becomes
    /// part of this group. Close before the dot for a field, or after the final
    /// parenthesis for an invocation, as in Vineflower's expression writers.
    pub(crate) fn begin_qualifier(&mut self, allow_break: bool, promote_receiver: bool) -> bool {
        if !allow_break {
            return false;
        }
        assert!(self.open.is_none(), "receiver has an open group");
        if promote_receiver
            && let Some(Event {
                at: 0,
                kind:
                    Kind::Begin {
                        qualifier: true,
                        link,
                        ..
                    },
            }) = self.events.first_mut()
        {
            let Link::Closed { end } = *link else {
                unreachable!("receiver group is closed");
            };
            *link = Link::Open { parent: None };
            // An invocation ends at its group boundary. A field can carry
            // its bytecode anchor after the boundary, but has no more groups.
            assert!(
                self.events[end + 1..]
                    .iter()
                    .all(|event| matches!(event.kind, Kind::Anchor { .. })),
                "receiver is not an intact qualifier chain",
            );
            self.events.remove(end);
        } else {
            for event in &mut self.events {
                if let Kind::Begin {
                    link: Link::Closed { end },
                    ..
                } = &mut event.kind
                {
                    *end += 1;
                }
            }
            self.events.insert(
                0,
                Event {
                    at: 0,
                    kind: Kind::Begin {
                        link: Link::Open { parent: None },
                        base: BaseDepth::Relative(0),
                        extra: 1,
                        has_breaks: true,
                        qualifier: true,
                    },
                },
            );
        }
        self.open = NonZeroUsize::new(1);
        self.soft_break("", false);
        true
    }

    /// Emit `flat` when the group fits. When it doesn't, emit a line break
    /// instead; `dedent` removes this group's extra indentation from here on.
    pub(crate) fn soft_break(&mut self, flat: &str, dedent: bool) {
        let open = self.open.expect("soft line break outside a group").get() - 1;
        let Kind::Begin { has_breaks, .. } = &mut self.events[open].kind else {
            unreachable!("open group references its begin event");
        };
        *has_breaks = true;
        self.events.push(Event {
            at: self.flat.len(),
            kind: Kind::Break {
                len: flat.len(),
                dedent,
            },
        });
        self.flat.push_str(flat);
    }

    pub(crate) fn end_group(&mut self) {
        let open = self.open.expect("no group to close").get() - 1;
        let end = self.events.len();
        let Kind::Begin { link, .. } = &mut self.events[open].kind else {
            unreachable!("open group references its begin event");
        };
        let Link::Open { parent } = *link else {
            unreachable!("open group references an unfinished group");
        };
        self.open = parent;
        *link = Link::Closed { end };
        self.events.push(Event {
            at: self.flat.len(),
            kind: Kind::End,
        });
    }

    /// Associate bytecode bytes with the rendered position of this event.
    pub(crate) fn anchor(&mut self, offsets: Range<u32>) {
        if !offsets.is_empty() {
            self.events.push(Event {
                at: self.flat.len(),
                kind: Kind::Anchor {
                    start: offsets.start,
                    end: offsets.end,
                },
            });
        }
    }

    /// Register a collection of expression or rule offsets without allocating
    /// one event per byte. The input's original registration order is retained.
    pub(crate) fn anchor_offsets(&mut self, offsets: impl IntoIterator<Item = u32>) {
        let mut run: Option<Range<u32>> = None;
        for offset in offsets {
            if let Some(previous) = &mut run
                && previous.end == offset
            {
                previous.end += 1;
            } else if let Some(previous) = run.replace(offset..offset + 1) {
                self.anchor(previous);
            }
        }
        if let Some(run) = run {
            self.anchor(run);
        }
    }

    /// Start a physical line at `delta` indentation levels beyond the
    /// enclosing statement, plus any active newline group's extra indentation.
    pub(crate) fn hard_line(&mut self, delta: usize) {
        self.events.push(Event {
            at: self.flat.len(),
            kind: Kind::HardLine { delta },
        });
        self.flat.push('\n');
    }

    /// Move a relative expression or statement into a nested fragment.
    pub(crate) fn offset_relative_depth(&mut self, levels: usize) {
        if levels == 0 {
            return;
        }
        for event in &mut self.events {
            match &mut event.kind {
                Kind::Begin {
                    base: BaseDepth::Relative(delta),
                    ..
                }
                | Kind::HardLine { delta } => *delta += levels,
                _ => {}
            }
        }
    }

    /// Method declaration parameters and invocation arguments. The outside
    /// group can break at the parentheses without breaking at the commas.
    pub(crate) fn delimited(
        depth: usize,
        items: impl IntoIterator<Item = impl Into<Self>>,
    ) -> Self {
        Self::parenthesized(BaseDepth::Depth(depth), items, false)
    }

    /// Invocation arguments whose rendered depth is not known during lifting.
    pub(crate) fn relative_delimited(items: impl IntoIterator<Item = impl Into<Self>>) -> Self {
        Self::parenthesized(BaseDepth::Relative(0), items, false)
    }

    pub(crate) fn append_relative_arguments<'a>(
        &mut self,
        args: impl IntoIterator<Item = &'a Self>,
    ) {
        self.append_parenthesized(BaseDepth::Relative(0), args, false, Self::append_ref);
    }

    /// Record components, which register outer breaks even for an empty record.
    pub(crate) fn record(depth: usize, items: impl IntoIterator<Item = impl Into<Self>>) -> Self {
        Self::parenthesized(BaseDepth::Depth(depth), items, true)
    }

    fn parenthesized(
        depth: BaseDepth,
        items: impl IntoIterator<Item = impl Into<Self>>,
        wrap_empty: bool,
    ) -> Self {
        let mut doc = Self::new();
        doc.append_parenthesized(depth, items, wrap_empty, |doc, item| {
            doc.append(item.into())
        });
        doc
    }

    fn append_parenthesized<T>(
        &mut self,
        depth: BaseDepth,
        items: impl IntoIterator<Item = T>,
        wrap_empty: bool,
        mut append: impl FnMut(&mut Self, T),
    ) {
        let mut items = items.into_iter().peekable();
        self.push('(');
        if items.peek().is_some() || wrap_empty {
            self.begin_at(depth, 1);
            self.soft_break("", false);
            self.begin_at(depth, 0);
            for (index, item) in items.enumerate() {
                if index != 0 {
                    self.push(',');
                    self.soft_break(" ", false);
                }
                append(self, item);
            }
            self.end_group();
            self.soft_break("", true);
            self.end_group();
        }
        self.push(')');
    }

    /// Start a streamed initializer without collecting its lifted elements.
    pub(crate) fn array_initializer(&mut self, style: ArrayStyle) -> ArrayElements<'_> {
        self.push('{');
        ArrayElements {
            doc: self,
            style,
            started: false,
        }
    }

    /// Declaration annotation. Elements include `name = ` where appropriate.
    pub(crate) fn annotation(
        depth: usize,
        name: &str,
        elements: impl IntoIterator<Item = impl Into<Self>>,
    ) -> Self {
        Self::annotation_at(BaseDepth::Depth(depth), name, elements)
    }

    /// Parameter or record component annotation, emitted without explicit indent.
    pub(crate) fn inline_annotation(
        name: &str,
        elements: impl IntoIterator<Item = impl Into<Self>>,
    ) -> Self {
        Self::annotation_at(BaseDepth::InlineAnnotation, name, elements)
    }

    fn annotation_at(
        depth: BaseDepth,
        name: &str,
        elements: impl IntoIterator<Item = impl Into<Self>>,
    ) -> Self {
        let mut doc = Self::from("@");
        doc.push_str(name);
        let mut elements = elements.into_iter().peekable();
        if elements.peek().is_some() {
            doc.push_str("(");
            doc.begin_at(depth, 1);
            doc.soft_break("", false);
            for (index, element) in elements.enumerate() {
                if index != 0 {
                    doc.push_str(",");
                    doc.soft_break(" ", false);
                }
                doc.append(element.into());
            }
            doc.soft_break("", true);
            doc.push_str(")");
            doc.end_group();
        }
        doc
    }

    /// A member chain ending in an invocation. Each member is paired with
    /// whether its receiver allows a break (a simple variable does not).
    #[cfg(test)]
    pub(crate) fn invocation_chain(
        depth: usize,
        receiver: impl Into<Self>,
        members: impl IntoIterator<Item = (bool, impl Into<Self>)>,
    ) -> Self {
        let mut doc = Self::new();
        doc.begin_group(depth, 1);
        doc.append(receiver.into());
        for (break_before_dot, member) in members {
            if break_before_dot {
                doc.soft_break("", false);
            }
            doc.push_str(".");
            doc.append(member.into());
        }
        doc.end_group();
        doc
    }

    /// Append the formatted fragment and return the number of emitted linefeeds.
    /// Existing text on the destination's last line contributes to the fit test.
    #[cfg(test)]
    pub(crate) fn render(&self, out: &mut String, width: usize, indent: &str) -> usize {
        self.render_with_crlf(out, width, indent, false)
    }

    /// The Java emitter stores LF internally. In CRLF mode, use the original
    /// TextBuffer's two-unit separator for measurement without converting output.
    #[cfg(test)]
    pub(crate) fn render_with_crlf(
        &self,
        out: &mut String,
        width: usize,
        indent: &str,
        crlf: bool,
    ) -> usize {
        self.render_at(out, width, indent, crlf, 0, |_, _| {})
    }

    /// Resolve relative indentation against `depth` and report bytecode
    /// ranges with zero-based fragment lines.
    pub(crate) fn render_at(
        &self,
        out: &mut String,
        width: usize,
        indent: &str,
        crlf: bool,
        depth: usize,
        on_anchor: impl FnMut(Range<u32>, usize),
    ) -> usize {
        self.render_impl(out, width, indent, crlf, depth, on_anchor, &[], |_, _| {})
    }

    /// Also report identifier spans in rendered, zero-based UTF-16 coordinates.
    pub(crate) fn render_with_tokens_at(
        &self,
        out: &mut String,
        width: usize,
        indent: &str,
        crlf: bool,
        depth: usize,
        on_anchor: impl FnMut(Range<u32>, usize),
        on_token: impl FnMut(&Rc<Token>, TokenRange),
    ) -> usize {
        self.render_impl(
            out,
            width,
            indent,
            crlf,
            depth,
            on_anchor,
            self.token_spans(),
            on_token,
        )
    }

    fn render_impl(
        &self,
        out: &mut String,
        width: usize,
        indent: &str,
        crlf: bool,
        depth: usize,
        on_anchor: impl FnMut(Range<u32>, usize),
        tokens: &[Span],
        on_token: impl FnMut(&Rc<Token>, TokenRange),
    ) -> usize {
        assert!(self.open.is_none(), "cannot render with an open group");
        if self.events.is_empty() && tokens.is_empty() {
            out.push_str(&self.flat);
            return self.flat.bytes().filter(|&byte| byte == b'\n').count();
        }
        let (has_newline, last_line) = out
            .rsplit_once('\n')
            .map_or((false, out.as_str()), |(_, tail)| (true, tail));
        let column = units(last_line);
        let mut renderer = Renderer {
            doc: self,
            out,
            width,
            indent,
            indent_width: units(indent),
            separator_width: if crlf { 2 } else { 1 },
            depth,
            on_anchor,
            tokens,
            on_token,
            cursor: 0,
            column,
            has_newline,
            lines: 0,
        };
        renderer.render_events(0, self.events.len(), self.flat.len(), 0, None);
        debug_assert!(renderer.tokens.is_empty(), "token span was not rendered");
        renderer.lines
    }
}

/// The two array initializer forms have different continuation indent and
/// fitting boundaries in Vineflower's `NewExprent`.
#[derive(Clone, Copy)]
pub(crate) enum ArrayStyle {
    New,
    #[cfg(test)]
    Direct,
}

#[must_use = "finish the array initializer to close its formatting groups"]
pub(crate) struct ArrayElements<'a> {
    doc: &'a mut Document,
    style: ArrayStyle,
    started: bool,
}

impl ArrayElements<'_> {
    pub(crate) fn append(&mut self, element: Document) {
        if self.started {
            self.doc.push(',');
            self.doc.soft_break(" ", false);
        } else {
            let extra = match self.style {
                ArrayStyle::New => 1,
                #[cfg(test)]
                ArrayStyle::Direct => 2,
            };
            self.doc.begin_relative_group(0, extra);
            self.doc.soft_break("", false);
            self.doc.begin_relative_group(0, 0);
            self.started = true;
        }
        self.doc.append(element);
    }

    pub(crate) fn finish(self) {
        if !self.started {
            self.doc.push('}');
            return;
        }
        self.doc.end_group();
        self.doc.soft_break("", true);
        match self.style {
            ArrayStyle::New => {
                self.doc.push('}');
                self.doc.end_group();
            }
            #[cfg(test)]
            ArrayStyle::Direct => {
                self.doc.end_group();
                self.doc.push('}');
            }
        }
    }
}

struct Renderer<'a, 'out, A, T> {
    doc: &'a Document,
    out: &'out mut String,
    width: usize,
    indent: &'a str,
    indent_width: usize,
    separator_width: usize,
    depth: usize,
    on_anchor: A,
    tokens: &'a [Span],
    on_token: T,
    cursor: usize,
    column: usize,
    has_newline: bool,
    lines: usize,
}

impl<A, T> Renderer<'_, '_, A, T>
where
    A: FnMut(Range<u32>, usize),
    T: FnMut(&Rc<Token>, TokenRange),
{
    fn render_events(
        &mut self,
        mut index: usize,
        end: usize,
        end_at: usize,
        inherited: usize,
        active: Option<(BaseDepth, usize)>,
    ) {
        let mut extra = active.map_or(inherited, |(_, extra)| extra);
        while index < end {
            let event = &self.doc.events[index];
            self.copy_until(event.at, extra);
            match event.kind {
                Kind::Begin {
                    link: Link::Closed { end },
                    base,
                    extra: nesting,
                    has_breaks,
                    ..
                } => {
                    let end_at = self.doc.events[end].at;
                    let active = (has_breaks && self.overflows(index + 1..end, end_at, extra))
                        .then_some((base, extra + nesting));
                    self.render_events(index + 1, end, end_at, extra, active);
                    index = end + 1;
                }
                Kind::Break { len, dedent } => {
                    if let Some((base, _)) = active {
                        if dedent {
                            extra = inherited;
                        }
                        self.cursor += len;
                        self.newline(base.with_extra(self.depth, extra));
                    }
                    index += 1;
                }
                Kind::Anchor { start, end } => {
                    (self.on_anchor)(start..end, self.lines);
                    index += 1;
                }
                Kind::HardLine { delta } => {
                    self.cursor += 1;
                    self.newline(self.depth + delta + extra);
                    index += 1;
                }
                Kind::Begin {
                    link: Link::Open { .. },
                    ..
                }
                | Kind::End => {
                    unreachable!("rendering only finished groups between their boundary events");
                }
            }
        }
        self.copy_until(end_at, extra);
    }

    fn overflows(&self, events: Range<usize>, end: usize, extra: usize) -> bool {
        let mut length = if self.doc.flat.as_bytes().get(self.cursor) == Some(&b'\n') {
            // TextBuffer's lastIndexOf is inclusive of the group's start.
            0
        } else {
            // Its first-line measurement starts at the preceding separator,
            // not at the first character after it.
            self.column
                + if self.has_newline {
                    self.separator_width
                } else {
                    0
                }
        };
        if length > self.width {
            return true;
        }
        let mut hard_lines = self.doc.events[events]
            .iter()
            .filter_map(|event| match event.kind {
                Kind::HardLine { delta } => Some((event.at, delta)),
                _ => None,
            })
            .peekable();
        for (offset, ch) in self.doc.flat[self.cursor..end].char_indices() {
            length = if ch == '\n' {
                // TextBuffer's inherited indent in this test is in levels,
                // not code units. A typed hard line adds its explicit indent.
                let explicit = if hard_lines
                    .peek()
                    .is_some_and(|&(at, _)| at == self.cursor + offset)
                {
                    let (_, delta) = hard_lines.next().expect("peeked typed hard line");
                    (self.depth + delta) * self.indent_width
                } else {
                    0
                };
                extra + explicit
            } else {
                length + ch.len_utf16()
            };
            if length > self.width {
                return true;
            }
        }
        self.doc.flat.as_bytes().get(end) == Some(&b'\n')
            && extra.saturating_sub(self.separator_width) > self.width
    }

    fn copy_until(&mut self, end: usize, extra: usize) {
        let doc = self.doc;
        for part in doc.flat[self.cursor..end].split_inclusive('\n') {
            let start = self.cursor;
            self.cursor += part.len();
            let (line, newline) = part
                .strip_suffix('\n')
                .map_or((part, false), |line| (line, true));
            let mut measured = 0;
            let end = start + line.len();
            while let Some((span, remaining)) = self.tokens.split_first()
                && span.start < end
            {
                let offset = span.start - start;
                self.column += units(&line[measured..offset]);
                measured = offset;
                (self.on_token)(
                    &span.token,
                    TokenRange::on_line(self.lines, self.column, span.width),
                );
                self.tokens = remaining;
            }
            self.out.push_str(line);
            if newline {
                let continues = self.cursor < doc.flat.len();
                let blank =
                    self.cursor + 1 < doc.flat.len() && doc.flat.as_bytes()[self.cursor] == b'\n';
                self.newline(if continues && !blank { extra } else { 0 });
            } else {
                self.column += units(&line[measured..]);
            }
        }
    }

    fn newline(&mut self, depth: usize) {
        self.out.push('\n');
        for _ in 0..depth {
            self.out.push_str(self.indent);
        }
        self.column = self.indent_width * depth;
        self.has_newline = true;
        self.lines += 1;
    }
}

fn units(text: &str) -> usize {
    text.chars().map(char::len_utf16).sum()
}

#[cfg(test)]
mod tests {
    use super::Document;

    #[test]
    fn long_method_declaration_matches_upstream() {
        let mut method = Document::from("   public void foo");
        method.append(Document::delimited(
            1,
            (1..=16).map(|i| format!("int param{i}")),
        ));
        method.push_str(" {");
        let mut out = String::from("public class TestLongMethodDeclaration {\n");
        let original = out.len();
        assert_eq!(method.render(&mut out, 160, "   "), 17);
        assert_eq!(
            &out[original..],
            concat!(
                "   public void foo(\n",
                "      int param1,\n",
                "      int param2,\n",
                "      int param3,\n",
                "      int param4,\n",
                "      int param5,\n",
                "      int param6,\n",
                "      int param7,\n",
                "      int param8,\n",
                "      int param9,\n",
                "      int param10,\n",
                "      int param11,\n",
                "      int param12,\n",
                "      int param13,\n",
                "      int param14,\n",
                "      int param15,\n",
                "      int param16\n",
                "   ) {",
            ),
        );
        out.truncate(original);
        assert_eq!(method.render(&mut out, 250, "   "), 0);
        assert_eq!(&out[original..], method.as_flat());
    }

    #[test]
    fn big_record_matches_upstream() {
        let mut record = Document::from("public record TestRecordBig");
        record.append(Document::record(
            0,
            (1..=16).map(|i| format!("int comp{i}")),
        ));
        record.push_str(" {\n}\n");
        let mut out = String::from("package pkg;\n\n");
        assert_eq!(record.render(&mut out, 160, "   "), 19);
        assert_eq!(
            out,
            concat!(
                "package pkg;\n\n",
                "public record TestRecordBig(\n",
                "   int comp1,\n",
                "   int comp2,\n",
                "   int comp3,\n",
                "   int comp4,\n",
                "   int comp5,\n",
                "   int comp6,\n",
                "   int comp7,\n",
                "   int comp8,\n",
                "   int comp9,\n",
                "   int comp10,\n",
                "   int comp11,\n",
                "   int comp12,\n",
                "   int comp13,\n",
                "   int comp14,\n",
                "   int comp15,\n",
                "   int comp16\n",
                ") {\n}\n",
            ),
        );
    }

    #[test]
    fn long_method_chain_matches_upstream() {
        let mut call = Document::from("      ");
        call.append(Document::invocation_chain(
            2,
            "this",
            (0..16).map(|i| (i != 0, "longMethodInvocation()")),
        ));
        call.push_str(";");
        let mut out = String::new();
        assert_eq!(call.render(&mut out, 160, "   "), 15);
        assert_eq!(
            out,
            format!(
                "      this{}.longMethodInvocation();",
                ".longMethodInvocation()\n         ".repeat(15),
            ),
        );
    }

    #[test]
    fn member_annotation_matches_upstream() {
        let mut source = String::from("   @Deprecated\n   ");
        let annotation = Document::annotation(
            1,
            "MoreAnnotations",
            [
                "intValue = 25".into(),
                "enumValue = TestEnum.SecondValue".into(),
                {
                    let mut value = Document::from("annotationValue = ");
                    value.append(Document::annotation(1, "NestedAnnotation", ["\"Bee\""]));
                    value
                },
                "classValue = String.class".into(),
                "booleanArray = false".into(),
                "enumArray = {TestEnum.FirstValue, TestEnum.SecondValue}".into(),
                "classArray = {String.class, StringBuilder.class}".into(),
            ],
        );
        assert_eq!(annotation.render(&mut source, 120, "   "), 8);
        assert_eq!(
            source,
            concat!(
                "   @Deprecated\n",
                "   @MoreAnnotations(\n",
                "      intValue = 25,\n",
                "      enumValue = TestEnum.SecondValue,\n",
                "      annotationValue = @NestedAnnotation(\"Bee\"),\n",
                "      classValue = String.class,\n",
                "      booleanArray = false,\n",
                "      enumArray = {TestEnum.FirstValue, TestEnum.SecondValue},\n",
                "      classArray = {String.class, StringBuilder.class}\n",
                "   )",
            ),
        );
    }

    #[test]
    fn argument_group_can_fit_after_the_parenthesis_break() {
        let mut out = String::from("  return f");
        let mut args = Document::delimited(1, ["aa", "bb", "cc"]);
        args.push_str(";");
        assert_eq!(args.render(&mut out, 16, "  "), 2);
        assert_eq!(out, "  return f(\n    aa, bb, cc\n  );");
    }

    #[test]
    fn nested_invocation_arguments_dedent_to_the_enclosing_group() {
        let mut inner = Document::from("inner");
        inner.append(Document::delimited(1, ["firstArgument", "secondArgument"]));
        let mut outer = Document::delimited(1, [inner, "fallback".into()]);
        outer.push_str(";");
        let mut out = String::from("  return outer");
        assert_eq!(outer.render(&mut out, 24, "  "), 6);
        assert_eq!(
            out,
            concat!(
                "  return outer(\n",
                "    inner(\n",
                "      firstArgument,\n",
                "      secondArgument\n",
                "    ),\n",
                "    fallback\n",
                "  );",
            ),
        );
    }

    #[test]
    fn only_annotation_counts_its_closing_parenthesis() {
        let mut out = String::from("@A");
        let args = Document::delimited(0, ["x"]);
        assert_eq!(args.render(&mut out, 4, "  "), 0);
        assert_eq!(out, "@A(x)");
        out.clear();
        assert_eq!(
            Document::annotation(0, "A", ["x"]).render(&mut out, 4, "  "),
            2
        );
        assert_eq!(out, "@A(\n  x\n)");
    }

    #[test]
    fn inline_annotation_retains_the_surrounding_groups_extra_indent() {
        let mut out = String::from("  f");
        let mut parameter = Document::inline_annotation("A", ["\"abcdefgh\""]);
        parameter.push_str(" int n");
        let args = Document::delimited(1, [parameter]);
        assert_eq!(args.render(&mut out, 10, "  "), 4);
        assert_eq!(out, "  f(\n    @A(\n  \"abcdefgh\"\n) int n\n  )");
    }

    #[test]
    fn width_uses_utf16_and_counts_the_preceding_line_separator() {
        let args = Document::delimited(1, ["😃"]);
        let mut out = String::from("other\n  f");
        assert_eq!(args.render(&mut out, 7, "  "), 0);
        assert_eq!(out, "other\n  f(😃)");
        out.truncate("other\n  f".len());
        assert_eq!(args.render_with_crlf(&mut out, 7, "  ", true), 2);
        assert_eq!(out, "other\n  f(\n    😃\n  )");
        out = String::from("  f");
        assert_eq!(args.render(&mut out, 5, "  "), 2);
    }

    #[test]
    fn hard_lines_inherit_extra_indent_except_blank_lines() {
        let mut out = String::from("  f");
        let args = Document::delimited(1, ["a,\n  b\n\n  c"]);
        assert_eq!(args.render(&mut out, 5, "  "), 5);
        assert_eq!(out, "  f(\n    a,\n    b\n\n    c\n  )");
    }

    #[test]
    fn adjacent_empty_breaks_apply_to_empty_records_but_not_methods() {
        let mut out = String::from("record R");
        assert_eq!(
            Document::record(0, std::iter::empty::<&str>()).render(&mut out, 4, "   "),
            2,
        );
        assert_eq!(out, "record R(\n   \n)");
        out = String::from("void f");
        assert_eq!(
            Document::delimited(0, std::iter::empty::<&str>()).render(&mut out, 4, "   "),
            0,
        );
        assert_eq!(out, "void f()");
    }

    #[test]
    fn promoted_qualifier_chain_places_bytecode_anchors_on_each_segment() {
        let mut expression = Document::from("this");
        assert!(!expression.begin_qualifier(false, false));
        expression.push('.');
        expression.anchor(1..4);
        expression.push_str("longField");
        assert!(expression.begin_qualifier(true, true));
        expression.end_group(); // Field ends the group before the dot.
        expression.push('.');
        expression.anchor(4..7);
        expression.push_str("secondField");
        assert!(expression.begin_qualifier(true, true));
        expression.push('.');
        expression.anchor(7..10);
        expression.push_str("call");
        expression.append_relative_arguments([]);
        expression.end_group();
        expression.push(';');

        let mut out = String::from("    ");
        let mut anchors = Vec::new();
        assert_eq!(
            expression.render_at(&mut out, 22, "  ", false, 2, |offsets, line| {
                anchors.push((offsets, line));
            }),
            2,
        );
        assert_eq!(
            out,
            "    this.longField\n      .secondField\n      .call();"
        );
        assert_eq!(anchors, [(1..4, 0), (4..7, 1), (7..10, 2)]);
    }

    #[test]
    fn composing_an_array_access_seals_the_receiver_chain() {
        let mut expression = Document::from("instance.first()");
        assert!(expression.begin_qualifier(true, false));
        expression.push_str(".next()");
        expression.end_group();
        expression.seal_qualifier();
        expression.push_str("[0]");
        assert!(expression.begin_qualifier(true, true));
        expression.push_str(".last()");
        expression.end_group();
        let mut out = String::new();
        assert_eq!(expression.render(&mut out, 14, "  "), 2);
        assert_eq!(out, "instance.first()\n    .next()[0]\n  .last()");
    }

    #[test]
    fn advances_relative_depth_and_anchors_within_a_typed_fragment() {
        let first_arg = Document::from("aaaaaaaaaaaa");
        let mut second_arg = Document::new();
        second_arg.anchor(10..13);
        second_arg.push_str("bbbbbbbbbbbb");
        let mut arm = Document::from("case 0 -> choose");
        arm.append_relative_arguments([&first_arg, &second_arg]);
        arm.offset_relative_depth(1);
        arm.push(';');

        let mut expression = Document::from("switch (state) {");
        expression.hard_line(1);
        expression.append(arm);
        expression.hard_line(0);
        expression.push('}');
        expression.surround("return ", ";");

        let mut out = String::from("      ");
        let mut anchors = Vec::new();
        assert_eq!(
            expression.render_at(&mut out, 36, "   ", false, 2, |offsets, line| {
                anchors.push((offsets, line));
            }),
            5,
        );
        assert_eq!(
            out,
            concat!(
                "      return switch (state) {\n",
                "         case 0 -> choose(\n",
                "            aaaaaaaaaaaa,\n",
                "            bbbbbbbbbbbb\n",
                "         );\n",
                "      };",
            ),
        );
        assert_eq!(anchors, [(10..13, 3)]);
    }

    #[test]
    fn plain_composition_does_not_allocate_layout_events() {
        let mut plain = Document::from("name");
        assert!(!plain.begin_qualifier(false, false));
        plain.append_relative_arguments([]);
        plain.append_ref(&Document::from(";"));
        assert_eq!(plain.pop(), Some(';'));
        plain.surround("(", ")");
        assert_eq!(plain, "(name())");
        assert_eq!(plain.events.capacity(), 0);
    }

    #[test]
    fn rewriting_a_literal_assignment_prefix_preserves_expression_events() {
        let mut initializer = Document::from("int local = ");
        initializer.push_str("supply");
        let mut value = Document::new();
        value.anchor(1..3);
        value.push_str("\"a long value\"");
        initializer.append_relative_arguments([&value]);
        initializer.push(';');
        initializer.replace_literal_prefix("int local = ".len(), "x = ");
        let mut out = String::new();
        let mut anchors = Vec::new();
        assert_eq!(
            initializer.render_at(&mut out, 16, "  ", false, 0, |offsets, line| {
                anchors.push((offsets, line));
            }),
            2,
        );
        assert_eq!(out, "x = supply(\n  \"a long value\"\n);");
        assert_eq!(anchors, [(1..3, 1)]);
    }

    #[test]
    fn explicit_and_direct_array_initializers_measure_different_boundaries() {
        use super::ArrayStyle;

        let mut explicit = Document::from("new int[]");
        let mut elements = explicit.array_initializer(ArrayStyle::New);
        elements.append(Document::from("1234"));
        elements.finish();
        let mut out = String::new();
        assert_eq!(explicit.render(&mut out, 14, "  "), 2);
        assert_eq!(out, "new int[]{\n  1234\n}");

        let mut direct = Document::from("int[] a = ");
        let mut elements = direct.array_initializer(ArrayStyle::Direct);
        elements.append(Document::from("1234"));
        elements.finish();
        out.clear();
        assert_eq!(direct.render(&mut out, 15, "  "), 0);
        assert_eq!(out, "int[] a = {1234}");
        out.clear();
        assert_eq!(direct.render(&mut out, 14, "  "), 2);
        assert_eq!(out, "int[] a = {\n    1234\n}");
    }

    #[test]
    fn switch_rule_offsets_register_as_consecutive_runs() {
        let mut doc = Document::from("switch (key) {");
        doc.hard_line(1);
        doc.anchor_offsets([1, 2, 3, 6, 7, 4]);
        doc.push_str("default -> 1;");
        doc.hard_line(0);
        doc.push('}');
        let mut out = String::new();
        let mut anchors = Vec::new();
        assert_eq!(
            doc.render_at(&mut out, 80, "  ", false, 0, |offsets, line| {
                anchors.push((offsets, line));
            }),
            2,
        );
        assert_eq!(out, "switch (key) {\n  default -> 1;\n}");
        assert_eq!(anchors, [(1..4, 1), (6..8, 1), (4..5, 1)]);
    }
}
