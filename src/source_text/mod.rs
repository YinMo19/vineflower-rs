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
        role: GroupRole,
    },
    Break {
        len: usize,
        dedent: bool,
    },
    Anchor {
        start: u32,
        end: u32,
        branch: Option<(u32, u32)>,
    },
    OmittedBytes {
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

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum GroupRole {
    Plain,
    Qualifier,
    Infix(Infix),
}

/// An operator's Java precedence (higher binds more tightly). The producer
/// decides when an operand of equal precedence can omit its parentheses.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct Infix {
    pub(crate) symbol: &'static str,
    pub(crate) precedence: u8,
}

impl Infix {
    pub(crate) const OR: Self = Self::new("||", 2);
    pub(crate) const AND: Self = Self::new("&&", 3);
    pub(crate) const TERNARY: Self = Self::new("?", 1);

    pub(crate) const fn new(symbol: &'static str, precedence: u8) -> Self {
        Self { symbol, precedence }
    }
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
        self.events
            .iter()
            .any(|event| !matches!(event.kind, Kind::Anchor { branch: Some(_), .. }))
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
                .all(|event| matches!(event.kind, Kind::Anchor { .. } | Kind::OmittedBytes { .. })),
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
                .all(|event| matches!(event.kind, Kind::End | Kind::Anchor { .. } | Kind::OmittedBytes { .. })),
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
                role: GroupRole::Plain,
            },
        });
    }

    pub(crate) fn begin_infix(&mut self, infix: Infix) {
        self.begin_relative_group(0, 1);
        let Some(Event { kind: Kind::Begin { role, .. }, .. }) = self.events.last_mut() else {
            unreachable!("a new group ends with its begin event");
        };
        *role = GroupRole::Infix(infix);
    }

    pub(crate) fn infix(&self) -> Option<Infix> {
        self.infix_span().map(|(_, _, infix, _)| infix)
    }

    fn infix_span(&self) -> Option<(usize, usize, Infix, bool)> {
        let metadata = |event: &Event| {
            matches!(event.kind, Kind::Anchor { .. } | Kind::OmittedBytes { .. })
        };
        let start = self.events.iter().position(|event| !metadata(event))?;
        let Event {
            at: 0,
            kind: Kind::Begin {
                link: Link::Closed { end },
                role: GroupRole::Infix(infix),
                has_breaks,
                ..
            },
        } = self.events[start]
        else {
            return None;
        };
        (self.events[end].at == self.flat.len() && self.events[end + 1..].iter().all(metadata))
            .then_some((start, end, infix, has_breaks))
    }

    /// Equal-precedence unparenthesized operands share their parent's breaks.
    /// Keep the operand's complete flat text, nested groups, and metadata.
    pub(crate) fn append_infix_operand(&mut self, fragment: &Self, parens: bool) {
        if parens {
            self.push('(');
            self.begin_relative_group(0, 1);
            self.soft_break("", false);
            self.append_ref(fragment);
            self.soft_break("", true);
            self.end_group();
            self.push(')');
            return;
        }
        let open = self.open.expect("infix operand outside a group").get() - 1;
        let Kind::Begin { role: GroupRole::Infix(parent), has_breaks, .. } =
            &mut self.events[open].kind
        else {
            unreachable!("infix operands belong to an infix group");
        };
        if let Some((start, end, child, child_breaks)) = fragment.infix_span()
            && child.precedence == parent.precedence
        {
            *has_breaks |= child_breaks;
            self.append_tokens(fragment.tokens.clone());
            self.extend(
                &fragment.flat,
                fragment.events.iter().cloned().enumerate().filter_map(|(index, mut event)| {
                    if index == start || index == end {
                        return None;
                    }
                    if let Kind::Begin { link: Link::Closed { end: nested }, .. } = &mut event.kind
                    {
                        *nested -= 1;
                    }
                    Some(event)
                }),
            );
        } else {
            self.append_ref(fragment);
        }
    }

    pub(crate) fn infix_separator(&mut self, symbol: &str) {
        self.soft_break(" ", false);
        self.push_str(symbol);
        self.push(' ');
    }

    pub(crate) fn infix_expression(infix: Infix, operands: [(&Self, bool); 2]) -> Self {
        let [(left, left_parens), (right, right_parens)] = operands;
        let mut text = Self::new();
        text.begin_infix(infix);
        text.append_infix_operand(left, left_parens);
        text.infix_separator(infix.symbol);
        text.append_infix_operand(right, right_parens);
        text.end_group();
        text
    }

    pub(crate) fn ternary_expression(operands: [&Self; 3], selector_parens: bool) -> Self {
        let [selector, yes, no] = operands;
        let mut text = Self::new();
        text.begin_infix(Infix::TERNARY);
        text.append_infix_operand(selector, selector_parens);
        text.infix_separator("?");
        text.append_infix_operand(yes, yes.infix() == Some(Infix::TERNARY));
        text.infix_separator(":");
        text.append_infix_operand(no, no.infix() == Some(Infix::TERNARY));
        text.end_group();
        text
    }

    /// Preserve the formatting of an embedded member chain without letting a
    /// containing non-member expression promote it into a later chain.
    pub(crate) fn seal_qualifier(&mut self) {
        if let Some(Event {
            at: 0,
            kind: Kind::Begin { role, .. },
        }) = self.events.first_mut()
        {
            if *role == GroupRole::Qualifier {
                *role = GroupRole::Plain;
            }
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
                        role: GroupRole::Qualifier,
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
                    .all(|event| matches!(event.kind, Kind::Anchor { .. } | Kind::OmittedBytes { .. })),
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
                        role: GroupRole::Qualifier,
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
                    branch: None,
                },
            });
        }
    }

    /// Carry a direct local test through speculative condition folding. Until
    /// a boolean value is actually materialized, its statement keeps owning
    /// both the load and the branch.
    pub(crate) fn defer_local_predicate(&mut self, load: Range<u32>, branch: Range<u32>) {
        self.events.push(Event {
            at: self.flat.len(),
            kind: Kind::Anchor {
                start: load.start,
                end: load.end,
                branch: Some((branch.start, branch.end)),
            },
        });
    }

    /// When a decision graph becomes a short-circuit value, the branches
    /// belong to the whole expression; the loads follow their predicate
    /// leaves across the infix layout's soft breaks.
    pub(crate) fn materialize_short_circuit_predicates(&mut self) -> bool {
        if !matches!(self.infix(), Some(Infix::AND | Infix::OR)) {
            return false;
        }
        // Each logical separator introduces one additional operand. Do not
        // guess origins for comparisons, invocations, or ternary operands.
        let mut operands = 1;
        let mut predicates = 0;
        for event in &self.events {
            match event.kind {
                Kind::Begin {
                    role: GroupRole::Infix(Infix::AND | Infix::OR) | GroupRole::Plain,
                    ..
                }
                | Kind::End
                | Kind::Break { len: 0, .. } => {}
                Kind::Break { len: 1, dedent: false } => operands += 1,
                Kind::Anchor { branch: Some(_), .. } => predicates += 1,
                _ => return false,
            }
        }
        if operands != predicates {
            return false;
        }
        let original_len = self.events.len();
        for index in 0..original_len {
            if let Kind::Anchor { branch, .. } = &mut self.events[index].kind
                && let Some((start, end)) = branch.take()
            {
                self.events.push(Event {
                    at: 0,
                    kind: Kind::Anchor { start, end, branch: None },
                });
            }
        }
        let added = self.events.len() - original_len;
        debug_assert_eq!(added, predicates);
        for event in &mut self.events[..original_len] {
            if let Kind::Begin { link: Link::Closed { end }, .. } = &mut event.kind {
                *end += added;
            }
        }
        self.events.rotate_right(added);
        true
    }

    /// Bytecode anchors in the flat representation, for text fragments
    /// interleaved with externally emitted anonymous class bodies.
    pub(crate) fn flat_anchors(&self) -> impl Iterator<Item = (usize, Range<u32>)> + '_ {
        self.events.iter().filter_map(|event| match event.kind {
            Kind::Anchor { start, end, branch: None } => Some((event.at, start..end)),
            _ => None,
        })
    }

    /// A compiler-only operation absorbed by an expression rewrite. Keep
    /// its CFG provenance but omit it from source mappings.
    pub(crate) fn omit_bytes(&mut self, offsets: Range<u32>) {
        if !offsets.is_empty() {
            self.events.push(Event {
                at: self.flat.len(),
                kind: Kind::OmittedBytes { start: offsets.start, end: offsets.end },
            });
        }
    }

    pub(crate) fn omitted_bytecode(&self) -> impl Iterator<Item = Range<u32>> + '_ {
        self.events.iter().filter_map(|event| match event.kind {
            Kind::OmittedBytes { start, end } => Some(start..end),
            _ => None,
        })
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

    pub(crate) fn relative_delimited_with<T>(
        items: impl IntoIterator<Item = T>,
        append: impl FnMut(&mut Self, T),
    ) -> Self {
        let mut doc = Self::new();
        doc.append_parenthesized(BaseDepth::Relative(0), items, false, append);
        doc
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
    pub(crate) fn array_initializer(&mut self) -> ArrayElements<'_> {
        self.push('{');
        ArrayElements {
            doc: self,
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

#[must_use = "finish the array initializer to close its formatting groups"]
pub(crate) struct ArrayElements<'a> {
    doc: &'a mut Document,
    started: bool,
}

impl ArrayElements<'_> {
    pub(crate) fn append(&mut self, element: Document) {
        if self.started {
            self.doc.push(',');
            self.doc.soft_break(" ", false);
        } else {
            self.doc.begin_relative_group(0, 1);
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
        self.doc.push('}');
        self.doc.end_group();
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
                Kind::Anchor { start, end, branch } => {
                    if branch.is_none() {
                        (self.on_anchor)(start..end, self.lines);
                    }
                    index += 1;
                }
                Kind::OmittedBytes { .. } => index += 1,
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
