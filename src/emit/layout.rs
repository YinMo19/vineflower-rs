// Based on Vineflower TextBuffer, ClassWriter, RecordHelper, and the Java expression writers (Apache-2.0).

/// A flat Java fragment with possible line breaks registered by its producer.
/// Nested groups make separate fit decisions after earlier breaks have been applied.
#[derive(Clone, Debug, Default)]
pub(crate) struct Document {
    flat: String,
    events: Vec<Event>,
    open: Option<usize>,
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
    },
    Break {
        len: usize,
        dedent: bool,
    },
    End,
}

#[derive(Clone, Copy, Debug)]
enum Link {
    Open { parent: Option<usize> },
    Closed { end: usize },
}

#[derive(Clone, Copy, Debug)]
enum BaseDepth {
    Depth(usize),
    InlineAnnotation,
}

impl BaseDepth {
    fn with_extra(self, extra: usize) -> usize {
        match self {
            Self::Depth(base) => base + extra,
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

impl Document {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn push_str(&mut self, text: &str) {
        self.flat.push_str(text);
    }

    pub(crate) fn as_flat(&self) -> &str {
        &self.flat
    }

    pub(crate) fn into_flat(self) -> String {
        self.flat
    }

    pub(crate) fn append(&mut self, fragment: Self) {
        assert!(fragment.open.is_none(), "appended document has an open group");
        if self.flat.is_empty() && self.events.is_empty() {
            *self = fragment;
            return;
        }
        let offset = self.flat.len();
        let event_offset = self.events.len();
        self.flat.push_str(&fragment.flat);
        self.events.extend(fragment.events.into_iter().map(|mut event| {
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
    pub(crate) fn begin_group(&mut self, base_depth: usize, extra_depth: usize) {
        self.begin_at(BaseDepth::Depth(base_depth), extra_depth);
    }

    fn begin_at(&mut self, base: BaseDepth, extra: usize) {
        let parent = self.open.replace(self.events.len());
        self.events.push(Event {
            at: self.flat.len(),
            kind: Kind::Begin {
                link: Link::Open { parent },
                base,
                extra,
                has_breaks: false,
            },
        });
    }

    /// Emit `flat` when the group fits. When it doesn't, emit a line break
    /// instead; `dedent` removes this group's extra indentation from here on.
    pub(crate) fn soft_break(&mut self, flat: &str, dedent: bool) {
        let open = self.open.expect("soft line break outside a group");
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
        let open = self.open.expect("no group to close");
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

    /// Method declaration parameters and invocation arguments. The outside
    /// group can break at the parentheses without breaking at the commas.
    pub(crate) fn delimited(
        depth: usize,
        items: impl IntoIterator<Item = impl Into<Self>>,
    ) -> Self {
        Self::parenthesized(depth, items, false)
    }

    /// Record components, which register outer breaks even for an empty record.
    pub(crate) fn record(
        depth: usize,
        items: impl IntoIterator<Item = impl Into<Self>>,
    ) -> Self {
        Self::parenthesized(depth, items, true)
    }

    fn parenthesized(
        depth: usize,
        items: impl IntoIterator<Item = impl Into<Self>>,
        wrap_empty: bool,
    ) -> Self {
        let mut items = items.into_iter().peekable();
        let mut doc = Self::from("(");
        if items.peek().is_some() || wrap_empty {
            doc.begin_group(depth, 1);
            doc.soft_break("", false);
            doc.begin_group(depth, 0);
            for (index, item) in items.enumerate() {
                if index != 0 {
                    doc.push_str(",");
                    doc.soft_break(" ", false);
                }
                doc.append(item.into());
            }
            doc.end_group();
            doc.soft_break("", true);
            doc.end_group();
        }
        doc.push_str(")");
        doc
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
    pub(crate) fn render(&self, out: &mut String, width: usize, indent: &str) -> usize {
        self.render_with_crlf(out, width, indent, false)
    }

    /// The Java emitter stores LF internally. In CRLF mode, use the original
    /// TextBuffer's two-unit separator for measurement without converting output.
    pub(crate) fn render_with_crlf(
        &self,
        out: &mut String,
        width: usize,
        indent: &str,
        crlf: bool,
    ) -> usize {
        assert!(self.open.is_none(), "cannot render with an open group");
        if self.events.is_empty() {
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
            cursor: 0,
            column,
            has_newline,
            lines: 0,
        };
        renderer.render_events(0, self.events.len(), self.flat.len(), 0, None);
        renderer.lines
    }
}

struct Renderer<'a, 'out> {
    doc: &'a Document,
    out: &'out mut String,
    width: usize,
    indent: &'a str,
    indent_width: usize,
    separator_width: usize,
    cursor: usize,
    column: usize,
    has_newline: bool,
    lines: usize,
}

impl Renderer<'_, '_> {
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
                } => {
                    let end_at = self.doc.events[end].at;
                    let active = (has_breaks && self.overflows(end_at, extra))
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
                        self.newline(base.with_extra(extra));
                    }
                    index += 1;
                }
                Kind::Begin { link: Link::Open { .. }, .. } | Kind::End => {
                    unreachable!("rendering only finished groups between their boundary events");
                }
            }
        }
        self.copy_until(end_at, extra);
    }

    fn overflows(&self, end: usize, extra: usize) -> bool {
        let mut length = if self.doc.flat.as_bytes().get(self.cursor) == Some(&b'\n') {
            // TextBuffer's lastIndexOf is inclusive of the group's start.
            0
        } else {
            // Its first-line measurement starts at the preceding separator,
            // not at the first character after it.
            self.column + if self.has_newline { self.separator_width } else { 0 }
        };
        if length > self.width {
            return true;
        }
        for ch in self.doc.flat[self.cursor..end].chars() {
            length = if ch == '\n' {
                // Hard lines inside a group already carry their explicit
                // indentation; upstream adds the inherited depth to the fit test.
                extra
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
            self.cursor += part.len();
            if let Some(line) = part.strip_suffix('\n') {
                self.out.push_str(line);
                let continues = self.cursor < doc.flat.len();
                let blank = self.cursor + 1 < doc.flat.len()
                    && doc.flat.as_bytes()[self.cursor] == b'\n';
                self.newline(if continues && !blank { extra } else { 0 });
            } else {
                self.out.push_str(part);
                self.column += units(part);
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
        method.append(Document::delimited(1, (1..=16).map(|i| format!("int param{i}"))));
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
        record.append(Document::record(0, (1..=16).map(|i| format!("int comp{i}"))));
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
        assert_eq!(Document::annotation(0, "A", ["x"]).render(&mut out, 4, "  "), 2);
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
}
