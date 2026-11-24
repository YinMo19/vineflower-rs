// Based on IFabricJavadocProvider. Copyright 2019 FabricMC project. Apache-2.0.
use std::fmt;

use crate::classfile::{ClassFile, Member};

/// Style of the comment supplied by a [`JavadocProvider`].
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum JavadocStyle {
    #[default]
    Html,
    Markdown,
}

/// A class, field or method in the original class file, before source renaming.
#[derive(Clone, Copy, Debug)]
pub enum JavadocTarget<'a, 'c> {
    Class(&'c ClassFile<'a>),
    Field(&'c ClassFile<'a>, &'c Member<'a>),
    Method(&'c ClassFile<'a>, &'c Member<'a>),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Javadoc {
    pub text: String,
    pub style: JavadocStyle,
}

/// Optional external documentation attached to declarations at render time.
pub trait JavadocProvider: Send + Sync {
    fn javadoc(&self, target: JavadocTarget<'_, '_>) -> Option<Javadoc>;
}

impl fmt::Debug for dyn JavadocProvider {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("JavadocProvider")
    }
}

pub(crate) fn lines(doc: &Javadoc, mut emit: impl FnMut(&str)) {
    let prefix = match doc.style {
        JavadocStyle::Html => {
            emit("/**");
            " * "
        }
        JavadocStyle::Markdown => "/// ",
    };
    let mut line = String::new();
    for text in doc.text.split_terminator('\n') {
        line.clear();
        line.push_str(prefix);
        // A provider controls documentation, not the surrounding Java syntax.
        // Escaping both a literal terminator and all backslashes prevents a
        // Java Unicode escape in a comment from injecting uncommented source.
        for part in text.strip_suffix('\r').unwrap_or(text).split_inclusive("*/") {
            if let Some(text) = part.strip_suffix("*/") {
                escape(&mut line, text);
                line.push_str("*&#47;");
            } else {
                escape(&mut line, part);
            }
        }
        emit(&line);
    }
    if doc.style == JavadocStyle::Html {
        emit(" */");
    }
}

fn escape(out: &mut String, text: &str) {
    for segment in text.split_inclusive('\\') {
        if let Some(prefix) = segment.strip_suffix('\\') {
            out.push_str(prefix);
            out.push_str("&#92;");
        } else {
            out.push_str(segment);
        }
    }
}
