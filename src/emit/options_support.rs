// Based on Vineflower ClassWriter (Apache-2.0).
// Copyright 2000-2021 JetBrains s.r.o.
use crate::{classfile::find_attribute, javadoc::{self, JavadocTarget}};

use super::{DecompileError, Writer};

impl Writer<'_, '_> {
    pub(super) fn sourcefile_comment(&mut self) -> Result<(), DecompileError> {
        if !self.options.sourcefile_comments {
            return Ok(());
        }
        let pool = &self.class.pool;
        if let Some(data) = find_attribute(&self.class.attributes, pool, "SourceFile")? {
            let index = u16::from_be_bytes(data.try_into().map_err(|_| DecompileError::InvalidAttribute("SourceFile"))?);
            let file = pool.utf8(index)?;
            let mut comment = String::from("// $VF: Compiled from ");
            for c in file.chars() {
                // Class-file names are untrusted. Preserve comment termination.
                match c {
                    '\r' | '\n' | '\\' => comment.push_str(&format!("\\\\u{:04x}", u32::from(c))),
                    _ => comment.push(c),
                }
            }
            self.line(0, &comment);
        }
        Ok(())
    }

    pub(super) fn javadoc(&mut self, depth: usize, target: JavadocTarget<'_, '_>) {
        if let Some(doc) = self.options.javadoc.as_deref().and_then(|provider| provider.javadoc(target)) {
            javadoc::lines(&doc, |line| self.line(depth, line));
        }
    }

    pub(super) fn matches_method(&self, name: &str, desc: &str) -> bool {
        let target = &self.options.method_to_decompile;
        if target.is_empty() {
            return true;
        }
        let local = |target: &str| target.strip_prefix(name) == Some(desc);
        (self.depth == 0 && local(target)) || target.strip_prefix(self.owner)
            .and_then(|tail| tail.strip_prefix('.')).is_some_and(local)
    }

    pub(super) fn matches_member_class(&self, name: &str) -> bool {
        let target = &self.options.method_to_decompile;
        target.is_empty() || target.strip_prefix(name).is_some_and(|tail| tail.starts_with(['.', '$']))
    }
}
