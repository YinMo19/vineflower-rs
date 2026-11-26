// SPDX-License-Identifier: Apache-2.0

//! Upstream's `modules.renamer` package: renaming of obfuscated identifiers.

pub mod pool_interceptor;

mod converter_helper;
mod identifier_converter;

use arcstr::ArcStr;

pub use converter_helper::ConverterHelper;
pub use identifier_converter::rename;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IdentifierKind {
    Class,
    Field,
    Method,
}

/// The naming callback used both by IdentifierConverter and InnerClasses.
pub trait IdentifierRenamer {
    fn to_be_renamed(
        &mut self,
        kind: IdentifierKind,
        class_name: &str,
        element: Option<&str>,
        descriptor: Option<&str>,
    ) -> bool;

    fn next_class_name(&mut self, name: &str, simple: Option<&str>) -> String;
    fn next_field_name(&mut self, class: &str, field: &str, descriptor: &str) -> String;
    fn next_method_name(&mut self, class: &str, method: &str, descriptor: &str) -> String;
}

/// Reuse the converter's callback for the simple name recorded in an
/// InnerClasses entry. The class tree caches replacements by internal name.
pub fn rename_inner_class(
    helper: &mut dyn IdentifierRenamer,
    name: &str,
    simple: &str,
) -> Option<ArcStr> {
    helper
        .to_be_renamed(IdentifierKind::Class, simple, None, None)
        .then(|| helper.next_class_name(name, Some(simple)).into())
}
