// Copyright 2000-2017 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.
// Tiny naming follows Vineflower's TinyNameProvider, adapted there from FabricMC's tiny-remapper.

use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
    fmt::Write,
};

use crate::descriptor::{Primitive, Type};

use super::identifiers::local_keyword;

#[cfg(test)]
mod tests;

/// Built-in Vineflower variable-renaming providers.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum VariableRenamer {
    Jad,
    Tiny,
}

impl VariableRenamer {
    /// An explicitly set name takes precedence over the legacy JAD option,
    /// including when it is empty or does not name a registered provider.
    pub fn select(explicit: Option<&str>, legacy_jad: bool) -> Option<Self> {
        match explicit {
            Some("jad") => Some(Self::Jad),
            Some("tiny") => Some(Self::Tiny),
            None if legacy_jad => Some(Self::Jad),
            _ => None,
        }
    }

    /// Creates isolated per-method naming state. The old parameter option
    /// applies to JAD only; it does not independently select a provider.
    pub fn for_method(
        self,
        rename_parameters: bool,
        legacy_jad_parameters: bool,
        major_version: u16,
    ) -> VariableNamer {
        VariableNamer {
            provider: match self {
                Self::Jad => Provider::Jad(Jad::default()),
                Self::Tiny => Provider::Tiny(Tiny::default()),
            },
            rename_parameters: rename_parameters || (self == Self::Jad && legacy_jad_parameters),
            major_version,
            parameters: HashMap::new(),
        }
    }
}

/// An SSA variable at the naming boundary. `cast_name` can supply a generic
/// source type or a class-context-aware spelling; otherwise the JVM type is used.
#[derive(Clone, Copy, Debug)]
pub struct VariableBinding<'a> {
    pub index: u16,
    pub version: u32,
    pub ty: &'a Type,
    pub cast_name: Option<&'a str>,
}

/// Per-method provider state. Proposed names still need to be checked against
/// names reserved by the enclosing source scope, such as fields and temporaries.
#[derive(Clone, Debug)]
pub struct VariableNamer {
    provider: Provider,
    rename_parameters: bool,
    major_version: u16,
    parameters: HashMap<u16, String>,
}

impl VariableNamer {
    /// Picks a name for a newly defined local binding (not each assignment).
    pub fn rename_local(&mut self, ty: &Type, cast_name: Option<&str>) -> Option<String> {
        match &mut self.provider {
            Provider::Jad(jad) => {
                let cast = cast_name.map_or_else(|| default_cast(ty, true), Cow::Borrowed);
                let cast = clean_type(&cast);
                (cast != "this").then(|| jad.name(cast))
            }
            Provider::Tiny(tiny) => {
                let cast = cast_name.map_or_else(|| default_cast(ty, false), Cow::Borrowed);
                tiny.name(ty, clean_type(&cast), self.major_version)
            }
        }
    }

    /// Picks (or reuses) the parameter name for a JVM slot, including for
    /// abstract/native methods that have no bytecode variable definitions.
    pub fn rename_parameter(
        &mut self,
        slot: u16,
        ty: &Type,
        cast_name: Option<&str>,
    ) -> Option<String> {
        if !self.rename_parameters {
            return None;
        }
        if let Some(name) = self.parameters.get(&slot) {
            return Some(name.clone());
        }
        let name = self.rename_local(ty, cast_name)?;
        self.parameters.insert(slot, name.clone());
        Some(name)
    }

    pub(crate) fn renames_parameters(&self) -> bool {
        self.rename_parameters
    }

    /// Names a complete set of bindings in Vineflower's index/version order.
    /// `parameter_slots` includes the receiver slot and both slots of wide
    /// parameters. Outputs omit bindings the provider elected not to rename.
    pub fn rename_bindings<'a>(
        &mut self,
        parameter_slots: u16,
        bindings: impl IntoIterator<Item = VariableBinding<'a>>,
    ) -> Vec<((u16, u32), String)> {
        let mut bindings: Vec<_> = bindings.into_iter().collect();
        bindings.sort_unstable_by_key(|binding| (binding.index, binding.version));
        bindings
            .into_iter()
            .filter_map(|binding| {
                let name = if binding.index < parameter_slots {
                    self.rename_parameter(binding.index, binding.ty, binding.cast_name)
                } else {
                    self.rename_local(binding.ty, binding.cast_name)
                }?;
                Some(((binding.index, binding.version), name))
            })
            .collect()
    }

    /// Inherits the enclosing method's provider state for a local class,
    /// anonymous class or lambda, but not its slot-to-parameter assignments.
    pub fn inherit(&mut self, parent: &Self) {
        match (&mut self.provider, &parent.provider) {
            (Provider::Jad(child), Provider::Jad(parent)) => child.clone_from(parent),
            (Provider::Tiny(child), Provider::Tiny(parent)) => {
                for name in &parent.used {
                    if !child.used.contains(name) {
                        child.used.insert(name.clone());
                    }
                }
            }
            _ => {}
        }
    }
}

#[derive(Clone, Debug)]
enum Provider {
    Jad(Jad),
    Tiny(Tiny),
}

fn default_cast(ty: &Type, show_arrays: bool) -> Cow<'_, str> {
    let mut element = ty;
    while let Type::Array(inner) = element {
        element = inner;
    }
    let raw = match element {
        Type::Primitive(primitive) => primitive.java_name(),
        Type::Object(name) => name.rsplit('/').next().unwrap_or(name),
        Type::Void => "void",
        Type::Array(_) => unreachable!(),
    };
    if show_arrays && matches!(ty, Type::Array(_)) {
        // JAD treats every nonzero array rank as one dimension.
        Cow::Owned(format!("{raw}[]"))
    } else {
        Cow::Borrowed(raw)
    }
}

fn clean_type(cast: &str) -> &str {
    let cast = cast.split_once('<').map_or(cast, |(base, _)| base);
    cast.rsplit_once('.').map_or(cast, |(_, leaf)| leaf)
}

#[derive(Clone, Debug, Default)]
struct Jad {
    used_preset: [u32; 16],
    other: HashMap<String, JadStem>,
}

#[derive(Clone, Debug)]
struct JadStem {
    base: String,
    uses: u32,
}

impl Jad {
    fn name(&mut self, cast: &str) -> String {
        let array = single_array(cast);
        if let Some(name) = self.existing(&array) {
            return name;
        }
        let lower = if array.is_ascii() && !array.bytes().any(|ch| ch.is_ascii_uppercase()) {
            array
        } else {
            let folded = array.to_lowercase();
            if let Some(name) = self.existing(&folded) {
                return name;
            }
            Cow::Owned(folded)
        };
        if cast == "long" {
            return self.preset("int").expect("JAD has an int preset");
        }
        if !cast.as_bytes().first().is_some_and(u8::is_ascii_uppercase)
            && !cast.contains('[')
            && !cast.contains("...")
        {
            return lower.into_owned();
        }
        let key = if lower.contains("...") {
            single_array(&lower.replace("...", "[]")).into_owned()
        } else {
            lower.into_owned()
        };
        let base = if key.contains('[') {
            format!("a{}", key.replace("[]", "").replace('.', ""))
        } else {
            key.replace('.', "")
        };
        self.other.insert(
            key,
            JadStem {
                base: base.clone(),
                uses: 1,
            },
        );
        base
    }

    fn existing(&mut self, cast: &str) -> Option<String> {
        if let Some(name) = self.preset(cast) {
            return Some(name);
        }
        let stem = self.other.get_mut(cast)?;
        let id = stem.uses;
        stem.uses += 1;
        Some(format!("{}{id}", stem.base))
    }

    fn preset(&mut self, cast: &str) -> Option<String> {
        let (index, first, skip_zero, names): (_, _, _, &[_]) = match cast {
            "int" => (0, 0, true, &["i", "j", "k", "l"]),
            "byte" => (1, 0, false, &["b"]),
            "char" => (2, 0, false, &["c"]),
            "short" => (3, 1, false, &["short"]),
            "boolean" => (4, 0, true, &["flag"]),
            "double" => (5, 0, false, &["d"]),
            "float" => (6, 0, true, &["f"]),
            "File" => (7, 1, true, &["file"]),
            "String" => (8, 0, true, &["s"]),
            "Class" => (9, 0, true, &["oclass"]),
            "Long" => (10, 0, true, &["olong"]),
            "Byte" => (11, 0, true, &["obyte"]),
            "Short" => (12, 0, true, &["oshort"]),
            "Boolean" => (13, 0, true, &["obool"]),
            "Package" => (14, 0, true, &["opackage"]),
            "Enum" => (15, 0, true, &["oenum"]),
            _ => return None,
        };
        let next = &mut self.used_preset[index];
        let id = (first + *next) as usize;
        *next += 1;
        let name = names[id % names.len()];
        let suffix = id / names.len();
        Some(if suffix == 0 && skip_zero {
            name.into()
        } else {
            format!("{name}{suffix}")
        })
    }
}

fn single_array(cast: &str) -> Cow<'_, str> {
    if !cast.contains("[][]") {
        return Cow::Borrowed(cast);
    }
    let mut result = cast.replace("[][]", "[]");
    while result.contains("[][]") {
        result = result.replace("[][]", "[]");
    }
    Cow::Owned(result)
}

#[derive(Clone, Debug, Default)]
struct Tiny {
    used: HashSet<String>,
    letter_next: [usize; 7],
    number_next: HashMap<String, usize>,
}

impl Tiny {
    fn name(&mut self, ty: &Type, cast: &str, major: u16) -> Option<String> {
        let cast = cast.rsplit_once('$').map_or(cast, |(_, leaf)| leaf);
        let cast = cast.trim_end_matches("[]");
        let cast = if cast.contains("[]") {
            Cow::Owned(cast.replace("[]", ""))
        } else {
            Cow::Borrowed(cast)
        };
        let mut element = ty;
        while let Type::Array(inner) = element {
            element = inner;
        }
        if !self.used.contains(cast.as_ref()) {
            self.used.insert(cast.as_ref().into());
        }
        use Primitive::*;
        let mut name = match element {
            Type::Primitive(Byte) => self.letter(0, b'b', major),
            Type::Primitive(Char) => self.letter(1, b'c', major),
            Type::Primitive(Double) => self.letter(2, b'd', major),
            Type::Primitive(Float) => self.letter(3, b'f', major),
            Type::Primitive(Int) => self.letter(4, b'i', major),
            Type::Primitive(Long) => self.letter(5, b'l', major),
            Type::Primitive(Short) => self.letter(6, b's', major),
            Type::Primitive(Boolean) => self.numbered("bl".into()),
            Type::Object(_) => {
                let first = cast.chars().next()?;
                let plural = matches!(ty, Type::Array(_)) && !cast.ends_with('s');
                // Character.toLowerCase(char) performs the simple mapping.
                let lower = if first.len_utf16() == 1 && first.is_uppercase() {
                    first.to_lowercase().next().unwrap()
                } else {
                    first
                };
                let rest = &cast[first.len_utf8()..];
                let mut base =
                    String::with_capacity(rest.len() + lower.len_utf8() + usize::from(plural));
                base.push(lower);
                base.push_str(rest);
                if plural {
                    base.push('s');
                }
                self.numbered(base)
            }
            Type::Void => return None,
            Type::Array(_) => unreachable!(),
        };
        if local_keyword(&name, major) {
            name.push('_');
        }
        self.used.insert(name.clone());
        Some(name)
    }

    fn letter(&mut self, cursor: usize, start: u8, major: u16) -> String {
        let next = &mut self.letter_next[cursor];
        *next = (*next).max(usize::from(start - b'a'));
        let mut digits = [0; usize::BITS as usize / 4 + 1];
        loop {
            let name = tiny_letters(*next, &mut digits);
            if !self.used.contains(name) {
                // Only the post-escaped spelling is reserved for a keyword.
                *next += usize::from(!local_keyword(name, major));
                return name.into();
            }
            *next += 1;
        }
    }

    fn numbered(&mut self, base: String) -> String {
        if !self.used.contains(&base) {
            return base;
        }
        let mut suffix = self.number_next.get(&base).copied().unwrap_or(1);
        let mut name = base.clone();
        loop {
            write!(name, "{suffix}").unwrap();
            suffix += 1;
            if !self.used.contains(&name) {
                self.number_next.insert(base, suffix);
                return name;
            }
            name.truncate(base.len());
        }
    }
}

fn tiny_letters(mut index: usize, buf: &mut [u8]) -> &str {
    // Base 26 with digits a-z, so the sequence proceeds from z to ba, not aa.
    let mut pos = buf.len();
    loop {
        pos -= 1;
        buf[pos] = b'a' + (index % 26) as u8;
        index /= 26;
        if index == 0 {
            return std::str::from_utf8(&buf[pos..]).unwrap();
        }
    }
}
