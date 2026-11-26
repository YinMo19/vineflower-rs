// Copyright 2000-2025 Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Name resolution in Vineflower's Kotlin JVM string table.

use super::proto::jvm::{StringTableTypes, string_table_types::record::Operation};
use crate::util::java_str::JavaString;

#[derive(Debug, Clone)]
pub struct NameResolver {
    types: StringTableTypes,
    strings: Vec<JavaString>,
    /// End of each record's run in the expanded Java list.
    record_ends: Vec<usize>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, thiserror::Error)]
pub enum ResolveError {
    #[error("no Kotlin JVM string-table record at index {0}")]
    MissingRecord(i32),
    #[error("no Kotlin d2 string at index {0}")]
    MissingString(i32),
    #[error(
        "Vineflower cannot decode the literal Kotlin JVM string-table record at index {0}: Code"
    )]
    LiteralRecord(i32),
    #[error("Kotlin JVM string-table substring is missing replacement operands at index {0}")]
    MissingSubstringOperands(i32),
}

impl NameResolver {
    pub fn new(types: StringTableTypes, strings: Vec<JavaString>) -> Self {
        let mut end = 0usize;
        let record_ends = types
            .record
            .iter()
            .map(|record| {
                end = end.saturating_add(usize::try_from(record.range()).unwrap_or(0));
                end
            })
            .collect();
        Self {
            types,
            strings,
            record_ends,
        }
    }

    pub fn string_table(&self) -> &StringTableTypes {
        &self.types
    }

    pub fn strings(&self) -> &[JavaString] {
        &self.strings
    }

    pub fn resolve(&self, index: i32) -> Result<JavaString, ResolveError> {
        let i = usize::try_from(index).map_err(|_| ResolveError::MissingRecord(index))?;
        let ordinal = self.record_ends.partition_point(|&end| end <= i);
        let record = self
            .types
            .record
            .get(ordinal)
            .ok_or(ResolveError::MissingRecord(index))?;
        // The bundled 1.12.0 metadata.jar uses "Code" as the charset
        // in ByteString.toStringUtf8. Every explicit literal fails there.
        if record.string.is_some() {
            return Err(ResolveError::LiteralRecord(index));
        }
        let string = if let Some(predefined) = record
            .predefined_index
            .and_then(|index| usize::try_from(index).ok())
            .and_then(|i| PREDEFINED.get(i))
        {
            JavaString::from(*predefined)
        } else {
            self.strings
                .get(i)
                .cloned()
                .ok_or(ResolveError::MissingString(index))?
        };

        let substring = record.substring_index.len() >= 2;
        let replacement = record.replace_char.len() >= 2;
        let operation = record.operation();
        if !substring && !replacement && operation == Operation::None {
            return Ok(string);
        }

        let mut units: Vec<_> = string.utf16().collect();
        if substring {
            // Vineflower tests substring_index, then reads the bounds from
            // replace_char. Keep that distinction when the lists disagree.
            let &[begin, end, ..] = record.replace_char.as_slice() else {
                return Err(ResolveError::MissingSubstringOperands(index));
            };
            if 0 <= begin && begin <= end && end as usize <= units.len() {
                units.copy_within(begin as usize..end as usize, 0);
                units.truncate((end - begin) as usize);
            }
        }
        if let &[from, to, ..] = record.replace_char.as_slice()
            && 0 <= from
            && from <= to
            && to <= i32::from(u16::MAX)
        {
            replace(&mut units, from as u16, to as u16);
        }
        if operation == Operation::DescToClassId && units.len() >= 2 {
            units.remove(0);
            units.pop();
        }
        if matches!(
            operation,
            Operation::InternalToClassId | Operation::DescToClassId
        ) {
            replace(&mut units, u16::from(b'$'), u16::from(b'.'));
        }
        Ok(JavaString::from_utf16(units))
    }
}

fn replace(units: &mut [u16], from: u16, to: u16) {
    for unit in units {
        if *unit == from {
            *unit = to;
        }
    }
}

const PREDEFINED: &[&str] = &[
    "kotlin/Any",
    "kotlin/Nothing",
    "kotlin/Unit",
    "kotlin/Throwable",
    "kotlin/Number",
    "kotlin/Byte",
    "kotlin/Double",
    "kotlin/Float",
    "kotlin/Int",
    "kotlin/Long",
    "kotlin/Short",
    "kotlin/Boolean",
    "kotlin/Char",
    "kotlin/CharSequence",
    "kotlin/String",
    "kotlin/Comparable",
    "kotlin/Enum",
    "kotlin/Array",
    "kotlin/ByteArray",
    "kotlin/DoubleArray",
    "kotlin/FloatArray",
    "kotlin/IntArray",
    "kotlin/LongArray",
    "kotlin/ShortArray",
    "kotlin/BooleanArray",
    "kotlin/CharArray",
    "kotlin/Cloneable",
    "kotlin/Annotation",
    "kotlin/collections/Iterable",
    "kotlin/collections/MutableIterable",
    "kotlin/collections/Collection",
    "kotlin/collections/MutableCollection",
    "kotlin/collections/List",
    "kotlin/collections/MutableList",
    "kotlin/collections/Set",
    "kotlin/collections/MutableSet",
    "kotlin/collections/Map",
    "kotlin/collections/MutableMap",
    "kotlin/collections/Map.Entry",
    "kotlin/collections/MutableMap.MutableEntry",
    "kotlin/collections/Iterator",
    "kotlin/collections/MutableIterator",
    "kotlin/collections/ListIterator",
    "kotlin/collections/MutableListIterator",
];
