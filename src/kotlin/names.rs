// Copyright 2010-2025 JetBrains s.r.o. and Kotlin Programming Language contributors.
// Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::{borrow::Cow, collections::HashSet};

use super::{ClassName, KotlinError, Type, proto};

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

pub(super) struct Names<'a> {
    strings: Vec<&'a str>,
    records: Vec<(usize, proto::StringRecord)>,
    locals: HashSet<i32>,
}

impl<'a> Names<'a> {
    pub fn new(table: proto::StringTableTypes, strings: Vec<&'a str>) -> Result<Self, KotlinError> {
        let mut end = 0usize;
        let records = table
            .records
            .into_iter()
            .map(|record| {
                let range = usize::try_from(record.range.unwrap_or(1))
                    .ok()
                    .filter(|&n| n != 0)
                    .ok_or(KotlinError::Metadata("invalid string record range"))?;
                end = end
                    .checked_add(range)
                    .ok_or(KotlinError::Metadata("string table overflow"))?;
                Ok((end, record))
            })
            .collect::<Result<Vec<_>, KotlinError>>()?;
        if table
            .local_names
            .iter()
            .any(|&n| usize::try_from(n).map_or(true, |n| n >= end))
        {
            return Err(KotlinError::Metadata(
                "local class name outside string table",
            ));
        }
        Ok(Self {
            strings,
            records,
            locals: table.local_names.into_iter().collect(),
        })
    }

    pub fn text(&self, index: i32) -> Result<Cow<'_, str>, KotlinError> {
        let index =
            usize::try_from(index).map_err(|_| KotlinError::Metadata("negative string index"))?;
        let (_, record) = self
            .records
            .get(self.records.partition_point(|(end, _)| *end <= index))
            .ok_or(KotlinError::Metadata(
                "string index outside Kotlin string table",
            ))?;
        let mut text = Cow::Borrowed(
            record
                .string
                .as_deref()
                .or_else(|| {
                    record
                        .predefined_index
                        .and_then(|index| usize::try_from(index).ok())
                        .and_then(|index| PREDEFINED.get(index).copied())
                })
                .or_else(|| self.strings.get(index).copied())
                .ok_or(KotlinError::Metadata("string table record has no string"))?,
        );

        // Substring indices count JVM UTF-16 code units, not UTF-8 bytes or code points.
        if let [start, end, ..] = record.substring[..] {
            let start = utf16_offset(&text, start)?;
            let end = utf16_offset(&text, end)?;
            if start > end {
                return Err(KotlinError::Metadata("reversed string-table slice"));
            }
            text = match text {
                Cow::Borrowed(text) => Cow::Borrowed(&text[start..end]),
                Cow::Owned(mut text) => {
                    text.truncate(end);
                    text.drain(..start);
                    Cow::Owned(text)
                }
            };
        }
        if let [from, to, ..] = record.replace[..] {
            let from = u16::try_from(from)
                .map_err(|_| KotlinError::Metadata("invalid string-table replacement"))?;
            let to = u16::try_from(to)
                .map_err(|_| KotlinError::Metadata("invalid string-table replacement"))?;
            if from != to {
                if let (Some(from), Some(to)) =
                    (char::from_u32(from.into()), char::from_u32(to.into()))
                {
                    if text.contains(from) {
                        let mut encoded = [0; 4];
                        text = Cow::Owned(text.replace(from, &*to.encode_utf8(&mut encoded)));
                    }
                } else {
                    text = Cow::Owned(
                        String::from_utf16(
                            &text
                                .encode_utf16()
                                .map(|unit| if unit == from { to } else { unit })
                                .collect::<Vec<_>>(),
                        )
                        .map_err(|_| KotlinError::Metadata("invalid UTF-16 in resolved string"))?,
                    );
                }
            }
        }
        match record.operation.unwrap_or(0) {
            0 => Ok(text),
            1 => Ok(replace_nested(text)),
            2 => {
                let stripped = text
                    .strip_prefix('L')
                    .and_then(|text| text.strip_suffix(';'))
                    .ok_or(KotlinError::Metadata("invalid descriptor in name table"))?;
                Ok(Cow::Owned(stripped.replace('$', ".")))
            }
            _ => Err(KotlinError::Metadata("unknown string table operation")),
        }
    }

    pub fn class(&self, index: i32) -> Result<ClassName, KotlinError> {
        let id = self.text(index)?.into_owned();
        if id.split(['/', '.']).any(str::is_empty) {
            return Err(KotlinError::Metadata("empty component in class ID"));
        }
        Ok(ClassName {
            id,
            local: self.locals.contains(&index),
        })
    }
}

fn replace_nested(text: Cow<'_, str>) -> Cow<'_, str> {
    if text.contains('$') {
        Cow::Owned(text.replace('$', "."))
    } else {
        text
    }
}

fn utf16_offset(text: &str, offset: i32) -> Result<usize, KotlinError> {
    let mut remaining = usize::try_from(offset)
        .map_err(|_| KotlinError::Metadata("negative string-table slice"))?;
    for (byte, character) in text.char_indices() {
        if remaining == 0 {
            return Ok(byte);
        }
        let Some(next) = remaining.checked_sub(character.len_utf16()) else {
            break;
        };
        remaining = next;
    }
    if remaining == 0 {
        Ok(text.len())
    } else {
        Err(KotlinError::Metadata("invalid UTF-16 string-table slice"))
    }
}

/// The compiler's ClassMapperLite fallback, used only when the writer omitted
/// a JVM descriptor from the wire. Do not substitute general JVM type erasure.
pub(super) fn default_descriptor(ty: &Type) -> Option<Cow<'static, str>> {
    let id = ty.class_id()?;
    let descriptor = match id {
        "kotlin/Boolean" => "Z",
        "kotlin/Byte" => "B",
        "kotlin/Char" => "C",
        "kotlin/Short" => "S",
        "kotlin/Int" => "I",
        "kotlin/Long" => "J",
        "kotlin/Float" => "F",
        "kotlin/Double" => "D",
        "kotlin/BooleanArray" => "[Z",
        "kotlin/ByteArray" => "[B",
        "kotlin/CharArray" => "[C",
        "kotlin/ShortArray" => "[S",
        "kotlin/IntArray" => "[I",
        "kotlin/LongArray" => "[J",
        "kotlin/FloatArray" => "[F",
        "kotlin/DoubleArray" => "[D",
        "kotlin/Unit" => "V",
        "kotlin/Any" => "Ljava/lang/Object;",
        "kotlin/Nothing" => "Ljava/lang/Void;",
        "kotlin/Annotation" => "Ljava/lang/annotation/Annotation;",
        "kotlin/collections/Map.Entry" | "kotlin/collections/MutableMap.MutableEntry" => {
            "Ljava/util/Map$Entry;"
        }
        _ => {
            if let Some(simple) = id.strip_prefix("kotlin/") {
                if matches!(
                    simple,
                    "String"
                        | "CharSequence"
                        | "Throwable"
                        | "Cloneable"
                        | "Number"
                        | "Comparable"
                        | "Enum"
                ) {
                    return Some(Cow::Owned(format!("Ljava/lang/{simple};")));
                }
                if let Some(collection) = simple.strip_prefix("collections/") {
                    let collection = collection.strip_prefix("Mutable").unwrap_or(collection);
                    if collection == "Iterable" {
                        return Some(Cow::Borrowed("Ljava/lang/Iterable;"));
                    }
                    if matches!(
                        collection,
                        "Iterator" | "Collection" | "List" | "Set" | "Map" | "ListIterator"
                    ) {
                        return Some(Cow::Owned(format!("Ljava/util/{collection};")));
                    }
                }
                if let Some(arity) = simple.strip_prefix("Function").and_then(arity) {
                    return Some(Cow::Owned(format!(
                        "Lkotlin/jvm/functions/Function{arity};"
                    )));
                }
                if simple
                    .strip_prefix("reflect/KFunction")
                    .and_then(arity)
                    .is_some()
                {
                    return Some(Cow::Borrowed("Lkotlin/reflect/KFunction;"));
                }
                if let Some(base) = simple.strip_suffix(".Companion").filter(|base| {
                    matches!(
                        *base,
                        "Char"
                            | "Byte"
                            | "Short"
                            | "Int"
                            | "Float"
                            | "Long"
                            | "Double"
                            | "String"
                            | "Enum"
                    )
                }) {
                    return Some(Cow::Owned(format!(
                        "Lkotlin/jvm/internal/{base}CompanionObject;"
                    )));
                }
            }
            return Some(Cow::Owned(format!("L{};", id.replace('.', "$"))));
        }
    };
    Some(Cow::Borrowed(descriptor))
}

fn arity(text: &str) -> Option<u8> {
    let number = text.parse::<u8>().ok()?;
    (number <= 22 && (text == "0" || !text.starts_with(['0', '+']))).then_some(number)
}
