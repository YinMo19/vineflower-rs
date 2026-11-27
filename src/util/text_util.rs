//! `util.TextUtil`: identifier checks and other small text helpers.

use std::borrow::Cow;

use unicode_general_category::{GeneralCategory, get_general_category};

use crate::code::BytecodeVersion;
use crate::code::code_constants::ACC_STATIC;
use crate::engine::Cx;
use crate::structs::{StructMember, StructMethod};

pub fn get_indent_string(cx: &Cx, length: i32) -> String {
    cx.options.indent_string.repeat(length.max(0) as usize)
}

/// `Character.getType` of a UTF-16 unit; a surrogate has no `char`.
fn category(unit: u16) -> Option<GeneralCategory> {
    char::from_u32(u32::from(unit)).map(get_general_category)
}

/// `isPrintableUnicode(char)`, for one UTF-16 unit.
pub fn is_printable_unicode(unit: u16) -> bool {
    use GeneralCategory::*;
    category(unit).is_some_and(|category| {
        !matches!(
            category,
            Unassigned | LineSeparator | ParagraphSeparator | Control | Format | PrivateUse
        )
    })
}

pub fn char_to_unicode_literal(value: i32) -> String {
    let hex = format!("{value:x}");
    let padded = format!("0000{hex}");
    format!("\\u{}", &padded[hex.len()..])
}

pub fn is_valid_identifier(id: &str, version: BytecodeVersion, mt: &StructMethod) -> bool {
    is_java_identifier(id) && !is_keyword(id, version, mt)
}

pub(crate) fn is_java_identifier(id: &str) -> bool {
    let mut units = id.encode_utf16();
    units.next().is_some_and(is_java_identifier_start) && units.all(is_java_identifier_part)
}

/// `ClassWriter.toValidJavaIdentifier`: replace each invalid UTF-16 unit.
pub fn to_valid_java_identifier(name: &str) -> Cow<'_, str> {
    if name.is_empty() || is_java_identifier(name) {
        return Cow::Borrowed(name);
    }
    let units: Vec<_> = name
        .encode_utf16()
        .enumerate()
        .map(|(index, unit)| {
            let valid = if index == 0 {
                is_java_identifier_start(unit)
            } else {
                is_java_identifier_part(unit)
            };
            if valid { unit } else { u16::from(b'_') }
        })
        .collect();
    Cow::Owned(String::from_utf16(&units).unwrap())
}

/// `Character.isJavaIdentifierStart(char)`.
pub(crate) fn is_java_identifier_start(unit: u16) -> bool {
    use GeneralCategory::*;
    category(unit).is_some_and(|category| {
        matches!(
            category,
            UppercaseLetter
                | LowercaseLetter
                | TitlecaseLetter
                | ModifierLetter
                | OtherLetter
                | LetterNumber
                | CurrencySymbol
                | ConnectorPunctuation
        )
    })
}

/// `Character.isJavaIdentifierPart(char)`.
pub(crate) fn is_java_identifier_part(unit: u16) -> bool {
    use GeneralCategory::*;
    is_java_identifier_start(unit)
        || is_java_identifier_ignorable(unit)
        || category(unit).is_some_and(|category| {
            matches!(category, DecimalNumber | SpacingMark | NonspacingMark)
        })
}

pub(crate) fn is_java_identifier_ignorable(unit: u16) -> bool {
    matches!(unit, 0x00..=0x08 | 0x0E..=0x1B | 0x7F..=0x9F)
        || category(unit) == Some(GeneralCategory::Format)
}

pub fn is_keyword(id: &str, version: BytecodeVersion, mt: &StructMethod) -> bool {
    is_reserved_word(id)
        || version.has_enums() && id == "enum"
        || mt.has_modifier(ACC_STATIC) && id == "this"
}

pub(crate) fn is_reserved_word(id: &str) -> bool {
    matches!(
        id,
        "abstract"
            | "default"
            | "if"
            | "private"
            | "this"
            | "boolean"
            | "do"
            | "implements"
            | "protected"
            | "throw"
            | "break"
            | "double"
            | "import"
            | "public"
            | "throws"
            | "byte"
            | "else"
            | "instanceof"
            | "return"
            | "transient"
            | "case"
            | "extends"
            | "int"
            | "short"
            | "try"
            | "catch"
            | "final"
            | "interface"
            | "static"
            | "void"
            | "char"
            | "finally"
            | "long"
            | "strictfp"
            | "volatile"
            | "class"
            | "float"
            | "native"
            | "super"
            | "while"
            | "const"
            | "for"
            | "new"
            | "switch"
            | "continue"
            | "goto"
            | "package"
            | "synchronized"
            | "true"
            | "false"
            | "null"
            | "assert"
    )
}

pub fn get_instruction_name(opcode: i32) -> &'static str {
    OPCODE_NAMES[opcode as usize]
}

#[rustfmt::skip]
const OPCODE_NAMES: [&str; 202] = [
    "nop", "aconst_null", "iconst_m1", "iconst_0", "iconst_1", "iconst_2", "iconst_3", "iconst_4",
    "iconst_5", "lconst_0", "lconst_1", "fconst_0", "fconst_1", "fconst_2", "dconst_0", "dconst_1",
    "bipush", "sipush", "ldc", "ldc_w", "ldc2_w", "iload", "lload", "fload", "dload", "aload",
    "iload_0", "iload_1", "iload_2", "iload_3", "lload_0", "lload_1", "lload_2", "lload_3",
    "fload_0", "fload_1", "fload_2", "fload_3", "dload_0", "dload_1", "dload_2", "dload_3",
    "aload_0", "aload_1", "aload_2", "aload_3", "iaload", "laload", "faload", "daload", "aaload",
    "baload", "caload", "saload", "istore", "lstore", "fstore", "dstore", "astore", "istore_0",
    "istore_1", "istore_2", "istore_3", "lstore_0", "lstore_1", "lstore_2", "lstore_3",
    "fstore_0", "fstore_1", "fstore_2", "fstore_3", "dstore_0", "dstore_1", "dstore_2",
    "dstore_3", "astore_0", "astore_1", "astore_2", "astore_3", "iastore", "lastore", "fastore",
    "dastore", "aastore", "bastore", "castore", "sastore", "pop", "pop2", "dup", "dup_x1",
    "dup_x2", "dup2", "dup2_x1", "dup2_x2", "swap", "iadd", "ladd", "fadd", "dadd", "isub",
    "lsub", "fsub", "dsub", "imul", "lmul", "fmul", "dmul", "idiv", "ldiv", "fdiv", "ddiv",
    "irem", "lrem", "frem", "drem", "ineg", "lneg", "fneg", "dneg", "ishl", "lshl", "ishr",
    "lshr", "iushr", "lushr", "iand", "land", "ior", "lor", "ixor", "lxor", "iinc", "i2l", "i2f",
    "i2d", "l2i", "l2f", "l2d", "f2i", "f2l", "f2d", "d2i", "d2l", "d2f", "i2b", "i2c", "i2s",
    "lcmp", "fcmpl", "fcmpg", "dcmpl", "dcmpg", "ifeq", "ifne", "iflt", "ifge", "ifgt", "ifle",
    "if_icmpeq", "if_icmpne", "if_icmplt", "if_icmpge", "if_icmpgt", "if_icmple", "if_acmpeq",
    "if_acmpne", "goto", "jsr", "ret", "tableswitch", "lookupswitch", "ireturn", "lreturn",
    "freturn", "dreturn", "areturn", "return", "getstatic", "putstatic", "getfield", "putfield",
    "invokevirtual", "invokespecial", "invokestatic", "invokeinterface",
    "invokedynamic", // since Java 7
    "new", "newarray", "anewarray", "arraylength", "athrow", "checkcast", "instanceof",
    "monitorenter", "monitorexit", "wide", "multianewarray", "ifnull", "ifnonnull", "goto_w",
    "jsr_w",
];
