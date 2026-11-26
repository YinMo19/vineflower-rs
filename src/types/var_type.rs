// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `struct.gen.VarType` with `CodeType` and `TypeFamily`: the type of a
//! value, and the lattice the type inference works on.
//!
//! Upstream's subclass `GenericType` is folded into [`VarType`]: a type whose
//! Java object would be a `GenericType` carries [`GenericType`] data (see
//! `generic_type.rs` for its methods). As upstream, equality and hashing look
//! only at the kind, the array dimension and the name, never at type
//! arguments; [`VarType::same`] stands in for reference identity.

use std::fmt;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use arcstr::{ArcStr, literal};

use super::generic_type::{GenericType, should_check_generic_base};
use crate::engine::Cx;
use crate::util::jhash::JavaHash;
use crate::util::java_str::utf16_len;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CodeType {
    Byte,
    Char,
    Double,
    Float,
    Int,
    Long,
    Short,
    Boolean,
    Object,
    Address,
    Void,
    Any,
    Group2empty,
    Null,
    Notinitialized,
    Bytechar,
    Shortchar,
    Unknown,
    Genvar,
}

impl CodeType {
    pub fn ordinal(self) -> i32 {
        self as i32
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum TypeFamily {
    Unknown,
    Boolean,
    Integer,
    Float,
    Long,
    Double,
    Object,
}

impl TypeFamily {
    pub fn is_numeric(self) -> bool {
        matches!(
            self,
            Self::Integer | Self::Float | Self::Long | Self::Double
        )
    }

    pub fn int_or_bool(self) -> bool {
        matches!(self, Self::Integer | Self::Boolean)
    }

    // TODO: document what these mean, and try to remove! Doesn't make sense to have these
    pub fn is_greater(self, other: TypeFamily) -> bool {
        self > other
    }

    pub fn is_lesser(self, other: TypeFamily) -> bool {
        self < other
    }
}

#[derive(Clone, Debug)]
pub struct VarType {
    pub ty: CodeType,
    pub array_dim: i32,
    /// The internal class name of an object type, the name of a type
    /// variable, or the descriptor character of any other type. Only the
    /// null type has none.
    pub value: Option<ArcStr>,
    pub type_family: TypeFamily,
    pub stack_size: i32,
    /// Present exactly when the Java object would be a `GenericType`.
    pub(super) generic: Option<Arc<GenericType>>,
}

macro_rules! basic_type {
    ($ty:ident, $value:literal) => {
        VarType::constant(CodeType::$ty, Some(literal!($value)))
    };
}

macro_rules! object_type {
    ($name:literal) => {
        VarType::constant(CodeType::Object, Some(literal!($name)))
    };
}

impl VarType {
    pub const VARTYPE_UNKNOWN: VarType = basic_type!(Unknown, "U");
    pub const VARTYPE_INT: VarType = basic_type!(Int, "I");
    pub const VARTYPE_FLOAT: VarType = basic_type!(Float, "F");
    pub const VARTYPE_LONG: VarType = basic_type!(Long, "J");
    pub const VARTYPE_DOUBLE: VarType = basic_type!(Double, "D");
    pub const VARTYPE_BYTE: VarType = basic_type!(Byte, "B");
    pub const VARTYPE_CHAR: VarType = basic_type!(Char, "C");
    pub const VARTYPE_SHORT: VarType = basic_type!(Short, "S");
    pub const VARTYPE_BOOLEAN: VarType = basic_type!(Boolean, "Z");
    pub const VARTYPE_BYTECHAR: VarType = basic_type!(Bytechar, "X");
    pub const VARTYPE_SHORTCHAR: VarType = basic_type!(Shortchar, "Y");
    pub const VARTYPE_NULL: VarType = VarType::constant(CodeType::Null, None);
    pub const VARTYPE_STRING: VarType = object_type!("java/lang/String");
    pub const VARTYPE_CLASS: VarType = object_type!("java/lang/Class");
    pub const VARTYPE_OBJECT: VarType = object_type!("java/lang/Object");
    pub const VARTYPE_INTEGER: VarType = object_type!("java/lang/Integer");
    pub const VARTYPE_CHARACTER: VarType = object_type!("java/lang/Character");
    pub const VARTYPE_BYTE_OBJ: VarType = object_type!("java/lang/Byte");
    pub const VARTYPE_SHORT_OBJ: VarType = object_type!("java/lang/Short");
    pub const VARTYPE_BOOLEAN_OBJ: VarType = object_type!("java/lang/Boolean");
    pub const VARTYPE_FLOAT_OBJ: VarType = object_type!("java/lang/Float");
    pub const VARTYPE_DOUBLE_OBJ: VarType = object_type!("java/lang/Double");
    pub const VARTYPE_LONG_OBJ: VarType = object_type!("java/lang/Long");
    pub const VARTYPE_VOID: VarType = basic_type!(Void, "V");
    pub const VARTYPE_METHODTYPE: VarType = object_type!("java/lang/invoke/MethodType");

    const fn constant(ty: CodeType, value: Option<ArcStr>) -> VarType {
        VarType {
            ty,
            array_dim: 0,
            value,
            type_family: Self::get_family(ty, 0),
            stack_size: Self::get_stack_size(ty, 0),
            generic: None,
        }
    }

    /// `new VarType(type)`.
    pub fn new(ty: CodeType) -> VarType {
        Self::with_dim(ty, 0)
    }

    /// `new VarType(type, arrayDim)`.
    pub fn with_dim(ty: CodeType, array_dim: i32) -> VarType {
        Self::raw(ty, array_dim, Self::get_char(ty))
    }

    /// `new VarType(type, arrayDim, value)`.
    pub fn with_value(ty: CodeType, array_dim: i32, value: impl Into<ArcStr>) -> VarType {
        Self::raw(ty, array_dim, Some(value.into()))
    }

    pub(super) fn raw(ty: CodeType, array_dim: i32, value: Option<ArcStr>) -> VarType {
        VarType {
            ty,
            array_dim,
            value,
            type_family: Self::get_family(ty, array_dim),
            stack_size: Self::get_stack_size(ty, array_dim),
            generic: None,
        }
    }

    /// `new VarType(signature)`: the type a field descriptor denotes.
    pub fn from_signature(signature: &str) -> VarType {
        Self::from_signature_cl(signature, false)
    }

    /// `new VarType(signature, clType)`: with `cl_type`, a signature that
    /// does not start an array is a class name.
    pub fn from_signature_cl(signature: &str, cl_type: bool) -> VarType {
        let mut ty = CodeType::Byte; // TODO: should be null!
        let mut array_dim = 0;
        let mut value = None;

        for (i, c) in signature.char_indices() {
            match c {
                '[' => array_dim += 1,
                'L' if signature.ends_with(';') => {
                    ty = CodeType::Object;
                    value = Some(&signature[i + 1..signature.len() - 1]);
                    break;
                }
                _ => {
                    let rest = &signature[i..];
                    ty = if (cl_type && i == 0) || utf16_len(rest) > 1 {
                        CodeType::Object
                    } else {
                        Self::get_type(c)
                    };
                    value = Some(rest);
                    break;
                }
            }
        }

        Self::raw(ty, array_dim, value.map(ArcStr::from))
    }

    pub fn get_char(ty: CodeType) -> Option<ArcStr> {
        Some(match ty {
            CodeType::Byte => literal!("B"),
            CodeType::Char => literal!("C"),
            CodeType::Double => literal!("D"),
            CodeType::Float => literal!("F"),
            CodeType::Int => literal!("I"),
            CodeType::Long => literal!("J"),
            CodeType::Short => literal!("S"),
            CodeType::Boolean => literal!("Z"),
            CodeType::Void => literal!("V"),
            CodeType::Group2empty => literal!("G"),
            CodeType::Notinitialized => literal!("N"),
            CodeType::Address => literal!("A"),
            CodeType::Bytechar => literal!("X"),
            CodeType::Shortchar => literal!("Y"),
            CodeType::Unknown => literal!("U"),
            CodeType::Null | CodeType::Object => return None,
            CodeType::Any | CodeType::Genvar => panic!("Invalid type"),
        })
    }

    pub(super) const fn get_stack_size(ty: CodeType, array_dim: i32) -> i32 {
        if array_dim > 0 {
            return 1;
        }
        match ty {
            CodeType::Double | CodeType::Long => 2,
            CodeType::Void | CodeType::Group2empty => 0,
            _ => 1,
        }
    }

    pub(super) const fn get_family(ty: CodeType, array_dim: i32) -> TypeFamily {
        if array_dim > 0 {
            return TypeFamily::Object;
        }
        match ty {
            CodeType::Byte
            | CodeType::Bytechar
            | CodeType::Shortchar
            | CodeType::Char
            | CodeType::Short
            | CodeType::Int => TypeFamily::Integer,
            CodeType::Double => TypeFamily::Double,
            CodeType::Float => TypeFamily::Float,
            CodeType::Long => TypeFamily::Long,
            CodeType::Boolean => TypeFamily::Boolean,
            CodeType::Null | CodeType::Object | CodeType::Genvar => TypeFamily::Object,
            _ => TypeFamily::Unknown,
        }
    }

    pub fn decrease_array_dim(&self) -> VarType {
        if self.generic.is_some() {
            return self.generic_with_dim(self.array_dim - 1);
        }
        if self.array_dim > 0 {
            Self::raw(self.ty, self.array_dim - 1, self.value.clone())
        } else {
            //throw new RuntimeException("array dimension equals 0!"); FIXME: investigate this case
            self.clone()
        }
    }

    /// A plain type keeps the type family and stack size it had before, as
    /// upstream does; a generic one has them recomputed.
    pub fn resize_array_dim(&self, new_array_dim: i32) -> VarType {
        if self.generic.is_some() {
            return self.generic_with_dim(new_array_dim);
        }
        VarType {
            array_dim: new_array_dim,
            ..self.clone()
        }
    }

    /// `new GenericType(type, arrayDim, value, parent, arguments, wildcard)`
    /// with this type's generic data.
    fn generic_with_dim(&self, array_dim: i32) -> VarType {
        VarType {
            array_dim,
            type_family: Self::get_family(self.ty, array_dim),
            stack_size: Self::get_stack_size(self.ty, array_dim),
            ..self.clone()
        }
    }

    /// The name of an object type or type variable. Fails for the null type,
    /// where upstream would dereference `null`.
    pub fn name(&self) -> &str {
        self.value.as_deref().unwrap()
    }

    /// Whether the two are indistinguishable, type arguments included. This
    /// is what the port uses where upstream compares references.
    pub fn same(&self, other: &VarType) -> bool {
        self == other
            && self.type_family == other.type_family
            && self.stack_size == other.stack_size
            && match (&self.generic, &other.generic) {
                (None, None) => true,
                (Some(a), Some(b)) => Arc::ptr_eq(a, b) || a.same(b),
                _ => false,
            }
    }

    pub fn get_type(c: char) -> CodeType {
        Self::try_get_type(c).unwrap_or_else(|| panic!("Invalid type: {c}"))
    }

    pub(super) fn try_get_type(c: char) -> Option<CodeType> {
        Some(match c {
            'B' => CodeType::Byte,
            'C' => CodeType::Char,
            'D' => CodeType::Double,
            'F' => CodeType::Float,
            'I' => CodeType::Int,
            'J' => CodeType::Long,
            'S' => CodeType::Short,
            'Z' => CodeType::Boolean,
            'V' => CodeType::Void,
            'G' => CodeType::Group2empty,
            'N' => CodeType::Notinitialized,
            'A' => CodeType::Address,
            'X' => CodeType::Bytechar,
            'Y' => CodeType::Shortchar,
            'U' => CodeType::Unknown,
            _ => return None,
        })
    }

    /// `UNBOXING_TYPES.get(this)`: the primitive a wrapper class boxes.
    pub fn unboxing_type(&self) -> Option<VarType> {
        if self.ty != CodeType::Object || self.array_dim != 0 {
            return None;
        }
        Some(match self.value.as_deref()? {
            "java/lang/Integer" => Self::VARTYPE_INT,
            "java/lang/Character" => Self::VARTYPE_CHAR,
            "java/lang/Byte" => Self::VARTYPE_BYTE,
            "java/lang/Short" => Self::VARTYPE_SHORT,
            "java/lang/Boolean" => Self::VARTYPE_BOOLEAN,
            "java/lang/Float" => Self::VARTYPE_FLOAT,
            "java/lang/Double" => Self::VARTYPE_DOUBLE,
            "java/lang/Long" => Self::VARTYPE_LONG,
            _ => return None,
        })
    }

    /// Whether the type is one that a wrapper class boxes.
    pub fn is_primitive(ty: &VarType) -> bool {
        [
            Self::VARTYPE_INT,
            Self::VARTYPE_CHAR,
            Self::VARTYPE_BYTE,
            Self::VARTYPE_SHORT,
            Self::VARTYPE_BOOLEAN,
            Self::VARTYPE_FLOAT,
            Self::VARTYPE_DOUBLE,
            Self::VARTYPE_LONG,
        ]
        .contains(ty)
    }

    // ==========================================================================
    //                            THE VARTYPE LATTICE
    // ==========================================================================
    //
    // VarType instances are organized in a lattice based on their type family.
    // Each family has its own lattice, each organized a bit differently, but all
    // are defined by MEET and JOIN. Of the 7 type families, the lattice of 4 of
    // them are trivial. For BOOLEAN, FLOAT, DOUBLE, and LONG, each element makes
    // up its own lattice such that:
    //                                  TOP
    //                                   |
    //                                  Type
    //                                   |
    //                                  BOT
    //
    // This makes MEET and JOIN trivial to define. Out of the rest, the integer
    // and object lattices are much more interesting. For the integer lattice, we
    // need to consider sub-integer types and how they play into the definition.
    // The integer lattice is defined as such:
    //                                  TOP
    //                                   |
    //                                  int
    //                                 /   \
    //                                /     \
    //                               /       \
    //                              /         \
    //                           char        short
    //                             \         /  |
    //                              \       /  byte
    //                               \     /    |
    //                               shortchar  |
    //                                   |     /
    //                                   |    /
    //                                bytechar
    //                                   |
    //                                  BOT
    //
    // The complication with this lattice is that there are in essence two
    // domains, integer and char. During the decompilation process there may
    // not be enough context to decide if a numerical definition is part of the
    // character or integer domain. To reconcile this, usages are calculated
    // and a sharper type is determined. The next interesting lattice is the
    // Object lattice family. It is defined as such:
    //
    //                                  TOP
    //                                   |
    //                                 Object
    //                                  /|\
    //                                 / | \
    //                                /  |  \
    //                             Implementors...
    //                                \  |  /
    //                                 \ | /
    //                                  \|/
    //                                   |
    //                                  null
    //                                   |
    //                                  BOT
    //
    // "Implementors" are any class that extends Object, so it can be regular
    // classes, all arrays, enums, records, et cetera. Arrays match the Object
    // lattice. If the size of the arrays are the same, then the array types
    // have the same relation as their base types.
    //
    // The final type family is UNKNOWN, the family of bottom types. This poses
    // a conundrum for the lattice, as it would only consist of the bottom.
    // Therefore it does not make sense to consider this as a lattice of its own
    // right, and just treat it as a special case.

    // Rule of thumb: A type HIGHER in the lattice will need a cast to go to a type LOWER in the lattice.
    pub fn higher_equal_in_lattice_than(&self, cx: &Cx, val: &VarType) -> bool {
        self == val
            || self.higher_in_lattice_than(cx, val)
            || val.unboxing_type().is_some_and(|unboxed| *self == unboxed)
    }

    /// Is `self` higher in the lattice when compared to `other`?
    pub fn higher_in_lattice_than(&self, cx: &Cx, other: &VarType) -> bool {
        // If other is BOT, and we are not BOT, we must necessarily be higher in the lattice
        if other.ty == CodeType::Unknown && self.ty != CodeType::Unknown {
            return true;
        }

        if self.array_dim > 0 && self.array_dim == other.array_dim {
            // Testing against two arrays
            // Arrays are covariant, check their bases
            return self
                .resize_array_dim(0)
                .higher_in_lattice_than(cx, &other.resize_array_dim(0));
        } else if other.array_dim > 0 {
            // If the other is an array, only Object is higher in the lattice than the other
            return *self == Self::VARTYPE_OBJECT;
        } else if self.array_dim > 0 {
            // If the other is not an array but we are, the only way we can be higher in the lattice
            // is if the other is null (close to bottom)
            return other.ty == CodeType::Null;
        }

        use CodeType::*;
        // c.f. the int family lattice
        match self.ty {
            Int => matches!(
                other.ty,
                Short | Char | Byte | Shortchar | Bytechar | Boolean
            ),
            Short => matches!(other.ty, Byte | Shortchar | Bytechar | Boolean),
            Char => matches!(other.ty, Shortchar | Bytechar | Boolean),
            Byte | Shortchar => matches!(other.ty, Bytechar | Boolean),
            // Special case boolean: it's represented as an integer, so the domains cross sometimes
            Bytechar => other.ty == Boolean,
            Object => {
                // BOT -> null -> Impl... -> Object -> TOP
                // if other is null, then, as an object, we must be higher in the lattice
                if other.ty == Null {
                    return true;
                } else if *self == Self::VARTYPE_OBJECT {
                    // if we are object, then we are higher than everything other than object and TOP
                    return *other != Self::VARTYPE_OBJECT;
                }

                // Check base if neither 'this' and 'other' are generic, or if the generic types
                // satisfy the condition.
                let check_base = !(self.is_generic() && other.is_generic())
                    || should_check_generic_base(self, other);

                // Given that B extends A, B is lower in the lattice when compared to A.
                check_base
                    && other.ty == Object
                    && other.value != self.value
                    && cx.classes().instance_of(other.name(), self.name())
            }
            _ => false,
        }
    }

    /// `higher_equal_in_lattice_than`, but also checking assignability
    /// relations across families.
    pub fn higher_cross_family_than(&self, cx: &Cx, other: &VarType, equal: bool) -> bool {
        // Check higher (equal) within the same lattice
        let higher = if equal {
            self.higher_equal_in_lattice_than(cx, other)
        } else {
            self.higher_in_lattice_than(cx, other)
        };
        if higher {
            return true;
        }

        // c.f. https://docs.oracle.com/javase/specs/jls/se21/html/jls-4.html#jls-4.10.1
        use TypeFamily::*;
        match self.ty {
            // float, long, and integer can be assigned to double
            CodeType::Double => matches!(other.type_family, Float | Long | Integer),
            // long and int
            CodeType::Float => matches!(other.type_family, Long | Integer),
            // just int
            CodeType::Long => other.type_family == Integer,
            _ => false,
        }
    }

    /// The "minimal" type out of the two provided (the MEET of both types).
    /// Types should fall in the lattice.
    pub fn meet(cx: &Cx, type1: &VarType, type2: &VarType) -> Option<VarType> {
        if type1.higher_equal_in_lattice_than(cx, type2) {
            return Some(type2.clone());
        } else if type2.higher_equal_in_lattice_than(cx, type1) {
            return Some(type1.clone());
        } else if type1.type_family == type2.type_family {
            // Special casing
            match type1.type_family {
                TypeFamily::Integer => {
                    return Some(
                        if matches!(
                            (type1.ty, type2.ty),
                            (CodeType::Char, CodeType::Short) | (CodeType::Short, CodeType::Char)
                        ) {
                            Self::VARTYPE_SHORTCHAR
                        } else {
                            Self::VARTYPE_BYTECHAR
                        },
                    );
                }
                // Consider a hierarchy where:
                // - B extends A
                // - C extends A
                // meet(B, C) must be null
                // TODO: no it doesn't! it can be a union type, that way it preserves information!
                TypeFamily::Object => return Some(Self::VARTYPE_NULL),
                _ => {}
            }
        }

        None
    }

    /// The "maximal" type out of the two provided (the JOIN of both types).
    /// Types should rise in the lattice.
    pub fn join(cx: &Cx, type1: &VarType, type2: &VarType) -> Option<VarType> {
        if type1.higher_equal_in_lattice_than(cx, type2) {
            return Some(type1.clone());
        } else if type2.higher_equal_in_lattice_than(cx, type1) {
            return Some(type2.clone());
        } else if type1.type_family == type2.type_family {
            // Special casing
            match type1.type_family {
                TypeFamily::Integer => {
                    return Some(
                        if matches!(
                            (type1.ty, type2.ty),
                            (CodeType::Shortchar, CodeType::Byte)
                                | (CodeType::Byte, CodeType::Shortchar)
                        ) {
                            Self::VARTYPE_SHORT
                        } else {
                            Self::VARTYPE_INT
                        },
                    );
                }
                TypeFamily::Object => {
                    // If either is null, join is the other
                    if type1.ty == CodeType::Null {
                        return Some(type2.clone());
                    } else if type2.ty == CodeType::Null {
                        return Some(type1.clone());
                    }

                    // TODO: can make an intersection type?
                    return Some(
                        match cx
                            .classes()
                            .find_common_ancestor(type1.name(), type2.name())
                        {
                            Some(cl) => Self::from_signature_cl(&cl.qualified_name, true),
                            None => Self::VARTYPE_OBJECT,
                        },
                    );
                }
                _ => {}
            }
        }

        None
    }

    pub fn find_family_bottom(family: TypeFamily) -> VarType {
        match family {
            TypeFamily::Boolean => Self::VARTYPE_BOOLEAN,
            TypeFamily::Integer => Self::VARTYPE_BYTECHAR,
            TypeFamily::Object => Self::VARTYPE_NULL,
            TypeFamily::Float => Self::VARTYPE_FLOAT,
            TypeFamily::Long => Self::VARTYPE_LONG,
            TypeFamily::Double => Self::VARTYPE_DOUBLE,
            TypeFamily::Unknown => Self::VARTYPE_UNKNOWN,
        }
    }
}

impl PartialEq for VarType {
    fn eq(&self, other: &Self) -> bool {
        self.ty == other.ty && self.array_dim == other.array_dim && self.value == other.value
    }
}

impl Eq for VarType {}

impl Hash for VarType {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.ty.hash(state);
        self.array_dim.hash(state);
        self.value.hash(state);
    }
}

impl JavaHash for VarType {
    fn java_hash(&self) -> i32 {
        let mut result = 1i32;
        result = result.wrapping_mul(37).wrapping_add(self.ty.ordinal());
        result = result.wrapping_mul(37).wrapping_add(self.array_dim);
        result.wrapping_mul(37).wrapping_add(
            self.value
                .as_deref()
                .map_or(0, JavaHash::java_hash),
        )
    }

    fn java_class_name(&self) -> Option<&'static str> {
        Some(if self.generic.is_some() {
            "org.jetbrains.java.decompiler.struct.gen.generics.GenericType"
        } else {
            "org.jetbrains.java.decompiler.struct.gen.VarType"
        })
    }
}

/// `VarType.toString()`: the descriptor form. The text upstream's
/// `GenericType.toString()` adds around it needs the import collector and is
/// [`VarType::to_generic_string`].
impl fmt::Display for VarType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for _ in 0..self.array_dim {
            f.write_str("[")?;
        }
        if self.ty == CodeType::Object {
            write!(f, "L{};", self.value.as_deref().unwrap_or("null"))
        } else {
            f.write_str(self.value.as_deref().unwrap_or("--null--"))
        }
    }
}
