// Copyright 2000-2018 JetBrains s.r.o. and Kotlin Programming Language contributors.
// SPDX-License-Identifier: Apache-2.0

//! Kotlin 2.2.20 metadata deserialization flags.

use std::marker::PhantomData;

use super::proto::{MemberKind, Modality, Visibility, class};

#[derive(Clone, Copy, Debug)]
pub struct BooleanFlag(u8);

impl BooleanFlag {
    pub const fn get(self, flags: i32) -> bool {
        flags & (1 << self.0) != 0
    }
}

#[derive(Clone, Copy, Debug)]
pub struct EnumFlag<E> {
    offset: u8,
    width: u8,
    enumeration: PhantomData<fn() -> E>,
}

impl<E: TryFrom<i32>> EnumFlag<E> {
    const fn new(offset: u8, width: u8) -> Self {
        Self {
            offset,
            width,
            enumeration: PhantomData,
        }
    }

    pub fn get(self, flags: i32) -> Option<E> {
        E::try_from((flags >> self.offset) & ((1 << self.width) - 1)).ok()
    }
}

// Common declaration prefix.
pub const HAS_ANNOTATIONS: BooleanFlag = BooleanFlag(0);
pub const VISIBILITY: EnumFlag<Visibility> = EnumFlag::new(1, 3);
pub const MODALITY: EnumFlag<Modality> = EnumFlag::new(4, 2);
pub const MEMBER_KIND: EnumFlag<MemberKind> = EnumFlag::new(6, 2);

// Class.
pub const CLASS_KIND: EnumFlag<class::Kind> = EnumFlag::new(6, 3);
pub const IS_INNER: BooleanFlag = BooleanFlag(9);
pub const IS_DATA: BooleanFlag = BooleanFlag(10);
pub const IS_EXTERNAL_CLASS: BooleanFlag = BooleanFlag(11);
pub const IS_EXPECT_CLASS: BooleanFlag = BooleanFlag(12);
pub const IS_VALUE_CLASS: BooleanFlag = BooleanFlag(13);
pub const IS_FUN_INTERFACE: BooleanFlag = BooleanFlag(14);
pub const HAS_ENUM_ENTRIES: BooleanFlag = BooleanFlag(15);

// Constructor.
pub const IS_SECONDARY: BooleanFlag = BooleanFlag(4);
pub const IS_CONSTRUCTOR_WITH_NON_STABLE_PARAMETER_NAMES: BooleanFlag = BooleanFlag(5);
pub const HAS_MUST_USE_RETURN_VALUE_CTOR: BooleanFlag = BooleanFlag(6);

// Function.
pub const IS_OPERATOR: BooleanFlag = BooleanFlag(8);
pub const IS_INFIX: BooleanFlag = BooleanFlag(9);
pub const IS_INLINE: BooleanFlag = BooleanFlag(10);
pub const IS_TAILREC: BooleanFlag = BooleanFlag(11);
pub const IS_EXTERNAL_FUNCTION: BooleanFlag = BooleanFlag(12);
pub const IS_SUSPEND: BooleanFlag = BooleanFlag(13);
pub const IS_EXPECT_FUNCTION: BooleanFlag = BooleanFlag(14);
pub const IS_FUNCTION_WITH_NON_STABLE_PARAMETER_NAMES: BooleanFlag = BooleanFlag(15);
pub const HAS_MUST_USE_RETURN_VALUE_FUNCTION: BooleanFlag = BooleanFlag(16);

// Property.
pub const IS_VAR: BooleanFlag = BooleanFlag(8);
pub const HAS_GETTER: BooleanFlag = BooleanFlag(9);
pub const HAS_SETTER: BooleanFlag = BooleanFlag(10);
pub const IS_CONST: BooleanFlag = BooleanFlag(11);
pub const IS_LATEINIT: BooleanFlag = BooleanFlag(12);
pub const HAS_CONSTANT: BooleanFlag = BooleanFlag(13);
pub const IS_EXTERNAL_PROPERTY: BooleanFlag = BooleanFlag(14);
pub const IS_DELEGATED: BooleanFlag = BooleanFlag(15);
pub const IS_EXPECT_PROPERTY: BooleanFlag = BooleanFlag(16);
pub const HAS_MUST_USE_RETURN_VALUE_PROPERTY: BooleanFlag = BooleanFlag(17);

// Value parameter.
pub const DECLARES_DEFAULT_VALUE: BooleanFlag = BooleanFlag(1);
pub const IS_CROSSINLINE: BooleanFlag = BooleanFlag(2);
pub const IS_NOINLINE: BooleanFlag = BooleanFlag(3);

// Accessor.
pub const IS_NOT_DEFAULT: BooleanFlag = BooleanFlag(6);
pub const IS_EXTERNAL_ACCESSOR: BooleanFlag = BooleanFlag(7);
pub const IS_INLINE_ACCESSOR: BooleanFlag = BooleanFlag(8);

// Type, contract expression, and annotation argument flags.
pub const SUSPEND_TYPE: BooleanFlag = BooleanFlag(0);
pub const DEFINITELY_NOT_NULL_TYPE: BooleanFlag = BooleanFlag(1);
pub const IS_NEGATED: BooleanFlag = BooleanFlag(0);
pub const IS_NULL_CHECK_PREDICATE: BooleanFlag = BooleanFlag(1);
pub const IS_UNSIGNED: BooleanFlag = BooleanFlag(0);
