// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `code.MethodProperties`: what `MethodPropertiesProcessor` learns about a
//! method from its bytecode before the method is decompiled.

use std::sync::Arc;

use crate::structs::struct_field::StructField;
use crate::structs::struct_method::StructMethod;

pub struct MethodProperties {
    pub mt: Arc<StructMethod>,
    pub is_synthetic_reference_lambda: bool,
    pub assert_field: Option<Arc<StructField>>,
}

impl MethodProperties {
    pub fn new(mt: Arc<StructMethod>) -> Self {
        Self {
            mt,
            is_synthetic_reference_lambda: false,
            assert_field: None,
        }
    }
}
