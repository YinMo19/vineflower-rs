// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `code.MethodProperties`: what `MethodPropertiesProcessor` learns about a
//! method from its bytecode before the method is decompiled.

use std::sync::Arc;

use super::Instruction;
use super::code_constants::*;
use crate::structs::struct_method::StructMethod;
use crate::structs::{StructClass, StructField, StructMember};

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

    pub(crate) fn analyze(
        method: Arc<StructMethod>,
        class: &StructClass,
        before_warning: impl FnOnce(),
    ) -> Self {
        let mut result = Self::new(method);
        let method = &result.mt;
        let synthetic = method.has_modifier(ACC_STATIC | ACC_SYNTHETIC);
        let initializer = method.name.as_str() == CLINIT_NAME;
        if !method.contains_code() || !(synthetic || initializer) {
            return result;
        }
        match method.expand_data(class) {
            Ok(Some(code)) => {
                if synthetic {
                    result.is_synthetic_reference_lambda =
                        is_synthetic_reference_lambda(&code.instructions);
                }
                if initializer {
                    result.assert_field = assert_field(class, &code.instructions);
                }
            }
            Err(err) => {
                before_warning();
                log::warn!(
                    "Could not read method properties of {}.{method}: {err}",
                    class.qualified_name
                );
            }
            Ok(None) => {}
        }
        result
    }
}

fn is_synthetic_reference_lambda(instructions: &[Arc<Instruction>]) -> bool {
    let mut code = instructions
        .iter()
        .map(|i| i.opcode)
        .skip_while(|op| (OPC_ILOAD..=OPC_ALOAD).contains(op));
    match code.next() {
        None => true,
        Some(OPC_INVOKEVIRTUAL) => {
            code.all(|op| matches!(op, OPC_POP | OPC_POP2 | OPC_IRETURN..=OPC_RETURN))
        }
        _ => false,
    }
}

fn assert_field(class: &StructClass, code: &[Arc<Instruction>]) -> Option<Arc<StructField>> {
    for window in code.windows(7) {
        let [load, invoke, branch, one, jump, zero, store] = window else {
            unreachable!()
        };
        if matches!(load.opcode, OPC_LDC | OPC_LDC_W)
            && invoke.opcode == OPC_INVOKEVIRTUAL
            && branch.opcode == OPC_IFNE
            && one.opcode == OPC_BIPUSH
            && one.operand(0) == 1
            && jump.opcode == OPC_GOTO
            && zero.opcode == OPC_BIPUSH
            && zero.operand(0) == 0
            && store.opcode == OPC_PUTSTATIC
            && let Some(check) = class.pool.get_link_constant(invoke.operand(0))
            && check.classname.as_deref() == Some("java/lang/Class")
            && check.elementname == "desiredAssertionStatus"
            && let Some(field) = class.pool.get_link_constant(store.operand(0))
            && field.classname.as_ref() == Some(&class.qualified_name)
            && field.descriptor == "Z"
        {
            return class
                .get_field(&field.elementname, &field.descriptor)
                .cloned();
        }
    }
    None
}
