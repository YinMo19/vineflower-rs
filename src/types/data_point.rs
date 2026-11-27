//! `struct.gen.DataPoint`: the local slots and operand stack at a point in
//! the bytecode.

use super::{CodeType, MethodDescriptor, VarType};
use crate::code::code_constants::ACC_STATIC;
use crate::structs::{StructClass, StructMember, StructMethod};

#[derive(Clone, Debug, Default)]
pub struct DataPoint {
    local_variables: Vec<VarType>,
    stack: Vec<VarType>,
}

impl DataPoint {
    pub fn initial(class: &StructClass, method: &StructMethod) -> Self {
        let descriptor = MethodDescriptor::parse_descriptor(&method.descriptor);
        let mut point = Self::default();

        if !method.has_modifier(ACC_STATIC) {
            point.local_variables.push(VarType::with_value(
                CodeType::Object,
                0,
                class.qualified_name.clone(),
            ));
        }

        for parameter in descriptor.params {
            let wide = parameter.stack_size == 2;
            point.local_variables.push(parameter);
            if wide {
                point
                    .local_variables
                    .push(VarType::new(CodeType::Group2empty));
            }
        }

        point
    }

    pub fn local_variables(&self) -> &[VarType] {
        &self.local_variables
    }

    pub fn get_variable(&self, index: usize) -> VarType {
        self.local_variables
            .get(index)
            .cloned()
            .unwrap_or_else(|| VarType::new(CodeType::Notinitialized))
    }

    pub fn set_variable(&mut self, index: usize, value: VarType) {
        if index >= self.local_variables.len() {
            self.local_variables
                .resize_with(index + 1, || VarType::new(CodeType::Notinitialized));
        }
        self.local_variables[index] = value;
    }

    pub fn stack(&self) -> &[VarType] {
        &self.stack
    }

    pub fn stack_mut(&mut self) -> &mut Vec<VarType> {
        &mut self.stack
    }

    /// The state propagated to an exception handler by `removeJsrInstructions`.
    pub fn exception_successor(&self) -> Self {
        Self {
            local_variables: self.local_variables.clone(),
            stack: vec![VarType::VARTYPE_OBJECT],
        }
    }
}
