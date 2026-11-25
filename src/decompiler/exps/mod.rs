// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `modules.decompiler.exps`: the typed expressions produced by bytecode lifting.

pub(crate) mod bounds;
mod bytecode;
mod function;
mod increments;
mod operations;
mod traversal;

use std::sync::Arc;

use arcstr::ArcStr;
use index_vec::IndexVec;

pub(crate) use self::increments::{delta_by_one, increment};
pub use self::{bytecode::BytecodeOffsets, function::FunctionType};
pub use crate::structs::consts::ConstantValue;

use crate::code::instruction::Instruction;
use crate::decompiler::ir::{ExprId, Ir, StatId, VarProcessorId};
use crate::decompiler::stats::StatementKind;
use crate::decompiler::vars::{var_version_pair::VarVersionPair, versions::VarVersions};
use crate::engine::Cx;
use crate::engine::class_nodes::ClassKind;
use crate::engine::counter_container::{CounterContainer, EXPRESSION_COUNTER, VAR_COUNTER};
use crate::structs::attr::LocalVariable;
use crate::structs::consts::{LinkConstant, PooledConstant};
use crate::types::{CodeType, FieldDescriptor, GenericType, MethodDescriptor, VarType};

/// `VarExprent.STACK_BASE`.
pub const STACK_BASE: i32 = 10_000;

#[derive(Debug)]
pub struct Expr {
    pub id: i32,
    pub kind: ExprKind,
    pub bytecode: Option<BytecodeOffsets>,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Assert {
        /// A missing condition is the representation of `assert false`.
        condition: Option<ExprId>,
        message: Option<ExprId>,
    },
    Constant {
        value: ConstantValue,
        var_type: VarType,
        bool_permitted: bool,
        was_condy: bool,
    },
    Variable(Variable),
    Assignment {
        left: ExprId,
        right: ExprId,
        compound: Option<FunctionType>,
    },
    Array {
        array: ExprId,
        index: ExprId,
        hard_type: VarType,
    },
    Field(Box<Field>),
    Invocation(Box<Invocation>),
    Function {
        op: FunctionType,
        operands: Vec<ExprId>,
        implicit_type: Option<Box<VarType>>,
    },
    New {
        new_type: VarType,
        dimensions: Box<[ExprId]>,
        constructor: Option<ExprId>,
        array_elements: Box<[ExprId]>,
        direct_array_init: bool,
        anonymous: bool,
        lambda: bool,
        method_reference: bool,
    },
    Exit {
        kind: ExitType,
        value: Option<ExprId>,
        return_type: Option<VarType>,
        method_descriptor: Arc<MethodDescriptor>,
    },
    Monitor {
        kind: MonitorType,
        value: ExprId,
        remove: bool,
    },
    If {
        condition: ExprId,
    },
    SwitchHead {
        value: ExprId,
        case_values: Option<SwitchCaseValues>,
    },
}

#[derive(Clone, Debug)]
pub struct Variable {
    pub processor: Option<VarProcessorId>,
    pub index: i32,
    pub var_type: VarType,
    pub version: i32,
    pub stack: bool,
    pub catch_temp: bool,
    pub effectively_final: bool,
    pub backing_instruction: Option<Arc<Instruction>>,
    pub lvt: Option<Arc<LocalVariable>>,
}

impl Variable {
    pub fn new(index: i32, var_type: VarType) -> Self {
        Self {
            processor: None,
            index,
            var_type,
            version: 0,
            stack: false,
            catch_temp: false,
            effectively_final: false,
            backing_instruction: None,
            lvt: None,
        }
    }

    pub fn pair(&self) -> VarVersionPair {
        VarVersionPair::new(self.index, self.version)
    }

    pub(crate) fn in_method(index: i32, ty: VarType, owner: VarProcessorId) -> Self {
        Self {
            processor: Some(owner),
            ..Self::new(index, ty)
        }
    }

    pub(crate) fn push_stack(mut self, ir: &mut Ir, counters: &mut CounterContainer) -> ExprId {
        self.stack = true;
        Expr::new(ir, counters, ExprKind::Variable(self), None)
    }

    /// VarExprent.setLVT also seeds its method's active type processor.
    fn record_local_type(&self, processors: &mut IndexVec<VarProcessorId, VarVersions>) {
        if let Some(owner) = self.processor
            && processors[owner].initialized
            && let Some(lvt) = &self.lvt
        {
            processors[owner]
                .lower
                .insert(self.pair(), lvt.get_var_type());
        }
    }

    pub(crate) fn expr_type(&self, cx: &Cx) -> VarType {
        if cx.options.use_lvt_names
            && let Some(lvt) = &self.lvt
        {
            lvt.get_var_type()
        } else if self.var_type.ty == CodeType::Unknown
            && let Some(owner) = self.processor
            && let Some(ty) = cx.ir[owner].lower.get(&self.pair())
        {
            ty.clone()
        } else {
            self.var_type.clone()
        }
    }
}

#[derive(Clone, Debug)]
pub struct Field {
    pub name: ArcStr,
    pub classname: Option<ArcStr>,
    pub instance: Option<ExprId>,
    pub descriptor: FieldDescriptor,
    pub force_qualified: bool,
    pub was_condy: bool,
}

impl Field {
    pub fn from_link(link: &LinkConstant, instance: Option<ExprId>) -> Self {
        Self {
            name: link.elementname.clone(),
            classname: link.classname.clone(),
            instance,
            descriptor: FieldDescriptor::parse_descriptor(&link.descriptor),
            force_qualified: false,
            was_condy: false,
        }
    }

    pub fn is_static(&self) -> bool {
        self.instance.is_none()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InvocationType {
    Special,
    Virtual,
    Static,
    Interface,
    Dynamic,
    ConstantDynamic,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InvocationFunction {
    General,
    Init,
    Clinit,
}

#[derive(Clone, Debug)]
pub struct Invocation {
    pub kind: InvocationType,
    pub function: InvocationFunction,
    pub name: ArcStr,
    pub classname: Option<ArcStr>,
    pub is_static: bool,
    pub instance: Option<ExprId>,
    pub descriptor: Arc<MethodDescriptor>,
    pub dynamic_class_suffix: Option<ArcStr>,
    pub parameters: Vec<ExprId>,
    pub bootstrap_method: Option<LinkConstant>,
    pub bootstrap_arguments: Option<Arc<[Option<PooledConstant>]>>,
    pub synthetic_null_check: bool,
    pub was_lazy_condy: bool,
}

impl Invocation {
    pub fn new(name: ArcStr, classname: Option<ArcStr>, descriptor: Arc<MethodDescriptor>) -> Self {
        Self {
            kind: InvocationType::Virtual,
            function: InvocationFunction::General,
            name,
            classname,
            is_static: false,
            instance: None,
            descriptor,
            dynamic_class_suffix: None,
            parameters: Vec::new(),
            bootstrap_method: None,
            bootstrap_arguments: None,
            synthetic_null_check: false,
            was_lazy_condy: false,
        }
    }

    pub fn string_descriptor(&self) -> &str {
        self.descriptor.as_str()
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExitType {
    Return,
    Throw,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MonitorType {
    Enter,
    Exit,
}

#[derive(Clone, Debug)]
pub enum SwitchCaseValues {
    /// The header shares the switch statement's label lists after initialization.
    Statement(StatId),
    /// `SwitchHeadExprent.copy` copies the lists, sharing their expressions.
    Copied(Box<[Vec<Option<ExprId>>]>),
}

impl SwitchCaseValues {
    fn copy(&self, ir: &Ir) -> Self {
        match self {
            Self::Statement(stat) => {
                let StatementKind::Switch(switch) = &ir[*stat].kind else {
                    unreachable!("Switch header case values belong to a switch statement");
                };
                Self::Copied(
                    switch
                        .cases
                        .iter()
                        .map(|case| case.values.clone())
                        .collect(),
                )
            }
            Self::Copied(_) => self.clone(),
        }
    }
}

impl Expr {
    pub fn new(
        ir: &mut Ir,
        counters: &mut CounterContainer,
        kind: ExprKind,
        bytecode: Option<BytecodeOffsets>,
    ) -> ExprId {
        ir.exprs.push(Self {
            id: counters.get_counter_and_increment(EXPRESSION_COUNTER),
            kind,
            bytecode,
        })
    }

    pub fn function(
        ir: &mut Ir,
        counters: &mut CounterContainer,
        op: FunctionType,
        operands: Vec<ExprId>,
        bytecode: Option<BytecodeOffsets>,
    ) -> ExprId {
        Self::new(
            ir,
            counters,
            ExprKind::Function {
                op,
                operands,
                implicit_type: None,
            },
            bytecode,
        )
    }

    pub(crate) fn guess_int_type(value: i32, bool_permitted: bool) -> VarType {
        match value {
            0 | 1 if bool_permitted => VarType::VARTYPE_BOOLEAN,
            0..=127 => VarType::VARTYPE_BYTECHAR,
            -128..=-1 => VarType::VARTYPE_BYTE,
            128..=32767 => VarType::VARTYPE_SHORTCHAR,
            -32768..=-129 => VarType::VARTYPE_SHORT,
            32768..=65535 => VarType::VARTYPE_CHAR,
            _ => VarType::VARTYPE_INT,
        }
    }

    pub fn int_constant(value: i32, bool_permitted: bool) -> ExprKind {
        ExprKind::Constant {
            value: ConstantValue::Integer(value),
            var_type: Self::guess_int_type(value, bool_permitted),
            bool_permitted,
            was_condy: false,
        }
    }

    pub fn constant(mut var_type: VarType, value: ConstantValue, was_condy: bool) -> ExprKind {
        if var_type == VarType::VARTYPE_CLASS
            && let ConstantValue::String(name) = &value
        {
            let name = name.as_utf8_lossy();
            let argument = VarType::from_signature_cl(name, !name.starts_with('['));
            var_type = VarType::generic(
                var_type.ty,
                var_type.array_dim,
                var_type.value,
                None,
                vec![Some(argument)],
                GenericType::WILDCARD_NO,
            );
        }
        ExprKind::Constant {
            value,
            var_type,
            bool_permitted: false,
            was_condy,
        }
    }

    pub fn new_int_constant(
        ir: &mut Ir,
        counters: &mut CounterContainer,
        value: i32,
        bool_permitted: bool,
    ) -> ExprId {
        Self::new(
            ir,
            counters,
            Self::int_constant(value, bool_permitted),
            None,
        )
    }

    pub fn new_variable(ir: &mut Ir, counters: &mut CounterContainer, var_type: VarType) -> ExprId {
        let index = counters.get_counter_and_increment(VAR_COUNTER);
        let kind = ExprKind::Variable(Variable::new(index, var_type));
        Self::new(ir, counters, kind, None)
    }

    pub fn new_stack_variable(
        ir: &mut Ir,
        counters: &mut CounterContainer,
        index: i32,
        var_type: VarType,
    ) -> ExprId {
        Variable::new(index, var_type).push_stack(ir, counters)
    }

    pub(crate) fn set_local_variable(ir: &mut Ir, expr: ExprId, lvt: Arc<LocalVariable>) {
        let ExprKind::Variable(var) = &mut ir.exprs[expr].kind else {
            unreachable!()
        };
        var.lvt = Some(lvt);
        var.record_local_type(&mut ir.variable_processors);
    }

    pub fn new_if(
        ir: &mut Ir,
        counters: &mut CounterContainer,
        bytecode: Option<BytecodeOffsets>,
        build_condition: impl FnOnce(&mut Ir, &mut CounterContainer) -> ExprId,
    ) -> ExprId {
        // The stack-based IfExprent constructor calls its base constructor first.
        let id = counters.get_counter_and_increment(EXPRESSION_COUNTER);
        let condition = build_condition(ir, counters);
        ir.exprs.push(Self {
            id,
            kind: ExprKind::If { condition },
            bytecode,
        })
    }

    pub fn new_allocation(
        cx: &mut Cx,
        counters: &mut CounterContainer,
        new_type: VarType,
        dimensions: Vec<ExprId>,
        bytecode: Option<BytecodeOffsets>,
    ) -> ExprId {
        let (anonymous, lambda, method_reference) = allocation_flags(cx, &new_type);
        Self::new(
            &mut cx.ir,
            counters,
            ExprKind::New {
                new_type,
                dimensions: dimensions.into_boxed_slice(),
                constructor: None,
                array_elements: Box::new([]),
                direct_array_init: false,
                anonymous,
                lambda,
                method_reference,
            },
            bytecode,
        )
    }

    /// `Exprent.getExprType`, including a local's method-specific inferred type.
    pub fn expr_type(cx: &Cx, expr: ExprId) -> VarType {
        match &cx.ir[expr].kind {
            ExprKind::Constant { var_type, .. } => var_type.clone(),
            ExprKind::Variable(variable) => variable.expr_type(cx),
            ExprKind::Assignment { left, right, .. } => {
                let left = Self::expr_type(cx, *left);
                let right = Self::expr_type(cx, *right);
                VarType::join(cx, &left, &right).unwrap_or(left)
            }
            ExprKind::Array {
                array, hard_type, ..
            } => {
                let array_type = Self::expr_type(cx, *array);
                if array_type == VarType::VARTYPE_NULL {
                    hard_type.clone()
                } else {
                    array_type.decrease_array_dim()
                }
            }
            ExprKind::Field(field) => field.descriptor.ty.clone(),
            ExprKind::Invocation(invocation) => invocation.descriptor.ret.clone(),
            ExprKind::Function {
                op,
                operands,
                implicit_type,
            } => op.expr_type(cx, operands, implicit_type.as_deref()),
            ExprKind::New {
                new_type,
                anonymous,
                ..
            } => {
                if *anonymous {
                    cx.class_nodes[new_type.name()]
                        .anonymous_type
                        .as_ref()
                        .expect("Anonymous allocation type")
                        .clone()
                } else {
                    new_type.clone()
                }
            }
            ExprKind::SwitchHead { value, .. } => Self::expr_type(cx, *value),
            ExprKind::Assert { .. }
            | ExprKind::If { .. }
            | ExprKind::Exit { .. }
            | ExprKind::Monitor { .. } => VarType::VARTYPE_VOID,
        }
    }

    /// `Exprent.copy` gives the expression and its children fresh IDs in
    /// constructor order. Immutable metadata and shared case-label expressions
    /// retain their original values.
    pub fn copy(cx: &mut Cx, counters: &mut CounterContainer, expr: ExprId) -> ExprId {
        let mut kind = cx.ir[expr].kind.clone();
        let mut bytecode = cx.ir[expr].bytecode.clone();
        let mut id = None;
        match &mut kind {
            // AssertExprent copies its parameter list, retaining the child identities.
            ExprKind::Assert { .. } => bytecode = None,
            ExprKind::Constant {
                value,
                var_type,
                bool_permitted,
                was_condy,
            } => {
                if *var_type == VarType::VARTYPE_CLASS {
                    kind = Self::constant(var_type.clone(), value.clone(), *was_condy);
                } else {
                    *bool_permitted = false;
                }
            }
            ExprKind::Variable(variable) => {
                variable.var_type = variable.expr_type(cx);
                variable.backing_instruction = None;
                variable.record_local_type(&mut cx.ir.variable_processors);
            }
            ExprKind::Assignment { left, right, .. } => {
                *left = Self::copy(cx, counters, *left);
                *right = Self::copy(cx, counters, *right);
            }
            ExprKind::Array { array, index, .. } => {
                *array = Self::copy(cx, counters, *array);
                *index = Self::copy(cx, counters, *index);
            }
            ExprKind::Field(field) => {
                field.instance = field.instance.map(|expr| Self::copy(cx, counters, expr));
            }
            ExprKind::Invocation(invocation) => {
                id = Some(counters.get_counter_and_increment(EXPRESSION_COUNTER));
                invocation.instance = invocation
                    .instance
                    .map(|expr| Self::copy(cx, counters, expr));
                copy_entries(cx, counters, &mut invocation.parameters);
                // The nonstatic invokedynamic receiver aliases the first argument.
                if invocation.kind == InvocationType::Dynamic
                    && !invocation.is_static
                    && invocation.instance.is_some()
                    && let Some(&first) = invocation.parameters.first()
                {
                    invocation.instance = Some(first);
                }
            }
            ExprKind::Function { operands, .. } => copy_entries(cx, counters, operands),
            ExprKind::New {
                new_type,
                dimensions,
                constructor,
                array_elements,
                lambda,
                method_reference,
                ..
            } => {
                copy_entries(cx, counters, dimensions);
                id = Some(counters.get_counter_and_increment(EXPRESSION_COUNTER));
                (_, *lambda, *method_reference) = allocation_flags(cx, new_type);
                *constructor = constructor.map(|expr| Self::copy(cx, counters, expr));
                copy_entries(cx, counters, array_elements);
            }
            ExprKind::Exit { value, .. } => {
                *value = value.map(|expr| Self::copy(cx, counters, expr));
            }
            ExprKind::Monitor { value, remove, .. } => {
                *value = Self::copy(cx, counters, *value);
                *remove = false;
            }
            ExprKind::If { condition } => *condition = Self::copy(cx, counters, *condition),
            ExprKind::SwitchHead { value, case_values } => {
                *value = Self::copy(cx, counters, *value);
                *case_values = case_values.as_ref().map(|cases| cases.copy(&cx.ir));
            }
        }
        cx.ir.exprs.push(Self {
            id: id.unwrap_or_else(|| counters.get_counter_and_increment(EXPRESSION_COUNTER)),
            kind,
            bytecode,
        })
    }
}

fn allocation_flags(cx: &Cx, new_type: &VarType) -> (bool, bool, bool) {
    if new_type.ty == CodeType::Object
        && new_type.array_dim == 0
        && let Some(node) = cx.class_nodes.get(new_type.name())
    {
        let lambda = node.kind == ClassKind::Lambda;
        (
            node.kind == ClassKind::Anonymous || lambda,
            lambda,
            lambda
                && node
                    .lambda
                    .as_ref()
                    .is_some_and(|info| info.is_method_reference),
        )
    } else {
        (false, false, false)
    }
}

fn copy_entries(cx: &mut Cx, counters: &mut CounterContainer, exprents: &mut [ExprId]) {
    for expr in exprents {
        *expr = Expr::copy(cx, counters, *expr);
    }
}
