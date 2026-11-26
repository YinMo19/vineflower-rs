// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `modules.decompiler.exps`: the typed expressions produced by bytecode lifting.

pub(crate) mod bounds;
mod bytecode;
pub(crate) mod expr_util;
mod function;
pub(crate) mod generic_inference;
mod increments;
pub mod literal;
mod operations;
mod traversal;
pub mod write;

use std::fmt;
use std::sync::Arc;

use arcstr::ArcStr;
use index_vec::IndexVec;

pub use self::generic_inference::{AllocationGenerics, InvocationGenerics};
pub(crate) use self::increments::{delta_by_one, increment};
pub use self::{bytecode::BytecodeOffsets, function::FunctionType};
pub use crate::structs::consts::ConstantValue;

use crate::code::instruction::Instruction;
use crate::decompiler::ir::{ExprId, Ir, StatId, VarProcessorId};
use crate::decompiler::stats::StatementKind;
use crate::decompiler::vars::{processor::VarProcessor, var_version_pair::VarVersionPair};
use crate::engine::Cx;
use crate::engine::class_nodes::ClassKind;
use crate::engine::counter_container::{CounterContainer, EXPRESSION_COUNTER, VAR_COUNTER};
use crate::structs::StructClass;
use crate::structs::attr::LocalVariable;
use crate::structs::consts::{LinkConstant, PooledConstant};
use crate::types::generic_main;
use crate::types::{CodeType, FieldDescriptor, GenericType, MethodDescriptor, TypeFamily, VarType};

/// `VarExprent.STACK_BASE`.
pub const STACK_BASE: i32 = 10_000;

bitflags::bitflags! {
    /// Mutable print state belongs to the expression object. Recursive writers
    /// can revisit an aliased operand after a previous use has marked it.
    #[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
    pub(crate) struct WriteFlags: u8 {
        const QUALIFIER       = 1 << 0;
        const WRITING_PATTERN = 1 << 1;
        const FORCE_UNBOXING  = 1 << 2;
        const VARARG          = 1 << 3;
        const UNGROUPED       = 1 << 4;
        const ENUM_CONST      = 1 << 5;
    }
}

#[derive(Debug)]
pub struct Expr {
    pub id: i32,
    pub kind: ExprKind,
    pub(crate) write_flags: WriteFlags,
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
        needs_cast: bool,
    },
    Pattern(Box<Pattern>),
    New {
        new_type: VarType,
        dimensions: Box<[ExprId]>,
        constructor: Option<ExprId>,
        array_elements: Box<[ExprId]>,
        direct_array_init: bool,
        anonymous: bool,
        lambda: bool,
        method_reference: bool,
        generics: Option<Box<AllocationGenerics>>,
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
    Switch {
        backing: StatId,
        var_type: VarType,
        fallthrough: bool,
        standalone: bool,
    },
    Yield {
        value: ExprId,
        return_type: VarType,
    },
}

/// A record pattern with bindings in declaration order.
#[derive(Clone)]
pub struct Pattern {
    pub class: Arc<StructClass>,
    pub var_type: VarType,
    pub children: Vec<ExprId>,
    pub bound_types: Vec<Option<VarType>>,
}

impl fmt::Debug for Pattern {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Pattern")
            .field("class", &self.class.qualified_name)
            .field("var_type", &self.var_type)
            .field("children", &self.children)
            .field("bound_types", &self.bound_types)
            .finish()
    }
}

#[derive(Clone, Debug)]
pub struct Variable {
    pub processor: Option<VarProcessorId>,
    pub index: i32,
    /// The stored type can be absent on a declaration with no inferred lower bound.
    pub var_type: Option<VarType>,
    pub version: i32,
    pub stack: bool,
    pub definition: bool,
    pub class_definition: bool,
    pub catch_temp: bool,
    pub intersection_type: bool,
    pub effectively_final: bool,
    pub backing_instruction: Option<Arc<Instruction>>,
    pub lvt: Option<Arc<LocalVariable>>,
    /// A lower type bound retained from an assignment removed by loop recovery.
    pub bound_type: Option<Box<VarType>>,
}

impl Variable {
    pub fn new(index: i32, var_type: impl Into<Option<VarType>>) -> Self {
        Self {
            processor: None,
            index,
            var_type: var_type.into(),
            version: 0,
            stack: false,
            definition: false,
            class_definition: false,
            catch_temp: false,
            intersection_type: false,
            effectively_final: false,
            backing_instruction: None,
            lvt: None,
            bound_type: None,
        }
    }

    pub fn pair(&self) -> VarVersionPair {
        VarVersionPair::new(self.index, self.version)
    }

    pub(crate) fn in_method(
        index: i32,
        ty: impl Into<Option<VarType>>,
        owner: VarProcessorId,
    ) -> Self {
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
    fn record_local_type(&self, processors: &mut IndexVec<VarProcessorId, VarProcessor>) {
        if let Some(owner) = self.processor
            && processors[owner].versions.initialized
            && let Some(lvt) = &self.lvt
        {
            processors[owner]
                .versions
                .lower
                .insert(self.pair(), lvt.get_var_type());
        }
    }

    pub(crate) fn expr_type(&self, cx: &Cx) -> VarType {
        if cx.options.use_lvt_names
            && let Some(lvt) = &self.lvt
        {
            lvt.get_var_type()
        } else if let Some(ty) = &self.var_type
            && ty.ty != CodeType::Unknown
        {
            ty.clone()
        } else if let Some(owner) = self.processor {
            let pair = self.pair();
            let processor = &cx.ir[owner];
            let inferred = processor.versions.lower.get(&pair);
            if let Some(name) = processor.this_vars.get(&pair) {
                if let Some(signature) = cx
                    .classes()
                    .get_class(name)
                    .and_then(|class| class.signature())
                {
                    return signature.generic_type.clone();
                }
                if inferred.is_none() {
                    return VarType::with_value(CodeType::Object, 0, name.clone());
                }
            }
            inferred.cloned().unwrap_or(VarType::VARTYPE_UNKNOWN)
        } else {
            VarType::VARTYPE_UNKNOWN
        }
    }

    /// A definition's type during method processing, before a MethodWrapper is active.
    pub(crate) fn definition_var_type(&self, cx: &Cx) -> VarType {
        if cx.options.use_lvt_names
            && cx.options.decompile_generics
            && let Some(local) = &self.lvt
            && let Some(signature) = local.get_signature()
            && let Some(mut descriptor) = generic_main::parse_field_signature(signature)
        {
            descriptor.verify_loosely(cx, &local.get_var_type());
            return descriptor.ty;
        }
        self.expr_type(cx)
    }

    /// `VarExprent.getInferredExprType(null)` prefers the local's generic signature.
    pub(crate) fn inferred_expr_type(&self, cx: &Cx) -> VarType {
        if let Some(lvt) = &self.lvt {
            match lvt.get_signature() {
                Some(signature) => {
                    if let Some(descriptor) = generic_main::parse_field_signature(signature) {
                        return descriptor.ty;
                    }
                }
                None => return lvt.get_var_type(),
            }
        }
        self.expr_type(cx)
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
    pub force_boxing: bool,
    pub can_ignore_boxing: bool,
    pub generics: Option<Box<InvocationGenerics>>,
}

impl Invocation {
    /// The first LambdaMetafactory bootstrap argument is the erased SAM descriptor.
    pub(crate) fn lambda_sam_descriptor(&self) -> std::io::Result<&str> {
        match self
            .bootstrap_arguments
            .as_ref()
            .and_then(|args| args.first())
        {
            Some(Some(PooledConstant::Primitive(descriptor))) => Ok(descriptor.get_string()),
            _ => Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "Missing LambdaMetafactory SAM descriptor",
            )),
        }
    }

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
            force_boxing: false,
            can_ignore_boxing: true,
            generics: None,
        }
    }

    pub fn string_descriptor(&self) -> &str {
        self.descriptor.as_str()
    }

    /// `InvocationExprent.isBoxingCall`.
    pub(crate) fn is_boxing_call(&self, cx: &Cx) -> bool {
        let [parameter] = self.parameters.as_slice() else {
            return false;
        };
        let Some(class) = self.classname.as_ref() else {
            return false;
        };
        if !self.is_static || self.name != "valueOf" {
            return false;
        }
        let ty = Expr::expr_type(cx, *parameter);
        let Some(unboxed) = VarType::with_value(CodeType::Object, 0, class.clone()).unboxing_type()
        else {
            return false;
        };

        // Integer constants can have a narrower or ambiguous type.
        if matches!(cx.ir[*parameter].kind, ExprKind::Constant { .. })
            && (ty.type_family == TypeFamily::Integer && unboxed.ty == CodeType::Int
                || matches!(ty.ty, CodeType::Bytechar | CodeType::Shortchar)
                    && matches!(unboxed.ty, CodeType::Char | CodeType::Short))
        {
            return true;
        }
        let primitive = match ty.ty {
            CodeType::Bytechar => CodeType::Byte,
            CodeType::Shortchar => CodeType::Short,
            primitive => primitive,
        };
        unboxed.ty == primitive
    }

    /// `InvocationExprent.isUnboxingCall`.
    pub(crate) fn is_unboxing_call(&self) -> bool {
        let wrapper = match self.name.as_str() {
            "booleanValue" => "java/lang/Boolean",
            "byteValue" => "java/lang/Byte",
            "shortValue" => "java/lang/Short",
            "intValue" => "java/lang/Integer",
            "longValue" => "java/lang/Long",
            "floatValue" => "java/lang/Float",
            "doubleValue" => "java/lang/Double",
            "charValue" => "java/lang/Character",
            _ => return false,
        };
        !self.is_static && self.parameters.is_empty() && self.classname.as_deref() == Some(wrapper)
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
                Self::Copied(switch.case_values().map(<[_]>::to_vec).collect())
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
            write_flags: WriteFlags::empty(),
            id: counters.get_counter_and_increment(EXPRESSION_COUNTER),
            kind,
            bytecode,
        })
    }

    /// Class-level rewrites use the counter still active in DecompilerContext.
    pub(crate) fn new_ambient(
        cx: &mut Cx,
        kind: ExprKind,
        bytecode: Option<BytecodeOffsets>,
    ) -> ExprId {
        cx.ir.exprs.push(Self {
            write_flags: WriteFlags::empty(),
            id: cx.expression_ids.next(),
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
                needs_cast: true,
            },
            bytecode,
        )
    }

    /// Allocate a record pattern after its component expressions have been built.
    /// Each component is a variable or another record pattern.
    pub fn record_pattern(
        ir: &mut Ir,
        counters: &mut CounterContainer,
        class: Arc<StructClass>,
        var_type: VarType,
        children: Vec<ExprId>,
    ) -> ExprId {
        let id = counters.get_counter_and_increment(EXPRESSION_COUNTER);
        assert!(
            children
                .iter()
                .all(|&expr| matches!(ir[expr].kind, ExprKind::Variable(_) | ExprKind::Pattern(_))),
            "Illegal input for PatternExprent"
        );
        let bound_types = vec![None; children.len()];
        ir.exprs.push(Self {
            write_flags: WriteFlags::empty(),
            id,
            kind: ExprKind::Pattern(Box::new(Pattern {
                class,
                var_type,
                children,
                bound_types,
            })),
            bytecode: None,
        })
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
            var_type = Self::class_literal_type(name.as_utf8_lossy());
        }
        ExprKind::Constant {
            value,
            var_type,
            bool_permitted: false,
            was_condy,
        }
    }

    /// ConstExprent gives a class literal the expression type Class<T>.
    pub(crate) fn class_literal_type(name: &str) -> VarType {
        let class = VarType::VARTYPE_CLASS;
        let argument = VarType::from_signature_cl(name, !name.starts_with('['));
        VarType::generic(
            class.ty,
            class.array_dim,
            class.value,
            None,
            vec![Some(argument)],
            GenericType::WILDCARD_NO,
        )
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
            write_flags: WriteFlags::empty(),
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
                generics: None,
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
                ..
            } => op.expr_type(cx, operands, implicit_type.as_deref()),
            ExprKind::Pattern(pattern) => pattern.var_type.clone(),
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
            ExprKind::Switch { var_type, .. }
            | ExprKind::Yield {
                return_type: var_type,
                ..
            } => var_type.clone(),
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
                variable.var_type = Some(variable.expr_type(cx));
                variable.backing_instruction = None;
                variable.bound_type = None;
                variable.intersection_type = false;
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
                invocation.force_boxing = false;
                invocation.generics = None;
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
            ExprKind::Function {
                operands,
                needs_cast,
                ..
            } => {
                copy_entries(cx, counters, operands);
                *needs_cast = true;
            }
            ExprKind::Pattern(pattern) => {
                copy_entries(cx, counters, &mut pattern.children);
                return Self::record_pattern(
                    &mut cx.ir,
                    counters,
                    Arc::clone(&pattern.class),
                    pattern.var_type.clone(),
                    std::mem::take(&mut pattern.children),
                );
            }
            ExprKind::New {
                new_type,
                dimensions,
                constructor,
                array_elements,
                lambda,
                method_reference,
                generics,
                ..
            } => {
                *generics = None;
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
            ExprKind::Switch { .. } => bytecode = None,
            ExprKind::Yield { value, .. } => {
                *value = Self::copy(cx, counters, *value);
                bytecode = None;
            }
        }
        // NewExprent.copy keeps enumConst; the other writing flags start clear.
        let write_flags = if matches!(kind, ExprKind::New { .. }) {
            cx.ir[expr].write_flags & WriteFlags::ENUM_CONST
        } else {
            WriteFlags::empty()
        };
        cx.ir.exprs.push(Self {
            write_flags,
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
