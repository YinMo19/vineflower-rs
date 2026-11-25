// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Lifts the instructions in one basic block to expression trees and
//! assignments to the synthetic variables that stand for the operand stack.

use std::io;
use std::sync::Arc;

use crate::code::Instruction;
use crate::code::code_constants::*;
use crate::decompiler::exps::{
    BytecodeOffsets, ExitType, Expr, ExprKind, Field, FunctionType, Invocation, InvocationFunction,
    InvocationType, MonitorType, STACK_BASE, Variable,
};
use crate::decompiler::ir::{ExprId, StatId};
use crate::decompiler::stats::StatementKind;
use crate::engine::Cx;
use crate::engine::counter_container::CounterContainer;
use crate::structs::consts::{ConstantPool, ConstantValue, LinkConstant, PooledConstant};
use crate::structs::{StructClass, StructMethod};
use crate::types::{CodeType, MethodDescriptor, VarType};

use super::{ExpressionData, condy};

const LOCAL_TYPES: [VarType; 5] = [
    VarType::VARTYPE_INT,
    VarType::VARTYPE_LONG,
    VarType::VARTYPE_FLOAT,
    VarType::VARTYPE_DOUBLE,
    VarType::VARTYPE_OBJECT,
];

const ARRAY_TYPES: [VarType; 8] = [
    VarType::VARTYPE_INT,
    VarType::VARTYPE_LONG,
    VarType::VARTYPE_FLOAT,
    VarType::VARTYPE_DOUBLE,
    VarType::VARTYPE_OBJECT,
    VarType::VARTYPE_BOOLEAN,
    VarType::VARTYPE_CHAR,
    VarType::VARTYPE_SHORT,
];

const NEWARRAY_TYPES: [CodeType; 8] = [
    CodeType::Boolean,
    CodeType::Char,
    CodeType::Float,
    CodeType::Double,
    CodeType::Byte,
    CodeType::Short,
    CodeType::Int,
    CodeType::Long,
];

const ARITHMETIC: [FunctionType; 5] = [
    FunctionType::Add,
    FunctionType::Sub,
    FunctionType::Mul,
    FunctionType::Div,
    FunctionType::Rem,
];

const SHIFT_AND_BITWISE: [FunctionType; 6] = [
    FunctionType::Shl,
    FunctionType::Shr,
    FunctionType::Ushr,
    FunctionType::And,
    FunctionType::Or,
    FunctionType::Xor,
];

const CONVERSIONS: [FunctionType; 15] = [
    FunctionType::I2l,
    FunctionType::I2f,
    FunctionType::I2d,
    FunctionType::L2i,
    FunctionType::L2f,
    FunctionType::L2d,
    FunctionType::F2i,
    FunctionType::F2l,
    FunctionType::F2d,
    FunctionType::D2i,
    FunctionType::D2l,
    FunctionType::D2f,
    FunctionType::I2b,
    FunctionType::I2c,
    FunctionType::I2s,
];

const COMPARISONS: [FunctionType; 5] = [
    FunctionType::Lcmp,
    FunctionType::Fcmpl,
    FunctionType::Fcmpg,
    FunctionType::Dcmpl,
    FunctionType::Dcmpg,
];

// A structured if tests the condition for continuing after the branch.
const INVERTED_BRANCH: [FunctionType; 8] = [
    FunctionType::Ne,
    FunctionType::Eq,
    FunctionType::Ge,
    FunctionType::Lt,
    FunctionType::Le,
    FunctionType::Gt,
    FunctionType::Ne,
    FunctionType::Eq,
];

pub(super) fn process_block(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    stat: StatId,
    data: &mut ExpressionData,
    class: &StructClass,
    method: &StructMethod,
    descriptor: &Arc<MethodDescriptor>,
) -> io::Result<()> {
    let StatementKind::BasicBlock { block } = cx.ir[stat].kind else {
        return Err(invalid_data("expression processing requires a basic block"));
    };
    let removable_monitorexit = cx.ir[stat].removable_monitorexit;
    let mut processor = BlockProcessor {
        cx,
        counters,
        data,
        class,
        method,
        descriptor,
    };
    let length = processor.cx.ir[block].seq.length();

    for i in 0..length {
        let block = &processor.cx.ir[block];
        let instruction = Arc::clone(block.get_instruction(i));
        let old_offset = block.get_old_offset(i);
        let next_opcode = (i + 1 < length).then(|| block.get_instruction(i + 1).opcode);
        processor
            .process_instruction(&instruction, old_offset, next_opcode, removable_monitorexit)
            .map_err(|error| {
                invalid_data(format!(
                    "{}.{}{} at bytecode offset {old_offset} ({instruction}): {error}",
                    class.qualified_name, method.name, method.descriptor,
                ))
            })?;
    }

    Ok(())
}

struct BlockProcessor<'a> {
    cx: &'a mut Cx,
    counters: &'a mut CounterContainer,
    data: &'a mut ExpressionData,
    class: &'a StructClass,
    method: &'a StructMethod,
    descriptor: &'a Arc<MethodDescriptor>,
}

impl BlockProcessor<'_> {
    fn process_instruction(
        &mut self,
        instruction: &Arc<Instruction>,
        old_offset: i32,
        next_opcode: Option<i32>,
        removable_monitorexit: bool,
    ) -> io::Result<()> {
        let opcode = instruction.opcode;
        let offsets = BytecodeOffsets::for_instruction(old_offset, instruction.length);
        let local_end = old_offset + instruction.length;

        match opcode {
            OPC_ACONST_NULL => {
                self.push_kind(
                    Expr::constant(VarType::VARTYPE_NULL, ConstantValue::Null, false),
                    offsets,
                    None,
                );
            }
            OPC_BIPUSH | OPC_SIPUSH => {
                self.push_kind(
                    Expr::int_constant(operand(instruction, 0)?, true),
                    offsets,
                    None,
                );
            }
            OPC_LCONST_0..=OPC_LCONST_1 => {
                self.push_kind(
                    Expr::constant(
                        VarType::VARTYPE_LONG,
                        ConstantValue::Long(i64::from(opcode - OPC_LCONST_0)),
                        false,
                    ),
                    offsets,
                    None,
                );
            }
            OPC_FCONST_0..=OPC_FCONST_2 => {
                self.push_kind(
                    Expr::constant(
                        VarType::VARTYPE_FLOAT,
                        ConstantValue::Float((opcode - OPC_FCONST_0) as f32),
                        false,
                    ),
                    offsets,
                    None,
                );
            }
            OPC_DCONST_0..=OPC_DCONST_1 => {
                self.push_kind(
                    Expr::constant(
                        VarType::VARTYPE_DOUBLE,
                        ConstantValue::Double(f64::from(opcode - OPC_DCONST_0)),
                        false,
                    ),
                    offsets,
                    None,
                );
            }
            OPC_LDC..=OPC_LDC2_W => self.load_constant(instruction, offsets)?,
            OPC_ILOAD..=OPC_ALOAD => {
                let ty = LOCAL_TYPES[(opcode - OPC_ILOAD) as usize].clone();
                let var = self.local(instruction, ty, local_end, offsets)?;
                self.push(var, None);
            }
            OPC_IALOAD..=OPC_SALOAD => {
                let index = self.pop()?;
                let array = self.pop()?;
                let hard_type = ARRAY_TYPES[(opcode - OPC_IALOAD) as usize].clone();
                let ty = match opcode {
                    OPC_LALOAD => Some(VarType::VARTYPE_LONG),
                    OPC_DALOAD => Some(VarType::VARTYPE_DOUBLE),
                    _ => None,
                };
                self.push_kind(
                    ExprKind::Array {
                        array,
                        index,
                        hard_type,
                    },
                    offsets,
                    ty,
                );
            }
            OPC_ISTORE..=OPC_ASTORE => {
                let value = self.pop()?;
                let ty = LOCAL_TYPES[(opcode - OPC_ISTORE) as usize].clone();
                let var = self.local(instruction, ty, local_end, offsets.clone())?;
                self.assign(var, value, offsets);
            }
            OPC_IASTORE..=OPC_SASTORE => {
                let value = self.pop()?;
                let index = self.pop()?;
                let array = self.pop()?;
                let hard_type = ARRAY_TYPES[(opcode - OPC_IASTORE) as usize].clone();
                let target = self.new_expr(
                    ExprKind::Array {
                        array,
                        index,
                        hard_type,
                    },
                    offsets.clone(),
                );
                self.assign(target, value, offsets);
            }
            OPC_IADD..=OPC_DREM => {
                self.push_function(ARITHMETIC[((opcode - OPC_IADD) / 4) as usize], 2, offsets)?;
            }
            OPC_INEG..=OPC_DNEG => self.push_function(FunctionType::Neg, 1, offsets)?,
            OPC_ISHL..=OPC_LXOR => {
                self.push_function(
                    SHIFT_AND_BITWISE[((opcode - OPC_ISHL) / 2) as usize],
                    2,
                    offsets,
                )?;
            }
            OPC_IINC => {
                let increment = operand(instruction, 1)?;
                let var = self.local(
                    instruction,
                    VarType::VARTYPE_INT,
                    local_end,
                    offsets.clone(),
                )?;
                let input = Expr::copy(self.cx, self.counters, var);
                let magnitude = self.new_expr(
                    Expr::constant(
                        VarType::VARTYPE_INT,
                        ConstantValue::Integer(increment.wrapping_abs()),
                        false,
                    ),
                    None,
                );
                let op = if increment < 0 {
                    FunctionType::Sub
                } else {
                    FunctionType::Add
                };
                let value = Expr::function(
                    &mut self.cx.ir,
                    self.counters,
                    op,
                    vec![input, magnitude],
                    offsets.clone(),
                );
                self.assign(var, value, offsets);
            }
            OPC_I2L..=OPC_I2S => {
                self.push_function(CONVERSIONS[(opcode - OPC_I2L) as usize], 1, offsets)?;
            }
            OPC_LCMP..=OPC_DCMPG => {
                self.push_function(COMPARISONS[(opcode - OPC_LCMP) as usize], 2, offsets)?;
            }
            OPC_IFEQ..=OPC_IFLE => {
                self.branch(
                    INVERTED_BRANCH[(opcode - OPC_IFEQ) as usize],
                    Some(Expr::int_constant(0, true)),
                    offsets,
                )?;
            }
            OPC_IF_ICMPEQ..=OPC_IF_ACMPNE => {
                self.branch(
                    INVERTED_BRANCH[(opcode - OPC_IF_ICMPEQ) as usize],
                    None,
                    offsets,
                )?;
            }
            OPC_IFNULL | OPC_IFNONNULL => {
                self.branch(
                    if opcode == OPC_IFNULL {
                        FunctionType::Ne
                    } else {
                        FunctionType::Eq
                    },
                    Some(Expr::constant(
                        VarType::VARTYPE_NULL,
                        ConstantValue::Null,
                        false,
                    )),
                    offsets,
                )?;
            }
            OPC_TABLESWITCH | OPC_LOOKUPSWITCH => {
                let value = self.pop()?;
                let head = self.new_expr(
                    ExprKind::SwitchHead {
                        value,
                        case_values: None,
                    },
                    offsets,
                );
                self.data.expressions.push(head);
            }
            OPC_IRETURN..=OPC_RETURN | OPC_ATHROW => {
                let value = if opcode == OPC_RETURN {
                    None
                } else {
                    Some(self.pop()?)
                };
                let (kind, return_type) = if opcode == OPC_ATHROW {
                    (ExitType::Throw, None)
                } else {
                    (ExitType::Return, Some(self.descriptor.ret.clone()))
                };
                let exit = self.new_expr(
                    ExprKind::Exit {
                        kind,
                        value,
                        return_type,
                        method_descriptor: Arc::clone(self.descriptor),
                    },
                    offsets,
                );
                self.data.expressions.push(exit);
            }
            OPC_MONITORENTER | OPC_MONITOREXIT => {
                let value = self.pop()?;
                let kind = if opcode == OPC_MONITORENTER {
                    MonitorType::Enter
                } else {
                    MonitorType::Exit
                };
                let remove = opcode == OPC_MONITOREXIT && removable_monitorexit;
                let monitor = self.new_expr(
                    ExprKind::Monitor {
                        kind,
                        value,
                        remove,
                    },
                    offsets,
                );
                self.data.expressions.push(monitor);
            }
            OPC_CHECKCAST | OPC_INSTANCEOF => {
                let ty = class_type(&self.class.pool, operand(instruction, 0)?)?;
                let target = self.new_expr(Expr::constant(ty, ConstantValue::Null, false), None);
                self.data.stack.push(target);
                let op = if opcode == OPC_CHECKCAST {
                    FunctionType::Cast
                } else {
                    FunctionType::InstanceOf
                };
                self.push_function(op, 2, offsets)?;
            }
            OPC_ARRAYLENGTH => self.push_function(FunctionType::ArrayLength, 1, offsets)?,
            OPC_GETSTATIC..=OPC_PUTFIELD => {
                let value = if matches!(opcode, OPC_PUTSTATIC | OPC_PUTFIELD) {
                    Some(self.pop()?)
                } else {
                    None
                };
                let field = link(&self.class.pool, operand(instruction, 0)?)?;
                let instance = if matches!(opcode, OPC_GETFIELD | OPC_PUTFIELD) {
                    Some(self.pop()?)
                } else {
                    None
                };
                let field = ExprKind::Field(Box::new(Field::from_link(&field, instance)));
                if let Some(value) = value {
                    let target = self.new_expr(field, offsets.clone());
                    self.assign(target, value, offsets);
                } else {
                    self.push_kind(field, offsets, None);
                }
            }
            OPC_INVOKEVIRTUAL..=OPC_INVOKEDYNAMIC => {
                if opcode != OPC_INVOKEDYNAMIC || instruction.bytecode_version.has_invoke_dynamic()
                {
                    let constant = link(&self.class.pool, operand(instruction, 0)?)?;
                    self.invoke(opcode, &constant, offsets, false)?;
                }
            }
            OPC_NEW | OPC_ANEWARRAY | OPC_MULTIANEWARRAY => {
                let dimensions = match opcode {
                    OPC_NEW => 0,
                    OPC_ANEWARRAY => 1,
                    _ => operand(instruction, 1)?,
                };
                let mut ty = class_type(&self.class.pool, operand(instruction, 0)?)?;
                if opcode != OPC_MULTIANEWARRAY {
                    ty = ty.resize_array_dim(ty.array_dim + dimensions);
                }
                self.allocate(ty, dimensions, offsets)?;
            }
            OPC_NEWARRAY => {
                let tag = operand(instruction, 0)?;
                let code_type = NEWARRAY_TYPES
                    .get(tag.wrapping_sub(4) as usize)
                    .ok_or_else(|| invalid_data(format!("invalid newarray type {tag}")))?;
                self.allocate(VarType::with_dim(*code_type, 1), 1, offsets)?;
            }
            OPC_DUP => self.duplicate(1)?,
            OPC_DUP_X1 => self.insert_copy(2, 1)?,
            OPC_DUP_X2 => {
                let depth = if self.stack_size(2)? == 2 { 2 } else { 3 };
                self.insert_copy(depth, 1)?;
            }
            OPC_DUP2 => {
                if self.stack_size(1)? == 2 {
                    self.duplicate(1)?;
                } else {
                    self.duplicate(2)?;
                    self.duplicate(2)?;
                }
            }
            OPC_DUP2_X1 => {
                if self.stack_size(1)? == 2 {
                    self.insert_copy(2, 1)?;
                } else {
                    self.insert_copy(3, 2)?;
                    self.insert_copy(3, 1)?;
                }
            }
            OPC_DUP2_X2 => {
                if self.stack_size(1)? == 2 {
                    let depth = if self.stack_size(2)? == 2 { 2 } else { 3 };
                    self.insert_copy(depth, 1)?;
                } else {
                    let depth = if self.stack_size(3)? == 2 { 3 } else { 4 };
                    self.insert_copy(depth, 2)?;
                    self.insert_copy(depth, 1)?;
                }
            }
            OPC_SWAP => {
                self.insert_copy(2, 1)?;
                self.pop()?;
            }
            OPC_POP => {
                self.pop()?;
                if let Some(next_opcode) = next_opcode {
                    self.mark_synthetic_null_check(next_opcode);
                }
            }
            OPC_POP2 => {
                if self.stack_size(1)? == 1 {
                    self.pop()?;
                }
                self.pop()?;
            }
            // The instruction parser normalizes the short constant and local
            // opcodes. Control-transfer-only and other ignored opcodes are left
            // to their earlier CFG passes, as in processBlock.
            _ => {}
        }

        Ok(())
    }

    fn new_expr(&mut self, kind: ExprKind, offsets: Option<BytecodeOffsets>) -> ExprId {
        Expr::new(&mut self.cx.ir, self.counters, kind, offsets)
    }

    fn load_constant(
        &mut self,
        instruction: &Instruction,
        offsets: Option<BytecodeOffsets>,
    ) -> io::Result<()> {
        match constant_at(&self.class.pool, operand(instruction, 0)?)? {
            Some(PooledConstant::Primitive(constant)) => {
                let ty = match constant.ty {
                    CONSTANT_INTEGER => VarType::VARTYPE_INT,
                    CONSTANT_FLOAT => VarType::VARTYPE_FLOAT,
                    CONSTANT_LONG => VarType::VARTYPE_LONG,
                    CONSTANT_DOUBLE => VarType::VARTYPE_DOUBLE,
                    CONSTANT_CLASS => VarType::VARTYPE_CLASS,
                    CONSTANT_STRING => VarType::VARTYPE_STRING,
                    9..=15 => VarType::VARTYPE_VOID,
                    CONSTANT_METHODTYPE => VarType::VARTYPE_METHODTYPE,
                    tag => return Err(invalid_data(format!("invalid ldc constant tag {tag}"))),
                };
                let kind = Expr::constant(ty, constant.value.clone(), false);
                self.push_kind(kind, offsets, None);
            }
            Some(PooledConstant::Link(constant)) if constant.ty == CONSTANT_DYNAMIC => {
                self.invoke(instruction.opcode, constant, offsets, true)?;
            }
            Some(PooledConstant::Link(constant)) => {
                // Upstream treats other links as string constants.
                let value = ConstantValue::String(constant.elementname.as_str().into());
                self.push_kind(
                    Expr::constant(VarType::VARTYPE_STRING, value, false),
                    offsets,
                    None,
                );
            }
            None => {}
        }
        Ok(())
    }

    fn local(
        &mut self,
        instruction: &Arc<Instruction>,
        ty: VarType,
        end: i32,
        offsets: Option<BytecodeOffsets>,
    ) -> io::Result<ExprId> {
        let index = operand(instruction, 0)?;
        let mut var = Variable::new(index, ty);
        var.backing_instruction = Some(Arc::clone(instruction));
        var.lvt = self
            .method
            .get_local_variable_attr()
            .and_then(|table| table.get_variable_at_start(index, end));
        Ok(self.new_expr(ExprKind::Variable(var), offsets))
    }

    fn push_function(
        &mut self,
        op: FunctionType,
        arity: usize,
        offsets: Option<BytecodeOffsets>,
    ) -> io::Result<()> {
        let operands = take_operands(&mut self.data.stack, arity)?;
        let expr = Expr::function(&mut self.cx.ir, self.counters, op, operands, offsets);
        self.push(expr, None);
        Ok(())
    }

    fn branch(
        &mut self,
        op: FunctionType,
        implicit: Option<ExprKind>,
        offsets: Option<BytecodeOffsets>,
    ) -> io::Result<()> {
        let mut operands =
            take_operands(&mut self.data.stack, if implicit.is_some() { 1 } else { 2 })?;
        let branch = Expr::new_if(
            &mut self.cx.ir,
            self.counters,
            offsets.clone(),
            |ir, counters| {
                if let Some(kind) = implicit {
                    operands.push(Expr::new(ir, counters, kind, None));
                }
                Expr::function(ir, counters, op, operands, offsets)
            },
        );
        self.data.expressions.push(branch);
        Ok(())
    }

    fn mark_synthetic_null_check(&mut self, next_opcode: i32) {
        if !matches!(next_opcode, OPC_ACONST_NULL..=OPC_LDC2_W | OPC_ASTORE | OPC_ASTORE_0..=OPC_ASTORE_3)
        {
            return;
        }
        let Some(&last) = self.data.expressions.last() else {
            return;
        };
        let ExprKind::Assignment { right, .. } = self.cx.ir[last].kind else {
            return;
        };
        let ExprKind::Invocation(invocation) = &mut self.cx.ir[right].kind else {
            return;
        };
        if !invocation.is_static
            && invocation.name.as_str() == "getClass"
            && invocation.string_descriptor() == "()Ljava/lang/Class;"
            || invocation.is_static
                && invocation.classname.as_deref() == Some("java/util/Objects")
                && invocation.name.as_str() == "requireNonNull"
                && invocation.string_descriptor() == "(Ljava/lang/Object;)Ljava/lang/Object;"
        {
            invocation.synthetic_null_check = true;
        }
    }

    fn invoke(
        &mut self,
        opcode: i32,
        constant: &LinkConstant,
        offsets: Option<BytecodeOffsets>,
        simplify_condy: bool,
    ) -> io::Result<()> {
        let invocation = invocation(
            self.cx,
            self.counters,
            self.class,
            opcode,
            constant,
            &mut self.data.stack,
            offsets,
        )?;
        if Expr::expr_type(self.cx, invocation).ty == CodeType::Void {
            self.data.expressions.push(invocation);
        } else {
            let value = if simplify_condy {
                condy::simplify(self.cx, self.counters, self.class, invocation)?
            } else {
                invocation
            };
            self.push(value, None);
        }
        Ok(())
    }

    fn allocate(
        &mut self,
        new_type: VarType,
        dimensions: i32,
        offsets: Option<BytecodeOffsets>,
    ) -> io::Result<()> {
        let dimensions =
            usize::try_from(dimensions).map_err(|_| invalid_data("negative array dimensions"))?;
        let dimensions = take_operands(&mut self.data.stack, dimensions)?;
        let value = Expr::new_allocation(self.cx, self.counters, new_type, dimensions, offsets);
        self.push(value, None);
        Ok(())
    }

    fn pop(&mut self) -> io::Result<ExprId> {
        pop(&mut self.data.stack)
    }

    fn assign(&mut self, left: ExprId, right: ExprId, offsets: Option<BytecodeOffsets>) {
        let assignment = self.new_expr(
            ExprKind::Assignment {
                left,
                right,
                compound: None,
            },
            offsets,
        );
        self.data.expressions.push(assignment);
    }

    fn assign_stack(&mut self, index: i32, value: ExprId, ty: Option<VarType>) -> ExprId {
        let ty = ty.unwrap_or_else(|| Expr::expr_type(self.cx, value));
        let var = Expr::new_stack_variable(&mut self.cx.ir, self.counters, index, ty);
        self.assign(var, value, None);
        Expr::copy(self.cx, self.counters, var)
    }

    fn push(&mut self, value: ExprId, ty: Option<VarType>) {
        let index = STACK_BASE + self.data.stack.len() as i32;
        let var = self.assign_stack(index, value, ty);
        self.data.stack.push(var);
    }

    fn push_kind(&mut self, kind: ExprKind, offsets: Option<BytecodeOffsets>, ty: Option<VarType>) {
        let value = self.new_expr(kind, offsets);
        self.push(value, ty);
    }

    fn stack_size(&self, depth: usize) -> io::Result<i32> {
        Ok(Expr::expr_type(self.cx, from_top(&self.data.stack, depth)?).stack_size)
    }

    fn duplicate(&mut self, depth: usize) -> io::Result<()> {
        let value = from_top(&self.data.stack, depth)?;
        let copy = Expr::copy(self.cx, self.counters, value);
        self.push(copy, None);
        Ok(())
    }

    /// `insertByOffsetEx`: move the affected stack entries into new
    /// temporaries in top-to-bottom order, freeing a slot for the copy.
    fn insert_copy(&mut self, depth: usize, copy_depth: usize) -> io::Result<()> {
        let base = STACK_BASE + self.data.stack.len() as i32;
        let stack_tail = take_operands(&mut self.data.stack, depth)?;
        let mut shifted = Vec::with_capacity(depth);
        for (offset, value) in stack_tail.into_iter().rev().enumerate() {
            shifted.push(self.assign_stack(base - offset as i32, value, None));
        }

        let value = Expr::copy(self.cx, self.counters, shifted[copy_depth - 1]);
        let insert = self.assign_stack(base - depth as i32, value, None);
        self.data.stack.push(insert);
        self.data.stack.extend(shifted.into_iter().rev());
        Ok(())
    }
}

pub(super) fn invocation(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    class: &StructClass,
    opcode: i32,
    constant: &LinkConstant,
    stack: &mut Vec<ExprId>,
    offsets: Option<BytecodeOffsets>,
) -> io::Result<ExprId> {
    let kind = match opcode {
        OPC_INVOKEVIRTUAL => InvocationType::Virtual,
        OPC_INVOKESPECIAL => InvocationType::Special,
        OPC_INVOKESTATIC => InvocationType::Static,
        OPC_INVOKEINTERFACE => InvocationType::Interface,
        OPC_INVOKEDYNAMIC => InvocationType::Dynamic,
        OPC_LDC..=OPC_LDC2_W => InvocationType::ConstantDynamic,
        _ => return Err(invalid_data(format!("invalid invocation opcode {opcode}"))),
    };
    let mut classname = constant.classname.clone();
    let mut bootstrap_method = None;
    let mut bootstrap_arguments: Option<Arc<[Option<PooledConstant>]>> = None;
    let mut dynamic_class_suffix = None;
    if matches!(
        kind,
        InvocationType::Dynamic | InvocationType::ConstantDynamic
    ) {
        let bootstrap = class
            .attributes
            .bootstrap_methods
            .as_ref()
            .ok_or_else(|| invalid_data("missing BootstrapMethods attribute"))?;
        let index = constant.index1 as usize;
        let method = bootstrap
            .method_refs
            .get(index)
            .ok_or_else(|| invalid_data(format!("missing bootstrap method {index}")))?;
        let arguments = bootstrap.method_arguments.get(index).ok_or_else(|| {
            invalid_data(format!("missing arguments for bootstrap method {index}"))
        })?;
        let prefix = if kind == InvocationType::Dynamic {
            "Lambda"
        } else {
            "Condy"
        };
        dynamic_class_suffix =
            Some(format!("##{prefix}_{}_{}", constant.index1, constant.index2).into());
        classname = method.classname.clone();
        bootstrap_method = Some(method.clone());
        bootstrap_arguments = Some(Arc::from(arguments.as_slice()));
    }

    let function = match constant.elementname.as_str() {
        "<init>" => InvocationFunction::Init,
        "<clinit>" => InvocationFunction::Clinit,
        _ => InvocationFunction::General,
    };
    let descriptor = Arc::new(if kind == InvocationType::ConstantDynamic {
        MethodDescriptor::parse_descriptor(&format!("(){}", constant.descriptor))
    } else {
        MethodDescriptor::parse_descriptor(&constant.descriptor)
    });
    let parameters = take_operands(stack, descriptor.params.len())?;
    let (is_static, instance) = if let Some(method) = &bootstrap_method {
        // Lambda bootstraps use the second argument for the implementation
        // handle. Other dynamic calls use the bootstrap handle itself.
        let is_static = match bootstrap_arguments.as_deref().and_then(|args| args.get(1)) {
            Some(Some(PooledConstant::Link(handle))) => handle.index1,
            _ => method.index1,
        } == CONSTANT_METHODHANDLE_REF_INVOKESTATIC;
        // The receiver also stays in the parameter list.
        (
            is_static,
            if is_static {
                None
            } else {
                parameters.first().copied()
            },
        )
    } else if opcode == OPC_INVOKESTATIC {
        (true, None)
    } else {
        (false, Some(pop(stack)?))
    };

    let mut invocation = Invocation::new(constant.elementname.clone(), classname, descriptor);
    invocation.kind = kind;
    invocation.function = function;
    invocation.is_static = is_static;
    invocation.instance = instance;
    invocation.dynamic_class_suffix = dynamic_class_suffix;
    invocation.parameters = parameters;
    invocation.bootstrap_method = bootstrap_method;
    invocation.bootstrap_arguments = bootstrap_arguments;
    Ok(Expr::new(
        &mut cx.ir,
        counters,
        ExprKind::Invocation(Box::new(invocation)),
        offsets,
    ))
}

fn invalid_data(message: impl Into<String>) -> io::Error {
    io::Error::new(io::ErrorKind::InvalidData, message.into())
}

fn operand(instruction: &Instruction, index: i32) -> io::Result<i32> {
    if index >= instruction.operands_count() {
        return Err(invalid_data(format!("missing instruction operand {index}")));
    }
    Ok(instruction.operand(index))
}

fn constant_at(pool: &ConstantPool, index: i32) -> io::Result<Option<&PooledConstant>> {
    pool.get_pool()
        .get(index as usize)
        .map(Option::as_ref)
        .ok_or_else(|| invalid_data(format!("missing constant pool entry {index}")))
}

fn link(pool: &ConstantPool, index: i32) -> io::Result<LinkConstant> {
    if !matches!(constant_at(pool, index)?, Some(PooledConstant::Link(_))) {
        return Err(invalid_data(format!(
            "expected link constant at pool entry {index}"
        )));
    }
    // This lookup applies the renamer, unlike the raw lookup used for ldc.
    Ok(pool.get_link_constant(index).unwrap())
}

fn class_type(pool: &ConstantPool, index: i32) -> io::Result<VarType> {
    if !matches!(
        constant_at(pool, index)?,
        Some(PooledConstant::Primitive(constant)) if matches!(constant.value, ConstantValue::String(_))
    ) {
        return Err(invalid_data(format!(
            "expected class name at pool entry {index}"
        )));
    }
    let constant = pool.get_primitive_constant(index).unwrap();
    Ok(VarType::from_signature_cl(constant.get_string(), true))
}

fn pop(stack: &mut Vec<ExprId>) -> io::Result<ExprId> {
    stack
        .pop()
        .ok_or_else(|| invalid_data("operand stack is empty"))
}

fn from_top(stack: &[ExprId], depth: usize) -> io::Result<ExprId> {
    let index = stack
        .len()
        .checked_sub(depth)
        .ok_or_else(|| invalid_data(format!("operand stack needs {depth} values")))?;
    Ok(stack[index])
}

fn take_operands(stack: &mut Vec<ExprId>, count: usize) -> io::Result<Vec<ExprId>> {
    let start = stack
        .len()
        .checked_sub(count)
        .ok_or_else(|| invalid_data(format!("operand stack needs {count} values")))?;
    Ok(stack.split_off(start))
}
