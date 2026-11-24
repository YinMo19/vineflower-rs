// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use super::{
    Bytecode, Code, Expected, Expr, ExprKind, Instruction, JvmType, KotlinError, Literal, Locals, Operand,
    Primitive, Type, ValueParameter, local_load, local_store, logic, pop_value, qualified,
};

#[derive(Debug)]
pub(super) struct Comparison<'a> {
    operand: Expr<'a>,
    target: Target,
    equal_to: Expr<'a>,
}

#[derive(Clone, Copy, Debug)]
enum Target {
    Int,
    String,
}

impl Target {
    fn from_class(class: &str) -> Option<Self> {
        match class {
            "java/lang/Integer" => Some(Self::Int),
            "java/lang/String" => Some(Self::String),
            _ => None,
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::Int => "kotlin/Int",
            Self::String => "kotlin/String",
        }
    }
}

impl Comparison<'_> {
    pub(super) fn write(
        &self,
        out: &mut String,
        expected: Expected<'_>,
        parameters: &[ValueParameter],
        declaration: &str,
        binding: u8,
    ) -> Result<(), KotlinError> {
        if expected.primitive() != Some(Primitive::Boolean)
            && !matches!(expected, Expected::Type(ty, JvmType::Object(owner)) if boxed_boolean(ty, owner))
        {
            return Err(invalid(declaration));
        }
        let parens = binding > logic::EQUALITY;
        if parens {
            out.push('(');
        }
        out.push('(');
        let from = if self.operand.stack_load() == Some(0x15) {
            Expected::Primitive(Primitive::Int)
        } else {
            Expected::Reference
        };
        self.operand.write_at(out, from, parameters, declaration, logic::RELATIONAL + 1)?;
        out.push_str(" as? ");
        qualified(out, self.target.name(), declaration)?;
        out.push_str(") == ");
        let rhs = match self.target {
            Target::Int => Expected::Primitive(Primitive::Int),
            Target::String => Expected::Reference,
        };
        self.equal_to.write_at(out, rhs, parameters, declaration, logic::EQUALITY + 1)?;
        if parens {
            out.push(')');
        }
        Ok(())
    }
}

pub(super) fn lower<'a>(
    bytecode: &Bytecode<'a, '_>,
    instructions: &[Instruction],
    locals: &Locals<'_>,
    code: &Code<'_>,
    (returns, jvm): (&Type, &JvmType),
    declaration: &str,
) -> Result<Option<Expr<'a>>, KotlinError> {
    let boxed = match jvm {
        JvmType::Primitive(Primitive::Boolean) if logic::primitive_type(returns) == Some(Primitive::Boolean) => false,
        JvmType::Object(owner) if boxed_boolean(returns, owner) => true,
        _ => return Ok(None),
    };
    if code.max_stack < 2 || instructions.first().and_then(local_load).is_none() {
        return Ok(None);
    }
    let lower = Lowering { bytecode, locals, max_locals: code.max_locals, boxed, declaration };
    match lower.comparison(instructions) {
        Ok(expression) => Ok(Some(expression)),
        Err(KotlinError::Unsupported { .. }) => Ok(None),
        Err(error) => Err(error),
    }
}

fn boxed_boolean(ty: &Type, owner: &str) -> bool {
    owner == "java/lang/Boolean" && ty.nullable && ty.class_id() == Some("kotlin/Boolean")
}

struct Lowering<'a, 'class, 'data> {
    bytecode: &'a Bytecode<'class, 'data>,
    locals: &'a Locals<'a>,
    max_locals: u16,
    boxed: bool,
    declaration: &'a str,
}

/// Each route reloads the same immutable parameter, possibly by way of a
/// fresh alias after a successful early type test. No call or arbitrary
/// expression is duplicated while projecting the two cast arms into one.
#[derive(Clone, Copy)]
struct OperandSource {
    load: u8,
    parameter: usize,
    slot: u16,
}

impl OperandSource {
    fn expr<'a>(self) -> Expr<'a> {
        Expr { kind: ExprKind::Parameter { index: self.parameter, load: self.load }, depth: 1 }
    }

    fn reads(self, instruction: &Instruction) -> bool {
        local_load(instruction) == Some((self.load, self.slot))
    }
}

struct Guard<'a> {
    condition: Expr<'a>,
    rejected: Expr<'a>,
    source: OperandSource,
}

impl<'a> Lowering<'_, 'a, '_> {
    fn comparison(&self, instructions: &[Instruction]) -> Result<Expr<'a>, KotlinError> {
        let (guard, rest) = self.guard(instructions)?;
        let (alias, rest) = if let (Some(guard), [load, store, rest @ ..]) = (&guard, rest)
            && guard.source.reads(load)
            && let Some((0x3a, slot)) = local_store(store)
            && self.scratch(slot)
        {
            (Some(OperandSource { slot, ..guard.source }), rest)
        } else {
            (None, rest)
        };
        let [load, rest @ ..] = rest else { return Err(self.invalid()); };
        let operand = alias.filter(|source| source.reads(load)).or_else(|| self.parameter(load)).ok_or_else(|| self.invalid())?;
        if alias.is_some_and(|alias| !alias.reads(load)) {
            return Err(self.invalid());
        }
        let [test, branch, reload, rest @ ..] = self.after_possible_box(operand, rest)? else { return Err(self.invalid()); };
        let [cast, jump, null, store, rest @ ..] = self.after_possible_box(operand, rest)? else { return Err(self.invalid()); };
        let class = self.class_operand(test, 0xc1)?.ok_or_else(|| self.invalid())?;
        let target = Target::from_class(class).ok_or_else(|| self.invalid())?;
        if !operand.reads(reload) || self.class_operand(cast, 0xc0)? != Some(class)
            || !branch_to(branch, 0x99, null) || !jump_to(jump, store) || null.opcode != 0x01
        {
            return Err(self.invalid());
        }
        let (0x3a, slot) = local_store(store).filter(|&(_, slot)| self.scratch(slot)).ok_or_else(|| self.invalid())? else {
            return Err(self.invalid());
        };
        let [load, rest @ ..] = rest else { return Err(self.invalid()); };
        if local_load(load) != Some((0x19, slot)) {
            return Err(self.invalid());
        }
        let (right, tail) = match target {
            Target::Int => self.int_equality(rest, slot)?,
            Target::String => self.string_equality(rest)?,
        };
        if !self.boolean_return(tail)? {
            return Err(self.invalid());
        }
        let expr = Expr::new(ExprKind::SafeCastComparison(Box::new(Comparison {
            operand: operand.expr(), target, equal_to: right,
        })), 2, self.declaration)?;
        match guard {
            Some(guard) => logic::Conditional::new(guard.condition, expr, guard.rejected, self.declaration),
            None => Ok(expr),
        }
    }

    fn guard<'ops>(&self, ops: &'ops [Instruction]) -> Result<(Option<Guard<'a>>, &'ops [Instruction]), KotlinError> {
        let (load, nullable, test, tail) = match ops {
            [load, dup, check_null, pop, yes, join, test, branch, ..]
                if dup.opcode == 0x59 && pop.opcode == 0x57 && yes.opcode == 0x04
                    && branch_to(check_null, 0xc7, test) && jump_to(join, branch) =>
            {
                (load, true, test, &ops[7..])
            }
            [load, test, tail @ ..] => (load, false, test, tail),
            _ => return Ok((None, ops)),
        };
        let [branch, value, ret, success, ..] = tail else { return Ok((None, ops)); };
        let Some(class) = self.class_operand(test, 0xc1)? else { return Ok((None, ops)); };
        if Target::from_class(class).is_none() || !branch_to(branch, 0x9a, success) {
            return Ok((None, ops));
        }
        let source = self.parameter(load).filter(|source| source.load == 0x19).ok_or_else(|| self.invalid())?;
        let rejected = match (self.boxed, value.opcode, ret.opcode) {
            (true, 0x01, 0xb0) => Literal::Null,
            (false, 0x03..=0x04, 0xac) => Literal::Int(i32::from(value.opcode - 0x03)),
            _ => return Err(self.invalid()),
        };
        let tested = Expr::new(ExprKind::TypeTest {
            operand: Box::new(source.expr()), target: class, negative: false,
        }, 2, self.declaration)?;
        let condition = if nullable {
            let is_null = logic::Comparison::reference(
                logic::Relation::Same, source.expr(), Expr::literal(Literal::Null), self.declaration,
            )?;
            logic::Conditional::new(is_null, Expr::literal(Literal::Int(1)), tested, self.declaration)?
        } else {
            tested
        };
        Ok((Some(Guard { condition, rejected: Expr::literal(rejected), source }), &tail[3..]))
    }

    fn string_equality<'ops>(&self, ops: &'ops [Instruction]) -> Result<(Expr<'a>, &'ops [Instruction]), KotlinError> {
        let [constant, equality, tail @ ..] = ops else { return Err(self.invalid()); };
        if !self.bytecode.reference_are_equal(equality)? {
            return Err(self.invalid());
        }
        let right = self.literal(constant)?;
        if !matches!(right.kind, ExprKind::Literal(Literal::String(_))) {
            return Err(self.invalid());
        }
        Ok((right, tail))
    }

    fn int_equality<'ops>(&self, ops: &'ops [Instruction], slot: u16) -> Result<(Expr<'a>, &'ops [Instruction]), KotlinError> {
        let [constant, store, dup, present, pop, absent_jump, unbox, reload, not_equal, yes, join, no, tail @ ..] = ops else {
            return Err(self.invalid());
        };
        let Some((0x36, temp)) = local_store(store) else { return Err(self.invalid()); };
        if temp == slot || !self.scratch(temp) || dup.opcode != 0x59 || pop.opcode != 0x57
            || !branch_to(present, 0xc7, unbox) || !jump_to(absent_jump, no)
            || self.bytecode.reference(unbox, 0xb6)? != Some(("java/lang/Integer", "intValue", "()I"))
            || local_load(reload) != Some((0x15, temp)) || !branch_to(not_equal, 0xa0, no)
            || yes.opcode != 0x04 || no.opcode != 0x03 || !tail.first().is_some_and(|ret| jump_to(join, ret))
        {
            return Err(self.invalid());
        }
        let right = self.literal(constant)?;
        if !matches!(right.kind, ExprKind::Literal(Literal::Int(_))) {
            return Err(self.invalid());
        }
        Ok((right, tail))
    }

    fn scratch(&self, slot: u16) -> bool {
        (self.locals.next_slot()..self.max_locals).contains(&slot)
    }

    fn parameter(&self, instruction: &Instruction) -> Option<OperandSource> {
        let (load, slot) = local_load(instruction)?;
        let parameter = self.locals.parameter(slot, load)?;
        (load == 0x19 || load == 0x15 && *self.locals.slots[parameter].1 == JvmType::Primitive(Primitive::Int))
            .then_some(OperandSource { load, parameter, slot })
    }

    fn class_operand(&self, instruction: &Instruction, opcode: u8) -> Result<Option<&'a str>, KotlinError> {
        if instruction.opcode == opcode && let Operand::Constant(index) = instruction.operand {
            Ok(Some(self.bytecode.class.pool.class_name(index)?))
        } else {
            Ok(None)
        }
    }

    fn after_possible_box<'ops>(&self, source: OperandSource, ops: &'ops [Instruction]) -> Result<&'ops [Instruction], KotlinError> {
        if source.load == 0x19 {
            return Ok(ops);
        }
        let [box_value, tail @ ..] = ops else { return Err(self.invalid()); };
        if self.bytecode.reference(box_value, 0xb8)? != Some(("java/lang/Integer", "valueOf", "(I)Ljava/lang/Integer;")) {
            return Err(self.invalid());
        }
        Ok(tail)
    }

    fn boolean_return(&self, ops: &[Instruction]) -> Result<bool, KotlinError> {
        match (self.boxed, ops) {
            (true, [box_value, ret]) => Ok(ret.opcode == 0xb0 && self.bytecode.reference(box_value, 0xb8)?
                == Some(("java/lang/Boolean", "valueOf", "(Z)Ljava/lang/Boolean;"))),
            (false, [ret]) => Ok(ret.opcode == 0xac),
            _ => Ok(false),
        }
    }

    fn literal(&self, instruction: &Instruction) -> Result<Expr<'a>, KotlinError> {
        let mut stack = Vec::new();
        self.bytecode.expression(instruction, self.locals, &mut stack, self.declaration)?;
        let value = pop_value(&mut stack, self.declaration)?;
        if stack.is_empty() { Ok(value) } else { Err(self.invalid()) }
    }

    fn invalid(&self) -> KotlinError {
        invalid(self.declaration)
    }
}

fn invalid(declaration: &str) -> KotlinError {
    KotlinError::unsupported(declaration, "unproven Kotlin safe-cast comparison")
}

fn jump_to(instruction: &Instruction, target: &Instruction) -> bool {
    matches!(instruction.opcode, 0xa7 | 0xc8) && instruction.operand == Operand::Branch(target.offset)
}

fn branch_to(instruction: &Instruction, opcode: u8, target: &Instruction) -> bool {
    instruction.opcode == opcode && instruction.operand == Operand::Branch(target.offset)
}
