// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use crate::cfg::ControlFlowGraph;

use super::{
    Bytecode, Expr, ExprKind, Instruction, JvmType, KotlinError, Literal, Locals, Operand,
    StackValue, ValueParameter, lambdas, logic::{self, Conditional}, pop_value, return_opcode,
    statements::{self, ValueBlock}, tailrec,
};

/// Lower a forward-only expression graph. A structured region either returns
/// directly or produces a single value at its immediate postdominator. The
/// operand stack must be empty *after* each branch condition: a live prefix
/// would need explicit Kotlin temporaries to preserve evaluation order.
pub(super) fn lower<'class>(
    bytecode: &Bytecode<'class, '_>,
    instructions: &[Instruction],
    locals: &Locals<'_>,
    return_type: &JvmType,
    parameters: &[ValueParameter],
    declaration: &str,
    tail: Option<tailrec::Shape>,
) -> Result<(Expr<'class>, Option<(u32, u32)>), KotlinError> {
    let cfg = ControlFlowGraph::build(instructions, &[]).map_err(|_| {
        KotlinError::unsupported(declaration, "invalid Kotlin expression control flow")
    })?;
    if cfg
        .blocks
        .iter()
        .enumerate()
        .any(|(index, block)| block.successors.iter().any(|&next| next <= index))
    {
        return Err(KotlinError::unsupported(
            declaration,
            "loop or backward control transfer",
        ));
    }
    if *return_type == JvmType::Void || cfg.reachable().contains(&false) {
        return Err(KotlinError::unsupported(
            declaration,
            "statement control flow or unreachable code",
        ));
    }
    let postdominators = cfg.immediate_postdominators();
    let materialized = boolean_materialization(&cfg, instructions, return_type);
    // Shared short-circuit arms may be visited once per predecessor. Bound
    // expansion so inputs which don't describe structured regions fail closed.
    let steps = cfg.blocks.len().saturating_mul(4);
    let mut lower = Lowering {
        cfg,
        instructions,
        bytecode,
        locals,
        parameters,
        declaration,
        postdominators,
        return_opcode: return_opcode(return_type),
        tail,
        steps,
    };
    match lower.region(0, None, &mut Vec::new(), None, 0)? {
        Exit::Return(expr) => Ok((expr, materialized)),
        Exit::Join(_) => Err(lower.unsupported("expression path without a return")),
    }
}

/// A single conditional and two constants often implement a bare comparison.
/// The arm instructions are compiler glue when the Kotlin writer folds them;
/// keep the condition itself and the typed return in the source mapping.
fn boolean_materialization(
    cfg: &ControlFlowGraph,
    instructions: &[Instruction],
    ty: &JvmType,
) -> Option<(u32, u32)> {
    if *ty != JvmType::Primitive(super::Primitive::Boolean) {
        return None;
    }
    let [head, yes, no, join] = cfg.blocks.as_slice() else {
        return None;
    };
    if head.successors != [2, 1] || yes.successors != [3] || no.successors != [3] {
        return None;
    }
    let [yes, skip] = &instructions[yes.instructions.clone()] else {
        return None;
    };
    let [no] = &instructions[no.instructions.clone()] else {
        return None;
    };
    let [ret] = &instructions[join.instructions.clone()] else {
        return None;
    };
    (matches!((yes.opcode, no.opcode), (0x03, 0x04) | (0x04, 0x03))
        && matches!(skip.opcode, 0xa7 | 0xc8)
        && ret.opcode == 0xac)
        .then_some((yes.offset, no.offset))
}

struct Lowering<'a, 'class, 'data> {
    cfg: ControlFlowGraph,
    instructions: &'a [Instruction],
    bytecode: &'a Bytecode<'class, 'data>,
    locals: &'a Locals<'a>,
    parameters: &'a [ValueParameter],
    declaration: &'a str,
    postdominators: Vec<Option<usize>>,
    return_opcode: u8,
    tail: Option<tailrec::Shape>,
    steps: usize,
}

enum Exit<'a> {
    Join(Expr<'a>),
    Return(Expr<'a>),
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum RefinedType {
    String,
    Int,
}

/// Lexical facts are available inside a single emitted arm, not at its
/// postdominator. The expression lifter never writes to a parameter slot.
struct ParameterFact<'a> {
    parameter: usize,
    ty: RefinedType,
    parent: Option<&'a Self>,
}

impl ParameterFact<'_> {
    fn contains(mut fact: Option<&Self>, index: usize, ty: RefinedType) -> bool {
        while let Some(current) = fact {
            if current.parameter == index && current.ty == ty {
                return true;
            }
            fact = current.parent;
        }
        false
    }
}

impl<'class> Lowering<'_, 'class, '_> {
    fn region(
        &mut self,
        mut index: usize,
        stop: Option<usize>,
        stack: &mut Vec<StackValue<'class>>,
        facts: Option<&ParameterFact<'_>>,
        depth: usize,
    ) -> Result<Exit<'class>, KotlinError> {
        if depth >= 64 {
            return Err(self.unsupported("Kotlin control flow nesting limit"));
        }
        loop {
            if let Some(stop) = stop {
                if index == stop {
                    return Ok(Exit::Join(self.one_value(stack)?));
                }
                if index > stop {
                    return Err(self.unsupported("branch crosses its Kotlin expression join"));
                }
            }
            self.steps = self
                .steps
                .checked_sub(1)
                .ok_or_else(|| self.unsupported("Kotlin control flow expansion limit"))?;
            let block = &self.cfg.blocks[index];
            let (last, before) = self.instructions[block.instructions.clone()]
                .split_last()
                .unwrap();
            if let Some(tail) = self.tail
                && matches!(last.operand, Operand::Branch(_)) && last.opcode == self.return_opcode
            {
                if stop.is_some() || !stack.is_empty() {
                    return Err(self.unsupported("live operands entering Kotlin tail-recursive updates"));
                }
                return tail.call(self.bytecode, before, self.locals, stack, self.declaration).map(Exit::Return);
            }
            if stop.is_none() && stack.is_empty() && last.opcode == self.return_opcode
                && let Some(value) = self.statement_value(block.instructions.start..block.instructions.end - 1)?
            {
                return Ok(Exit::Return(value));
            }
            if last.opcode == 0xbf && stop.is_none() && stack.is_empty()
                && let Some(throw) = self.throw_value(before)?
            {
                return Ok(Exit::Return(throw));
            }
            for instruction in before {
                self.expression(instruction, stack, facts)?;
            }
            match (last.opcode, &last.operand, block.successors.as_slice()) {
                (0xac..=0xb1, _, []) => {
                    if stop.is_some() || last.opcode != self.return_opcode {
                        return Err(self.unsupported("inconsistent Kotlin return path"));
                    }
                    return Ok(Exit::Return(self.one_value(stack)?));
                }
                (0xa7 | 0xc8, Operand::Branch(_), [next]) => index = *next,
                (0x99..=0xa6 | 0xc6 | 0xc7, Operand::Branch(_), [target, fallthrough]) => {
                    let (target, fallthrough) = (*target, *fallthrough);
                    let guard =
                        logic::condition(last.opcode, stack, self.parameters, self.declaration)?;
                    if !stack.is_empty() {
                        return Err(
                            self.unsupported("live operand stack across Kotlin conditional")
                        );
                    }
                    let join = self.postdominators[index];
                    if stop.is_some_and(|stop| join.is_none_or(|join| join > stop)) {
                        return Err(self.unsupported("crossing Kotlin conditional regions"));
                    }
                    let guarded = self.parameter_fact(&guard, facts);
                    let yes_facts = guarded.as_ref().filter(|(negative, _)| !negative).map(|(_, fact)| fact).or(facts);
                    let no_facts = guarded.as_ref().filter(|(negative, _)| *negative).map(|(_, fact)| fact).or(facts);
                    let yes = self.region(fallthrough, join, stack, yes_facts, depth + 1)?;
                    let no = self.region(target, join, stack, no_facts, depth + 1)?;
                    match (yes, no, join) {
                        (Exit::Return(yes), Exit::Return(no), None) => {
                            return Ok(Exit::Return(Conditional::new(
                                guard,
                                yes,
                                no,
                                self.declaration,
                            )?));
                        }
                        (Exit::Join(yes), Exit::Join(no), Some(join)) => {
                            stack.push(StackValue::Value(Conditional::new(
                                guard,
                                yes,
                                no,
                                self.declaration,
                            )?));
                            index = join;
                        }
                        _ => return Err(self.unsupported("incompatible Kotlin conditional arms")),
                    }
                }
                (_, Operand::Branch(_) | Operand::Switch { .. }, _) => {
                    return Err(self.unsupported("unsupported Kotlin control transfer"));
                }
                (_, _, [next]) => {
                    self.expression(last, stack, facts)?;
                    index = *next;
                }
                _ => return Err(self.unsupported("unterminated Kotlin expression path")),
            }
        }
    }

    fn parameter_fact<'a>(
        &self,
        guard: &Expr<'_>,
        parent: Option<&'a ParameterFact<'a>>,
    ) -> Option<(bool, ParameterFact<'a>)> {
        let (parameter, ty, negative) = match &guard.kind {
            ExprKind::TypeTest { operand, target, negative }
                if let ExprKind::Parameter { index, load: 0x19 } = operand.kind =>
            {
                let ty = match *target {
                    "java/lang/String" => RefinedType::String,
                    "java/lang/Integer" => RefinedType::Int,
                    _ => return None,
                };
                (index, ty, *negative)
            }
            ExprKind::Compare(compare) => {
                let (parameter, positive) = compare.nonnull_parameter()?;
                let ty = &self.parameters[parameter].ty;
                if ty.class_id() != Some("kotlin/Int")
                    || !matches!(self.locals.slots[parameter].1, JvmType::Object(owner) if owner == "java/lang/Integer")
                {
                    return None;
                }
                (parameter, RefinedType::Int, !positive)
            }
            _ => return None,
        };
        Some((negative, ParameterFact { parameter, ty, parent }))
    }

    fn expression(
        &self,
        instruction: &Instruction,
        stack: &mut Vec<StackValue<'class>>,
        facts: Option<&ParameterFact<'_>>,
    ) -> Result<(), KotlinError> {
        if let Some(StackValue::Value(value)) = stack.last_mut()
            && let ExprKind::Parameter { index: parameter, load: 0x19 } = value.kind
        {
            if let (0xc0, Operand::Constant(index)) = (instruction.opcode, &instruction.operand) {
                match self.bytecode.class.pool.class_name(*index)? {
                    "java/lang/String" if ParameterFact::contains(facts, parameter, RefinedType::String) => {
                        value.kind = ExprKind::SmartString(parameter);
                        return Ok(());
                    }
                    "java/lang/Integer" | "java/lang/Number"
                        if ParameterFact::contains(facts, parameter, RefinedType::Int) => return Ok(()),
                    _ => {}
                }
            }
            if ParameterFact::contains(facts, parameter, RefinedType::Int)
                && matches!(self.bytecode.reference(instruction, 0xb6)?,
                    Some(("java/lang/Integer" | "java/lang/Number", "intValue", "()I")))
            {
                value.kind = ExprKind::SmartInt(parameter);
                return Ok(());
            }
        }
        if let Some(StackValue::Value(value)) = stack.last()
            && self.bytecode.reference(instruction, 0xb6)? == Some(("java/lang/String", "length", "()I"))
            && (matches!(value.kind, ExprKind::SmartString(_) | ExprKind::Literal(Literal::String(_)))
                || value.source_type(self.locals).is_some_and(|(ty, jvm)| {
                    !ty.nullable && ty.class_id() == Some("kotlin/String")
                        && matches!(jvm, JvmType::Object(owner) if owner == "java/lang/String")
                }))
        {
            let value = pop_value(stack, self.declaration)?;
            let depth = value.depth + 1;
            let length = Expr::new(ExprKind::StringLength(Box::new(value)), depth, self.declaration)?;
            stack.push(StackValue::Value(length));
            return Ok(());
        }
        self.bytecode.expression(instruction, self.locals, stack, self.declaration)
    }

    fn throw_value(&self, before: &[Instruction]) -> Result<Option<Expr<'class>>, KotlinError> {
        let [new, dup, label, tail @ ..] = before else { return Ok(None); };
        let owner = "java/lang/IllegalStateException";
        let (0xbb, Operand::Constant(ty)) = (new.opcode, &new.operand) else { return Ok(None); };
        let (0x12 | 0x13, Operand::Constant(label)) = (label.opcode, &label.operand) else { return Ok(None); };
        if self.bytecode.class.pool.class_name(*ty)? != owner || dup.opcode != 0x59
            || lambdas::namespace_shadowed(self.locals)
        {
            return Ok(None);
        }
        let init = match tail {
            [init] => init,
            [stringify, init] if self.bytecode.reference(stringify, 0xb6)?
                == Some(("java/lang/Object", "toString", "()Ljava/lang/String;")) => init,
            _ => return Ok(None),
        };
        if self.bytecode.reference(init, 0xb7)? != Some((owner, "<init>", "(Ljava/lang/String;)V")) {
            return Ok(None);
        }
        let Literal::String(message) = self.bytecode.literal(self.bytecode.class.pool.get(*label)?, self.declaration)?
            else { return Ok(None); };
        Expr::new(ExprKind::ThrowIllegalState(message), 1, self.declaration).map(Some)
    }

    fn statement_value(&self, range: std::ops::Range<usize>) -> Result<Option<Expr<'class>>, KotlinError> {
        if !self.instructions[range.clone()].iter().any(|instruction| instruction.opcode == 0xb2)
            || self.parameters.iter().any(|parameter| parameter.name == "kotlin")
            || self.locals.templates.properties.iter().any(|property| property.name == "kotlin")
            || self.bytecode.owner.split(['/', '$']).next() == Some("kotlin")
        {
            return Ok(None);
        }
        // The terminal block owns the effects and the final operand. The
        // caller executes this block only on its original conditional arm.
        let (statements, tail) = match statements::lower_open(
            self.bytecode, self.instructions, range, self.locals, self.declaration, &[],
        ) {
            Ok(result) => result,
            Err(KotlinError::Unsupported { .. }) => return Ok(None),
            Err(error) => return Err(error),
        };
        let Some(tail) = tail.filter(|tail| tail.expr.stack_load() == Some(self.return_opcode - 0x97)) else {
            return Ok(None);
        };
        if statements.is_empty() {
            return Ok(None);
        }
        let depth = tail.expr.depth + 1;
        Expr::new(ExprKind::ValueBlock(Box::new(ValueBlock {
            statements, value: tail.expr,
        })), depth, self.declaration).map(Some)
    }

    fn one_value(&self, stack: &mut Vec<StackValue<'class>>) -> Result<Expr<'class>, KotlinError> {
        if stack.len() != 1 {
            return Err(self.unsupported("expected a single live Kotlin expression"));
        }
        pop_value(stack, self.declaration)
    }

    fn unsupported(&self, reason: &'static str) -> KotlinError {
        KotlinError::unsupported(self.declaration, reason)
    }
}
