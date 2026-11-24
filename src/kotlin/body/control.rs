// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use crate::cfg::ControlFlowGraph;

use super::{
    Bytecode, Expr, Instruction, JvmType, KotlinError, Locals, Operand, StackValue, ValueParameter,
    logic::{self, Conditional},
    pop_value, return_opcode,
    tailrec,
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
    match lower.region(0, None, &mut Vec::new(), 0)? {
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

impl<'class> Lowering<'_, 'class, '_> {
    fn region(
        &mut self,
        mut index: usize,
        stop: Option<usize>,
        stack: &mut Vec<StackValue<'class>>,
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
            for instruction in before {
                self.bytecode
                    .expression(instruction, self.locals, stack, self.declaration)?;
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
                    let yes = self.region(fallthrough, join, stack, depth + 1)?;
                    let no = self.region(target, join, stack, depth + 1)?;
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
                    self.bytecode
                        .expression(last, self.locals, stack, self.declaration)?;
                    index = *next;
                }
                _ => return Err(self.unsupported("unterminated Kotlin expression path")),
            }
        }
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
