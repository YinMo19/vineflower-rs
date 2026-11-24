// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use std::ops::Range;

use crate::cfg::ControlFlowGraph;

use super::{
    Bytecode, Code, Expected, Expr, Instruction, KotlinError, Locals, Operand, Primitive,
    StackValue, ValueParameter,
    logic::{self, Conditional},
    pop_value,
    statements::{self, Statement},
};

pub(in crate::kotlin) struct DecisionBody<'a> {
    arms: Vec<Arm<'a>>,
    end: Vec<Statement<'a>>,
    instructions: Vec<Instruction>,
    start: usize,
    pub lines: Vec<(u16, u16)>,
}

struct Arm<'a> {
    guard: Expr<'a>,
    guard_span: Range<usize>,
    statements: Vec<Statement<'a>>,
}

/// Recover ordered predicates and their statement arms. A guard may merge
/// short-circuit Boolean values, but may not mutate locals or retain a live
/// stack when it enters either statement arm. The method returns at one
/// shared exit, so branches cannot fall through into subsequent arms.
pub(super) fn lower<'class, 'data>(
    bytecode: &Bytecode<'class, 'data>,
    instructions: Vec<Instruction>,
    start: usize,
    code: &Code<'data>,
    locals: &Locals<'_>,
    parameters: &[ValueParameter],
    declaration: &str,
    trace: bool,
) -> Result<DecisionBody<'class>, KotlinError> {
    let invalid = || KotlinError::unsupported(declaration, "unsupported Kotlin decision statement");
    let instructions_slice = &instructions[start..];
    let cfg = ControlFlowGraph::build(instructions_slice, &[]).map_err(|_| invalid())?;
    let exit = cfg.blocks.len().checked_sub(1).ok_or_else(invalid)?;
    let return_range = cfg.blocks[exit].instructions.clone();
    if !matches!(&instructions_slice[return_range.clone()], [ret] if ret.opcode == 0xb1)
        || cfg.reachable().contains(&false)
        || cfg
            .blocks
            .iter()
            .enumerate()
            .any(|(index, block)| block.successors.iter().any(|&next| next <= index))
    {
        return Err(invalid());
    }
    let postdominators = cfg.immediate_postdominators();
    let mut lower = Lowering {
        cfg: &cfg,
        postdominators: &postdominators,
        instructions: instructions_slice,
        bytecode,
        locals,
        parameters,
        declaration,
        cap: cfg.blocks.len().saturating_mul(4),
    };
    let mut arms = Vec::new();
    let mut index = 0;
    let mut stack = Vec::new();
    let end = loop {
        if index == exit {
            break Vec::new();
        }
        let guard_start = cfg.blocks[index].instructions.start;
        let Some((guard, yes, no)) = lower.guard(index, exit, &mut stack)? else {
            if !stack.is_empty() {
                return Err(invalid());
            }
            break lower.statements(index, exit)?;
        };
        let next = if no == exit && cfg.blocks[yes].successors != [exit] {
            arms.push(Arm {
                guard: logic::negate(guard, declaration)?,
                guard_span: guard_start..cfg.blocks[yes].instructions.start,
                statements: Vec::new(),
            });
            yes
        } else {
            if yes >= no || no > exit {
                return Err(invalid());
            }
            arms.push(Arm {
                guard,
                guard_span: guard_start..cfg.blocks[yes].instructions.start,
                statements: lower.statements(yes, exit)?,
            });
            no
        };
        index = next;
    };
    if arms.is_empty() {
        return Err(invalid());
    }
    let lines = if trace {
        code.line_numbers(&bytecode.class.pool)?
    } else {
        Vec::new()
    };
    Ok(DecisionBody {
        arms,
        end,
        instructions,
        start,
        lines,
    })
}

struct Lowering<'a, 'class, 'data> {
    cfg: &'a ControlFlowGraph,
    postdominators: &'a [Option<usize>],
    instructions: &'a [Instruction],
    bytecode: &'a Bytecode<'class, 'data>,
    locals: &'a Locals<'a>,
    parameters: &'a [ValueParameter],
    declaration: &'a str,
    cap: usize,
}

impl<'class> Lowering<'_, 'class, '_> {
    fn guard(
        &mut self,
        mut index: usize,
        exit: usize,
        stack: &mut Vec<StackValue<'class>>,
    ) -> Result<Option<(Expr<'class>, usize, usize)>, KotlinError> {
        loop {
            let block = &self.cfg.blocks[index];
            let (last, before) = self.instructions[block.instructions.clone()]
                .split_last()
                .unwrap();
            if !matches!(last.opcode, 0x99..=0xa6 | 0xc6 | 0xc7) {
                return Ok(None);
            }
            for instruction in before {
                self.bytecode
                    .expression(instruction, self.locals, stack, self.declaration)?;
            }
            let [target, yes] = block.successors[..] else {
                return Err(self.invalid());
            };
            let guard = logic::condition(last.opcode, stack, self.parameters, self.declaration)?;
            let join = self.postdominators[index].ok_or_else(|| self.invalid())?;
            if join == exit {
                if !stack.is_empty() {
                    return Err(self.invalid());
                }
                return Ok(Some((guard, yes, target)));
            }
            if stack
                .iter()
                .any(|value| !matches!(value, StackValue::Value(expr) if expr.infallible()))
            {
                return Err(self.invalid());
            }
            let yes = self.value(yes, join, 0)?;
            let no = self.value(target, join, 0)?;
            stack.push(StackValue::Value(Conditional::new(
                guard,
                yes,
                no,
                self.declaration,
            )?));
            index = join;
        }
    }

    fn value(
        &mut self,
        mut index: usize,
        stop: usize,
        depth: u8,
    ) -> Result<Expr<'class>, KotlinError> {
        // A fresh stack proves both the value's arity and its independence
        // from any earlier operands that survive the nested predicate.
        let mut arm = Vec::new();
        if depth >= 64 {
            return Err(self.invalid());
        }
        let value = loop {
            if index == stop {
                if arm.len() != 1 {
                    return Err(self.invalid());
                }
                break pop_value(&mut arm, self.declaration)?;
            }
            if index > stop {
                return Err(self.invalid());
            }
            self.cap = self.cap.checked_sub(1).ok_or_else(|| self.invalid())?;
            let block = &self.cfg.blocks[index];
            let (last, before) = self.instructions[block.instructions.clone()]
                .split_last()
                .unwrap();
            for instruction in before {
                self.bytecode
                    .expression(instruction, self.locals, &mut arm, self.declaration)?;
            }
            match (last.opcode, &last.operand, block.successors.as_slice()) {
                (0xa7 | 0xc8, Operand::Branch(_), [next]) => index = *next,
                (0x99..=0xa6 | 0xc6 | 0xc7, Operand::Branch(_), [target, yes]) => {
                    let (target, yes) = (*target, *yes);
                    let guard =
                        logic::condition(last.opcode, &mut arm, self.parameters, self.declaration)?;
                    let join = self.postdominators[index]
                        .filter(|join| *join <= stop)
                        .ok_or_else(|| self.invalid())?;
                    if arm
                        .iter()
                        .any(|value| !matches!(value, StackValue::Value(expr) if expr.infallible()))
                    {
                        return Err(self.invalid());
                    }
                    let yes = self.value(yes, join, depth + 1)?;
                    let no = self.value(target, join, depth + 1)?;
                    arm.push(StackValue::Value(Conditional::new(
                        guard,
                        yes,
                        no,
                        self.declaration,
                    )?));
                    index = join;
                }
                (_, Operand::Branch(_) | Operand::Switch { .. }, _) => return Err(self.invalid()),
                (_, _, [next]) => {
                    self.bytecode
                        .expression(last, self.locals, &mut arm, self.declaration)?;
                    index = *next;
                }
                _ => return Err(self.invalid()),
            }
        };
        Ok(value)
    }

    fn statements(&self, index: usize, exit: usize) -> Result<Vec<Statement<'class>>, KotlinError> {
        let block = &self.cfg.blocks[index];
        let mut range = block.instructions.clone();
        if block.successors != [exit] {
            return Err(self.invalid());
        }
        if matches!(self.instructions[range.end - 1].opcode, 0xa7 | 0xc8) {
            range.end -= 1;
        }
        statements::lower_range(
            self.bytecode,
            self.instructions,
            range,
            self.locals,
            self.declaration,
        )
    }

    fn invalid(&self) -> KotlinError {
        KotlinError::unsupported(self.declaration, "unsupported Kotlin decision statement")
    }
}

impl DecisionBody<'_> {
    pub fn write(
        &self,
        out: &mut String,
        parameters: &[ValueParameter],
        declaration: &str,
        indent: &str,
        unit: &str,
        mut map: impl FnMut(&Instruction, usize),
    ) -> Result<(), KotlinError> {
        let mut line = 1;
        let instructions = &self.instructions[self.start..];
        out.push_str(" {\n");
        out.push_str(indent);
        out.push_str(unit);
        out.push_str("when {\n");
        line += 1;
        for arm in &self.arms {
            out.push_str(indent);
            out.push_str(unit);
            out.push_str(unit);
            arm.guard.write_at(
                out,
                Expected::Primitive(Primitive::Boolean),
                parameters,
                declaration,
                0,
            )?;
            out.push_str(" -> ");
            for instruction in &instructions[arm.guard_span.clone()] {
                if instruction.opcode != 0x00 {
                    map(instruction, line);
                }
            }
            write_arm(
                out,
                &arm.statements,
                parameters,
                declaration,
                indent,
                unit,
                instructions,
                &mut line,
                &mut map,
            )?;
        }
        if !self.end.is_empty() {
            out.push_str(indent);
            out.push_str(unit);
            out.push_str(unit);
            out.push_str("else -> ");
            write_arm(
                out,
                &self.end,
                parameters,
                declaration,
                indent,
                unit,
                instructions,
                &mut line,
                &mut map,
            )?;
        } else {
            // An exhaustive subjectless `when` works on all Kotlin versions.
            out.push_str(indent);
            out.push_str(unit);
            out.push_str(unit);
            out.push_str("else -> {}\n");
            line += 1;
        }
        out.push_str(indent);
        out.push_str(unit);
        out.push_str("}\n");
        map(
            instructions.last().expect("decision ends in return"),
            line + 1,
        );
        out.push_str(indent);
        out.push('}');
        Ok(())
    }
}

fn write_arm(
    out: &mut String,
    statements: &[Statement<'_>],
    parameters: &[ValueParameter],
    declaration: &str,
    indent: &str,
    unit: &str,
    instructions: &[Instruction],
    line: &mut usize,
    mut map: impl FnMut(&Instruction, usize),
) -> Result<(), KotlinError> {
    match statements {
        [] => out.push_str("{}"),
        [statement] => {
            statement.write(out, parameters, declaration)?;
            super::switches::map_statement(instructions, statement, *line, &mut map);
        }
        statements => {
            out.push_str("{\n");
            *line += 1;
            for statement in statements {
                out.push_str(indent);
                out.push_str(unit);
                out.push_str(unit);
                out.push_str(unit);
                statement.write(out, parameters, declaration)?;
                super::switches::map_statement(instructions, statement, *line, &mut map);
                out.push('\n');
                *line += 1;
            }
            out.push_str(indent);
            out.push_str(unit);
            out.push_str(unit);
            out.push('}');
        }
    }
    out.push('\n');
    *line += 1;
    Ok(())
}
