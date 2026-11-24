// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use std::{collections::BTreeMap, ops::Range};

use crate::cfg::ControlFlowGraph;

use super::{
    Bytecode, Code, Expected, Expr, ExprKind, Instruction, JvmType, KotlinError, Literal, Locals,
    Operand, Primitive, Type, ValueParameter, identifier, local_load,
    local_store, pop_value, return_opcode, statements::{self, Statement},
};

pub(in crate::kotlin) struct SwitchBody<'a> {
    selector: Expr<'a>,
    key_type: Primitive,
    head: Range<usize>,
    cases: Vec<Case<'a>>,
    continuation: Continuation<'a>,
    pub lines: Vec<(u16, u16)>,
    instructions: Vec<Instruction>,
    start: usize,
}

struct Case<'a> {
    /// An empty key list denotes the default target, including table holes.
    keys: Vec<i32>,
    arm: Arm<'a>,
    terminal: Option<usize>,
    range: Range<usize>,
}

enum Arm<'a> {
    Statements(Vec<Statement<'a>>),
    Value(Expr<'a>),
}

enum Continuation<'a> {
    Return(Option<usize>),
    Statement(usize),
    Bind { name: &'a str, slot: u16, store: usize, end: usize },
}

/// Recover direct integer switches. Every arm owns exactly one basic block
/// (or the empty default at the exit), cannot fall into a sibling, and must
/// either return the declared type or reach the switch's postdominator.
pub(super) fn lower<'a, 'data>(
    bytecode: &Bytecode<'a, 'data>, instructions: Vec<Instruction>, start: usize, code: &Code<'data>,
    locals: &Locals<'_>, parameters: &[ValueParameter], return_type: &JvmType, declaration: &str, trace: bool,
) -> Result<SwitchBody<'a>, KotlinError> {
    let invalid = || KotlinError::unsupported(declaration, "unsupported Kotlin switch shape");
    let decoded = &instructions[start..];
    let cfg = ControlFlowGraph::build(decoded, &[]).map_err(|_| invalid())?;
    let entry = cfg.blocks.first().ok_or_else(invalid)?;
    let (switch, head) = decoded[entry.instructions.clone()].split_last().ok_or_else(invalid)?;
    let Operand::Switch { default, cases } = &switch.operand else { return Err(invalid()); };
    let default = cfg.block_at(*default).ok_or_else(invalid)?;
    let mut targets = BTreeMap::new();
    for &(key, offset) in cases {
        let target = cfg.block_at(offset).ok_or_else(invalid)?;
        if target != default { targets.entry(target).or_insert_with(Vec::new).push(key); }
    }
    targets.insert(default, Vec::new());
    let join = cfg.immediate_postdominators()[0];
    if targets.contains_key(&0) || join == Some(0) || join.is_some_and(|join| targets.keys().any(|&target| target > join)) {
        return Err(invalid());
    }
    let standalone_blocks = targets.len() + 1 + usize::from(join.is_some_and(|join| !targets.contains_key(&join)));
    if cfg.blocks.len() != standalone_blocks || cfg.reachable().contains(&false) {
        return Err(invalid());
    }

    let continuation = match (return_type, join) {
        (JvmType::Void, Some(join)) => {
            let tail = cfg.blocks[join].instructions.clone();
            match &decoded[tail.clone()] {
                [ret] if ret.opcode == 0xb1 => Continuation::Statement(tail.start),
                _ if !targets.contains_key(&join) => {
                    bound_print(bytecode, code, decoded, tail, locals, parameters, declaration)?
                }
                _ => return Err(invalid()),
            }
        }
        (JvmType::Void, None) => return Err(invalid()),
        (_, Some(join)) => match &decoded[cfg.blocks[join].instructions.clone()] {
            [ret] if ret.opcode == return_opcode(return_type) && !targets.contains_key(&join) => {
                Continuation::Return(Some(cfg.blocks[join].instructions.start))
            }
            _ => return Err(invalid()),
        },
        (_, None) => Continuation::Return(None),
    };
    let mut stack = Vec::new();
    for instruction in head { bytecode.expression(instruction, locals, &mut stack, declaration)?; }
    let selector = pop_value(&mut stack, declaration)?;
    let key_type = selector.primitive_hint(parameters).unwrap_or(Primitive::Int);
    if !stack.is_empty() || !matches!(key_type, Primitive::Int | Primitive::Short | Primitive::Byte | Primitive::Char)
        || selector.stack_load() != Some(0x15)
    {
        return Err(invalid());
    }
    let mut arms = Vec::with_capacity(targets.len());
    for (target, keys) in targets {
        if Some(target) == join {
            if !matches!(continuation, Continuation::Statement(_)) { return Err(invalid()); }
            let start = cfg.blocks[target].instructions.start;
            arms.push(Case { keys, arm: Arm::Statements(Vec::new()), terminal: None, range: start..start });
            continue;
        }
        let block = &cfg.blocks[target];
        let mut range = block.instructions.clone();
        let last = &decoded[range.end - 1];
        let terminal = if let Some(join) = join {
            if block.successors != [join] { return Err(invalid()); }
            if matches!(last.opcode, 0xa7 | 0xc8) {
                range.end -= 1;
                Some(range.end)
            } else { None }
        } else {
            if !block.successors.is_empty() || last.opcode != return_opcode(return_type) { return Err(invalid()); }
            range.end -= 1;
            Some(range.end)
        };
        let arm = if matches!(continuation, Continuation::Statement(_)) {
            Arm::Statements(statements::lower_range(bytecode, decoded, range.clone(), locals, declaration)?)
        } else {
            for instruction in &decoded[range.clone()] { bytecode.expression(instruction, locals, &mut stack, declaration)?; }
            let expr = pop_value(&mut stack, declaration)?;
            if !stack.is_empty() { return Err(invalid()); }
            Arm::Value(expr)
        };
        arms.push(Case { keys, arm, terminal, range });
    }
    // Kotlin requires else to be the last when branch. Other arms have
    // disjoint integer predicates and cannot transfer into one another.
    let index = arms.iter().position(|arm| arm.keys.is_empty()).expect("switch has default arm");
    arms[index..].rotate_left(1);
    let lines = if trace { code.line_numbers(&bytecode.class.pool)? } else { Vec::new() };
    Ok(SwitchBody { selector, key_type, head: entry.instructions.clone(), cases: arms, continuation, lines, instructions, start })
}

fn bound_print<'a, 'data>(
    bytecode: &Bytecode<'a, 'data>, code: &Code<'data>, decoded: &[Instruction], range: Range<usize>,
    locals: &Locals<'_>, parameters: &[ValueParameter], declaration: &str,
) -> Result<Continuation<'a>, KotlinError> {
    let invalid = || KotlinError::unsupported(declaration, "unsupported Kotlin switch result continuation");
    let [store, get, load, call, ret] = &decoded[range.clone()] else { return Err(invalid()); };
    let Some((0x3a, slot)) = local_store(store) else { return Err(invalid()); };
    if slot < locals.next_slot() || local_load(load) != Some((0x19, slot)) || ret.opcode != 0xb1
        || bytecode.reference(get, 0xb2)? != Some(("java/lang/System", "out", "Ljava/io/PrintStream;"))
        || !matches!(bytecode.reference(call, 0xb6)?, Some(("java/io/PrintStream", "println", "(Ljava/lang/Object;)V" | "(Ljava/lang/String;)V")))
    {
        return Err(invalid());
    }
    let name = code.local_variables(&bytecode.class.pool)?.into_iter().find(|local| {
        local.index == slot && local.descriptor == "Ljava/lang/String;" && u32::from(local.start_pc) == get.offset
            && load.offset < u32::from(local.start_pc) + u32::from(local.length)
            && !parameters.iter().any(|parameter| parameter.name == local.name)
    }).map_or("", |local| local.name);
    Ok(Continuation::Bind { name, slot, store: range.start, end: range.end })
}

impl SwitchBody<'_> {
    pub fn write(&self, out: &mut String, returns: (&Type, &JvmType), parameters: &[ValueParameter],
        declaration: &str, indent: &str, unit: &str, mut map: impl FnMut(&Instruction, usize),
    ) -> Result<(), KotlinError> {
        let decoded = &self.instructions[self.start..];
        let mut line = 1;
        out.push_str(" {\n");
        out.push_str(indent);
        out.push_str(unit);
        let binding = if let Continuation::Bind { name, slot, .. } = self.continuation {
            let name = if !name.is_empty() {
                std::borrow::Cow::Borrowed(name)
            } else {
                let mut name = format!("var{slot}");
                while parameters.iter().any(|parameter| parameter.name == name) { name.push('_'); }
                std::borrow::Cow::Owned(name)
            };
            out.push_str("val ");
            identifier(out, &name, declaration)?;
            out.push_str(": String = ");
            Some(name)
        } else {
            if matches!(self.continuation, Continuation::Return(_)) { out.push_str("return "); }
            None
        };
        out.push_str("when (");
        self.selector.write_at(out, Expected::Primitive(self.key_type), parameters, declaration, 0)?;
        out.push_str(") {\n");
        for instruction in &decoded[self.head.clone()] { map(instruction, line); }
        line += 1;
        for case in &self.cases {
            out.push_str(indent);
            out.push_str(unit);
            out.push_str(unit);
            if case.keys.is_empty() {
                out.push_str("else");
            } else {
                for (index, &key) in case.keys.iter().enumerate() {
                    if index != 0 { out.push_str(", "); }
                    let key_expr = Expr::literal(Literal::Int(key));
                    if matches!(self.key_type, Primitive::Byte | Primitive::Short) { out.push('('); }
                    key_expr.write_at(out, Expected::Primitive(self.key_type), parameters, declaration, 0)?;
                    match self.key_type {
                        Primitive::Byte => out.push_str(").toByte()"),
                        Primitive::Short => out.push_str(").toShort()"),
                        _ => {}
                    }
                }
            }
            out.push_str(" -> ");
            match &case.arm {
                Arm::Statements(statements) => match statements.as_slice() {
                    [] => out.push_str("{}"),
                    [statement] => {
                        statement.write(out, parameters, declaration)?;
                        map_statement(decoded, statement, line, &mut map);
                    }
                    statements => {
                        out.push_str("{\n");
                        line += 1;
                        for statement in statements {
                            out.push_str(indent);
                            out.push_str(unit);
                            out.push_str(unit);
                            out.push_str(unit);
                            statement.write(out, parameters, declaration)?;
                            out.push('\n');
                            map_statement(decoded, statement, line, &mut map);
                            line += 1;
                        }
                        out.push_str(indent);
                        out.push_str(unit);
                        out.push_str(unit);
                        out.push('}');
                    }
                },
                Arm::Value(expr) => {
                    if binding.is_some() {
                        if !matches!(&expr.kind, ExprKind::Literal(Literal::String(_)))
                            && !matches!(&expr.kind, ExprKind::Parameter {index, ..}
                                if parameters[*index].ty.class_id() == Some("kotlin/String") && !parameters[*index].ty.nullable)
                        {
                            return Err(KotlinError::unsupported(declaration, "unproven String switch arm for local binding"));
                        }
                        expr.write_at(out, Expected::Reference, parameters, declaration, 0)?;
                    } else {
                        expr.write(out, returns.0, returns.1, parameters, declaration)?;
                    }
                    for instruction in &decoded[case.range.clone()] { map(instruction, line); }
                }
            }
            if let Some(terminal) = case.terminal { map(&decoded[terminal], line); }
            out.push('\n');
            line += 1;
        }
        out.push_str(indent);
        out.push_str(unit);
        out.push_str("}\n");
        let final_return = match self.continuation {
            Continuation::Return(Some(ret)) => { map(&decoded[ret], line); None }
            Continuation::Return(None) => None,
            Continuation::Statement(ret) => Some(ret),
            Continuation::Bind { store, end, .. } => {
                map(&decoded[store], line);
                line += 1;
                out.push_str(indent);
                out.push_str(unit);
                out.push_str("System.out.println(");
                identifier(out, binding.as_deref().expect("local binding emitted"), declaration)?;
                out.push_str(")\n");
                for instruction in &decoded[store + 1..end - 1] { map(instruction, line); }
                Some(end - 1)
            }
        };
        if let Some(ret) = final_return { map(&decoded[ret], line + 1); }
        out.push('}');
        Ok(())
    }
}

pub(super) fn map_statement(instructions: &[Instruction], statement: &Statement<'_>, line: usize, mut map: impl FnMut(&Instruction, usize)) {
    for instruction in &instructions[statement.instructions.clone()] {
        if !matches!(instruction.opcode, 0x00 | 0x5f) { map(instruction, line); }
    }
}
