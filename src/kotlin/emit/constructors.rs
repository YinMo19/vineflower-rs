// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use super::{
    Bytecode, ClassDeclaration, Constructor, KotlinError, Location, Style, Types, body, trace,
    value_parameter, visibility,
};

pub(super) fn render(
    out: &mut String,
    bytecode: &Bytecode<'_, '_>,
    types: &Types<'_>,
    declaration: &ClassDeclaration,
    primary: &Constructor,
    style: Style<'_>,
    mut location: Location<'_>,
) -> Result<(), KotlinError> {
    let constructors = body::constructors::recover(bytecode, declaration, primary, location.is_some())?;
    for secondary in constructors {
        if !out.is_empty() {
            out.push('\n');
            if let Some((_, line)) = &mut location {
                *line += 1;
            }
        }
        let constructor = secondary.constructor;
        out.push_str(style.indent);
        out.push_str(visibility(constructor.flags.visibility()?)?);
        out.push_str("constructor(");
        for (index, parameter) in constructor.parameters.iter().enumerate() {
            if index != 0 {
                out.push_str(", ");
            }
            value_parameter(out, types, parameter, false, None)?;
        }
        out.push(')');
        secondary.write_delegation(out, bytecode.owner)?;
        out.push_str(" {\n");
        let mut trace = location.as_ref()
            .map(|_| trace::Trace::new(bytecode, secondary.method)).transpose()?;
        if let (Some(trace), Some((_, line))) = (&mut trace, &mut location) {
            for instruction in secondary.delegation() {
                trace.instruction(instruction, *line);
            }
            *line += 1;
        }
        for statement in &secondary.block.statements {
            out.push_str(style.indent);
            out.push_str(style.unit);
            secondary.write_statement(statement, out, bytecode.owner)?;
            out.push('\n');
            if let (Some(trace), Some((_, line))) = (&mut trace, &mut location) {
                statement.trace(bytecode, &secondary.block.instructions, |instruction| {
                    trace.instruction(instruction, *line);
                })?;
                *line += 1;
            }
        }
        out.push_str(style.indent);
        out.push_str("}\n");
        if let (Some(mut trace), Some((map, line))) = (trace, &mut location) {
            let ret = secondary.block.instructions.last().expect("constructor ends with return");
            trace.instruction(ret, *line);
            trace.finish(map, secondary.block.lines);
            *line += 1;
        }
    }
    Ok(())
}
