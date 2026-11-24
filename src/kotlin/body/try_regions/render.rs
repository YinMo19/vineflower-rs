// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use std::ops::Range;

use super::{Binding, Block, End, Finally, Instruction, JvmType, KotlinError, Region, TryBody, ValueParameter};
use crate::kotlin::{Type, syntax::qualified};
use super::super::{Expected, Primitive};

impl TryBody<'_> {
    pub fn write(
        &self,
        out: &mut String,
        returns: (&Type, &JvmType),
        parameters: &[ValueParameter],
        declaration: &str,
        indent: &str,
        unit: &str,
        map: impl FnMut(&Instruction, usize),
    ) -> Result<(), KotlinError> {
        out.push_str(" {\n");
        let mut writer = Writer {
            out, returns, parameters, declaration, indent, unit, instructions: &self.instructions,
            line: 1, map,
        };
        writer.block(&self.block, 1)?;
        writer.out.push_str(indent);
        writer.out.push('}');
        Ok(())
    }
}

struct Writer<'a, M> {
    out: &'a mut String,
    returns: (&'a Type, &'a JvmType),
    parameters: &'a [ValueParameter],
    declaration: &'a str,
    indent: &'a str,
    unit: &'a str,
    instructions: &'a [Instruction],
    line: usize,
    map: M,
}

impl<M: FnMut(&Instruction, usize)> Writer<'_, M> {
    fn indent(&mut self, level: u8) {
        self.out.push_str(self.indent);
        for _ in 0..level {
            self.out.push_str(self.unit);
        }
    }

    fn newline(&mut self) {
        self.out.push('\n');
        self.line += 1;
    }

    fn map(&mut self, range: Range<usize>) {
        for instruction in &self.instructions[range] {
            if !matches!(instruction.opcode, 0x00 | 0x5f) {
                (self.map)(instruction, self.line);
            }
        }
    }

    fn map_finally(&mut self, cleanup: &Finally<'_>, span: Range<usize>) {
        self.map(span.clone());
        for copy in &cleanup.copies {
            let start = *copy + span.start - cleanup.start;
            self.map(start..start + span.len());
        }
    }

    fn block(&mut self, block: &Block<'_>, level: u8) -> Result<(), KotlinError> {
        for statement in &block.statements {
            self.indent(level);
            statement.write(self.out, self.parameters, self.declaration)?;
            self.map(statement.instructions.clone());
            self.newline();
        }
        match &block.end {
            End::Continue => {}
            End::ReturnUnit(index, implicit) => {
                self.map(*index..*index + 1);
                if !*implicit {
                    self.indent(level);
                    self.out.push_str("return");
                    self.newline();
                }
            }
            End::Return(value) | End::Result(value) => {
                self.indent(level);
                if matches!(&block.end, End::Return(_)) {
                    self.out.push_str("return ");
                }
                value.expr.write(self.out, self.returns.0, self.returns.1, self.parameters, self.declaration)?;
                self.map(value.instructions.clone());
                self.newline();
            }
            End::Throw(binding, range) => {
                self.indent(level);
                self.out.push_str("throw ");
                binding.write(self.out, self.declaration)?;
                self.map(range.clone());
                self.newline();
            }
            End::Try(region) => self.region(region, level)?,
            End::Loop { start, body, next } => {
                self.indent(level);
                self.out.push_str("while (true) {");
                (self.map)(&self.instructions[*start], self.line);
                self.newline();
                self.block(body, level + 1)?;
                self.indent(level);
                self.out.push('}');
                self.newline();
                self.block(next, level)?;
            }
            End::BreakIf { condition, instructions } => {
                self.indent(level);
                self.out.push_str("if (");
                condition.write_at(
                    self.out, Expected::Primitive(Primitive::Boolean), self.parameters, self.declaration, 0,
                )?;
                self.out.push_str(") break");
                self.map(instructions.clone());
                self.newline();
            }
        }
        Ok(())
    }

    fn region(&mut self, region: &Region<'_>, level: u8) -> Result<(), KotlinError> {
        self.indent(level);
        if region.result.is_some() {
            self.out.push_str("return ");
        }
        self.out.push_str("try {");
        // The compiler's leading nop often owns the source `try` line.
        (self.map)(&self.instructions[region.start], self.line);
        self.newline();
        self.block(&region.body, level + 1)?;
        self.indent(level);
        self.out.push('}');
        for catch in &region.catches {
            self.out.push_str(" catch (");
            catch.binding.write(self.out, self.declaration)?;
            self.out.push_str(": ");
            catch_type(self.out, catch.binding, self.declaration)?;
            self.out.push_str(") {");
            self.map(catch.handler..catch.handler + 1);
            self.newline();
            self.block(&catch.body, level + 1)?;
            self.indent(level);
            self.out.push('}');
        }
        if let Some(cleanup) = &region.finally {
            self.out.push_str(" finally {");
            self.newline();
            for statement in &cleanup.statements {
                self.indent(level + 1);
                statement.write(self.out, self.parameters, self.declaration)?;
                self.map_finally(cleanup, statement.instructions.clone());
                self.newline();
            }
            if let Some(value) = &cleanup.returning {
                self.indent(level + 1);
                self.out.push_str("return ");
                value.expr.write(self.out, self.returns.0, self.returns.1, self.parameters, self.declaration)?;
                self.map_finally(cleanup, value.instructions.clone());
                self.newline();
            }
            self.indent(level);
            self.out.push('}');
        }
        if let Some(result) = &region.result {
            self.map(result.clone());
        }
        self.newline();
        if let Some(next) = &region.next {
            if !next.statements.is_empty() || !matches!(next.end, End::ReturnUnit(_, true)) {
                self.newline();
            }
            self.block(next, level)?;
        }
        Ok(())
    }
}

fn catch_type(out: &mut String, binding: Binding<'_>, declaration: &str) -> Result<(), KotlinError> {
    let ty = match binding.ty {
        "java/lang/Throwable" => "kotlin/Throwable",
        "java/lang/Exception" => "kotlin/Exception",
        "java/lang/RuntimeException" => "kotlin/RuntimeException",
        "java/lang/ArithmeticException" => "kotlin/ArithmeticException",
        "java/lang/IllegalArgumentException" => "kotlin/IllegalArgumentException",
        "java/lang/IllegalStateException" => "kotlin/IllegalStateException",
        "java/lang/NullPointerException" => "kotlin/NullPointerException",
        "java/lang/IndexOutOfBoundsException" => "kotlin/IndexOutOfBoundsException",
        "java/lang/UnsupportedOperationException" => "kotlin/UnsupportedOperationException",
        other => other,
    };
    qualified(out, ty, declaration)
}
