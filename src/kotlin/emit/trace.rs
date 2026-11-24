// Copyright 2026 Vineflower contributors. Licensed under the Apache License, Version 2.0.

use crate::{
    bytecode::Instruction,
    classfile::Member,
    emit::{MethodMap, SourceMap},
};

use super::{Bytecode, KotlinError};

pub(super) struct Trace(MethodMap);

impl Trace {
    pub(super) fn new(
        bytecode: &Bytecode<'_, '_>,
        member: &Member<'_>,
    ) -> Result<Self, KotlinError> {
        let pool = &bytecode.class.pool;
        Ok(Self(MethodMap {
            class_name: bytecode.owner.to_owned(),
            name: pool.utf8(member.name_index)?.to_owned(),
            descriptor: pool.utf8(member.descriptor_index)?.to_owned(),
            offsets: Default::default(),
        }))
    }

    pub(super) fn instruction(&mut self, instruction: &Instruction, line: usize) {
        // Vineflower tracks the byte range belonging to a source expression,
        // including the operand bytes of JVM instructions.
        self.offsets(
            instruction.offset..instruction.offset + instruction.len,
            line,
        );
    }

    pub(super) fn offsets(&mut self, offsets: impl IntoIterator<Item = u32>, line: usize) {
        self.0
            .offsets
            .extend(offsets.into_iter().map(|offset| (offset, line)));
    }

    pub(super) fn finish(self, output: &mut SourceMap, lines: Vec<(u16, u16)>) {
        output.add(self.0, lines);
    }
}

pub(super) fn line_count(source: &str) -> usize {
    source.bytes().filter(|&byte| byte == b'\n').count()
}
