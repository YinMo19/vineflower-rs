// Copyright 2000-2017 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! Java VarProcessor.setVarDefinitions, after expression and loop recovery.

pub(crate) mod clashes;
mod finality;
mod locals;
mod merge;
mod placement;

use crate::decompiler::ir::{StatId, VarProcessorId};
use crate::engine::Cx;
use crate::engine::counter_container::CounterContainer;
use crate::types::MethodDescriptor;
use std::{io, sync::Arc};

pub(crate) fn define(
    cx: &mut Cx,
    counters: &mut CounterContainer,
    root: StatId,
    owner: VarProcessorId,
    descriptor: &MethodDescriptor,
) -> io::Result<()> {
    let cx = &mut *cx.enter_method(counters);
    let method = Arc::clone(root.method(&cx.ir));
    let implicit = placement::initialize(cx, root, owner, descriptor);
    merge::merge(cx, root, &method, owner)?;
    placement::place(cx, counters, root, owner, implicit);
    merge::merge(cx, root, &method, owner)?;
    locals::propagate(cx, root, owner, &method, descriptor)?;
    finality::set_non_final(&mut cx.ir, root);
    let clashes = clashes::remap_clashing_names(cx, root, &method, owner)?;
    cx.ir[owner].clashing_names.extend(clashes);
    cx.ir[owner].definitions_set = true;
    Ok(())
}
