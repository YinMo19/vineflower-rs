// Copyright 2000-2024 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! The Kotlin plugin's CFG and method passes through local declaration placement.

mod dead_vars;

use std::{io, sync::Arc};

use crate::decompiler::{
    decompose::{
        finish::{
            build_synchronized, clear_statements, condense_sequences, remove_synchronized_handlers,
        },
        if_helper::merge_all_ifs,
    },
    exits, increments, inline_blocks, labels,
    loops::{eliminate, enhance, extract, late},
    post_process, secondary,
    stack::{StackSimplifyOptions, simplify_stack_vars},
};
use crate::engine::method_timeout::checkpoint;
use crate::engine::{
    Cx,
    method_processor::{ExpressionMethod, structured_statement_graph_for_language},
};
use crate::structs::{StructClass, StructMethod};

/// Run the Kotlin pipeline through SetVarDefinitions. The following Kotlin AST
/// rewrites use the same statement root, variable processor and counters.
pub fn defined_method(
    cx: &mut Cx,
    class: &StructClass,
    method: &Arc<StructMethod>,
) -> io::Result<Option<ExpressionMethod>> {
    let Some(structured) = structured_statement_graph_for_language(cx, class, method, true)? else {
        return Ok(None);
    };
    let cx = &mut *cx.enter_method(&structured.flow.counters);
    let mut recovered = structured.recover_finally(cx, class)?;
    let root = recovered.structured.root;
    let counters = &mut recovered.structured.flow.counters;
    build_synchronized(&mut cx.ir, counters, root);
    remove_synchronized_handlers(&mut cx.ir, root);
    condense_sequences(cx, counters, root);
    clear_statements(cx, root);

    let mut result = recovered.lift_expressions(cx, class)?;
    result.recover_initial_increments(cx, class)?;
    increments::inline_in_conditions(cx, root);
    result.build_assertions(cx, class)?;

    main_loop(cx, class, &mut result)?;

    simplify_stack_vars(
        cx,
        &mut result.flow.counters,
        root,
        class,
        &StackSimplifyOptions {
            inline_regular_vars: true,
        },
    );
    post_process::adjust_returns(&mut cx.ir, root, &result.descriptor.ret);
    post_process::remove_redundant_returns(&mut cx.ir, root);
    identify_secondary(cx, &mut result)?;
    result.set_var_definitions(cx)?;
    Ok(Some(result))
}

fn main_loop(cx: &mut Cx, class: &StructClass, method: &mut ExpressionMethod) -> io::Result<()> {
    let root = method.root;
    loop {
        checkpoint();
        labels::clean_up_edges(&mut cx.ir, root);
        merge_loops(cx, class, method)?;
        method.simplify_stack_vars(cx, class);
        method.set_var_versions(cx, class)?;
        labels::identify_labels(&mut cx.ir, root);
        if identify_secondary(cx, method)? {
            continue;
        }
        // A dead assignment removal lets the remaining passes see the new tree.
        dead_vars::eliminate(cx, root)?;
        let counters = &mut method.flow.counters;
        if inline_blocks::inline(cx, counters, root)?
            || late::make_do_while(cx, counters, root)?
            || late::condense_returns(cx, counters, root)?
            || exits::condense(cx, counters, root)?
        {
            continue;
        }
        return Ok(());
    }
}

fn merge_loops(cx: &mut Cx, class: &StructClass, method: &mut ExpressionMethod) -> io::Result<()> {
    let root = method.root;
    let counters = &mut method.flow.counters;
    loop {
        checkpoint();
        if eliminate::eliminate(cx, counters, root, class)? {
            continue;
        }
        enhance::enhance_kotlin(cx, counters, root)?;
        if extract::extract(cx, counters, root) || merge_all_ifs(cx, counters, root, class) {
            continue;
        }
        return Ok(());
    }
}

fn identify_secondary(cx: &mut Cx, method: &mut ExpressionMethod) -> io::Result<bool> {
    secondary::identify(
        cx,
        &mut method.flow.counters,
        method.root,
        method.flow.variables,
        true,
    )
}
