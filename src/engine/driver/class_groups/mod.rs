// SPDX-License-Identifier: Apache-2.0

//! Each task prepares and renders its own Java roots. Bytecode and the class
//! path are shared. Method graphs, class wrappers and import scopes stay local.

mod dependencies;

use std::io;
use std::sync::Arc;

use rayon::prelude::*;

use super::{Cx, DecompiledClass, PendingClass, ReclaimSchedule, prepare, render_unit};
use crate::engine::class_nodes::{ClassNodeId, ClassNodes};

pub(super) struct Plan {
    assignment: Vec<usize>,
    groups: usize,
}

pub(super) fn plan(cx: &Cx, roots: &[PendingClass], single_unit: bool) -> io::Result<Option<Plan>> {
    if !single_unit
        || roots.len() < 2
        || cx.kotlin_members.is_some()
        || roots.iter().any(|root| root.kotlin)
    {
        return Ok(None);
    }
    let requested = cx.options.worker_count();
    if requested > 0x7fff {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "thread-count exceeds the ForkJoinPool limit of 32767",
        ));
    }
    if requested < 2 {
        return Ok(None);
    }
    let Some(components) = dependencies::connected_roots(
        &cx.class_nodes,
        roots,
        cx.options.decompile_complex_constant_dynamic,
    ) else {
        return Ok(None);
    };
    let groups = requested.min(components.len());
    if groups < 2 {
        return Ok(None);
    }

    // Give the heaviest components separate workers before filling the smaller
    // gaps. Nested methods can dominate a small-looking top-level class.
    let mut costs: Vec<_> = components
        .into_iter()
        .map(|indices| {
            let cost: usize = indices
                .iter()
                .map(|&i| cost(&cx.class_nodes, roots[i].node))
                .sum();
            (indices, cost)
        })
        .collect();
    costs.sort_by_key(|(_, cost)| std::cmp::Reverse(*cost));
    let mut loads = std::collections::BinaryHeap::from(
        (0..groups)
            .map(|i| std::cmp::Reverse((0usize, i)))
            .collect::<Vec<_>>(),
    );
    let mut assignment = vec![0; roots.len()];
    for (component, cost) in costs {
        let std::cmp::Reverse((load, group)) = loads.pop().unwrap();
        for index in component {
            assignment[index] = group;
        }
        loads.push(std::cmp::Reverse((load + cost, group)));
    }
    Ok(Some(Plan { assignment, groups }))
}

fn cost(nodes: &ClassNodes, root: ClassNodeId) -> usize {
    let node = &nodes[root];
    1 + node
        .class
        .methods
        .iter()
        .map(|m| 1 + m.stored_code_len())
        .sum::<usize>()
        + node.nested.iter().map(|&id| cost(nodes, id)).sum::<usize>()
}

pub(super) fn run(
    cx: &Cx,
    roots: Vec<PendingClass>,
    plan: Plan,
) -> io::Result<Vec<(usize, DecompiledClass)>> {
    log::info!(
        "Processing {} Java roots in {} parallel groups",
        roots.len(),
        plan.groups
    );
    let mut groups = (0..plan.groups).map(|_| Vec::new()).collect::<Vec<_>>();
    for (index, (root, group)) in roots.into_iter().zip(plan.assignment).enumerate() {
        groups[group].push((index, root));
    }
    let run_groups = || {
        groups
            .into_par_iter()
            .map(|group| {
                let mut worker = Cx::new(Arc::clone(&cx.struct_context));
                worker.class_nodes = cx.class_nodes.initial_copy();
                worker.collect_text_tokens = cx.collect_text_tokens;
                worker.javadoc.clone_from(&cx.javadoc);
                let parent = worker.take_class_session();
                let mut reclaim = ReclaimSchedule::default();
                let (indices, mut roots): (Vec<_>, Vec<_>) = group.into_iter().unzip();
                prepare::ordered(&mut worker, &mut roots, &mut reclaim, &parent)?;
                let mut output = Vec::with_capacity(roots.len());
                render_unit(&mut worker, roots, &mut reclaim, parent, |i, class| {
                    output.push((indices[i], class));
                    Ok(())
                })?;
                Ok(output)
            })
            .collect::<io::Result<Vec<_>>>()
    };
    // A normal CLI invocation uses the shared Rayon pool. Explicit smaller
    // limits and differently configured host pools keep the requested budget.
    let requested = cx.options.worker_count();
    let results = if requested == std::thread::available_parallelism().map_or(1, usize::from)
        && rayon::current_num_threads() == requested
    {
        run_groups()?
    } else {
        rayon::ThreadPoolBuilder::new()
            .num_threads(plan.groups)
            .build()
            .map_err(io::Error::other)?
            .install(run_groups)?
    };
    let mut ordered: Vec<_> = results.into_iter().flatten().collect();
    ordered.sort_unstable_by_key(|(index, _)| *index);
    Ok(ordered)
}
