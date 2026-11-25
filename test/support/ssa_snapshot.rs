// SPDX-License-Identifier: Apache-2.0

use std::collections::{BTreeMap, HashSet};
use std::fmt::Write;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::Arc;

use itertools::Itertools;
use vineflower_rs::decompiler::exps::Expr;
use vineflower_rs::decompiler::ir::{ExprKind, Ir, StatId};
use vineflower_rs::decompiler::sforms::{
    InstructionRewrites, SsaResult, SsauResult, VersionMap, reassign_ssa, reset_versions,
    split_ssa, split_ssau,
};
use vineflower_rs::decompiler::stats::StatementKind;
use vineflower_rs::decompiler::vars::var_version_pair::VarVersionPair;
use vineflower_rs::decompiler::vars::version_graph::VersionState;
use vineflower_rs::engine::counter_container::{
    CounterContainer, EXPRESSION_COUNTER, STATEMENT_COUNTER, VAR_COUNTER,
};
use vineflower_rs::engine::method_processor::StructuredMethod;
use vineflower_rs::structs::StructMethod;

pub fn run(ir: &mut Ir, structured: &StructuredMethod, method: &StructMethod) -> String {
    let root = structured.root;
    let counters = &structured.flow.counters;
    let (ssa, mut snapshot) = match phase("split", || {
        let ssa = split_ssa(ir, root, method);
        let snapshot = split_state(ir, root, counters, &ssa);
        (ssa, snapshot)
    }) {
        Ok(split) => split,
        Err(error) => return error,
    };

    match phase("reassign", || {
        let changes = reassign_ssa(ir, root, &ssa.versions, counters);
        format!(
            "reassigned={};{}{}",
            counters_text(counters),
            variables(ir, root),
            rewrites(ir, root, &changes)
        )
    }) {
        Ok(reassigned) => write!(snapshot, "\t{reassigned}").unwrap(),
        Err(error) => return format!("{snapshot}\t{error}"),
    }
    match phase("reset", || reset(ir, root, counters, "reset")) {
        Ok(reset) => write!(snapshot, "\t{reset}").unwrap(),
        Err(error) => return format!("{snapshot}\t{error}"),
    }
    match phase("ssau", || {
        let ssau = split_ssau(ir, root, method);
        ssau_state(ir, root, counters, &ssau)
    }) {
        Ok(ssau) => write!(snapshot, "\t{ssau}").unwrap(),
        Err(error) => return format!("{snapshot}\t{error}"),
    }
    match phase("ssau-reset", || reset(ir, root, counters, "ssau-reset")) {
        Ok(reset) | Err(reset) => write!(snapshot, "\t{reset}").unwrap(),
    }
    snapshot
}

fn reset(ir: &mut Ir, root: StatId, counters: &CounterContainer, stage: &str) -> String {
    reset_versions(ir, root);
    format!(
        "{stage}={};{}",
        counters_text(counters),
        variables(ir, root)
    )
}

fn phase<T>(stage: &str, run: impl FnOnce() -> T) -> Result<T, String> {
    catch_unwind(AssertUnwindSafe(run))
        .map_err(|error| format!("{stage}-panic={}", super::panic_text(&*error)))
}

fn split_state(ir: &Ir, root: StatId, counters: &CounterContainer, ssa: &SsaResult) -> String {
    let mut fields = format!("split={};{}", counters_text(counters), variables(ir, root));
    append_entries(&mut fields, "phi", ssa.versions.phi.iter(), |set| {
        set.iter().sorted().join(",")
    });
    append_entries(
        &mut fields,
        "rev",
        ssa.versions.simple_reverse_phi_lookup().iter(),
        i32::to_string,
    );
    append_entries(&mut fields, "read", &ssa.read_counts, i32::to_string);
    fields
}

fn ssau_state(ir: &Ir, root: StatId, counters: &CounterContainer, ssau: &SsauResult) -> String {
    let mut fields = format!("ssau={};{}", counters_text(counters), variables(ir, root));
    for node in &ssau.versions.graph.nodes {
        let state = match node.state {
            Some(VersionState::Write) => "WRITE",
            Some(VersionState::Read) => "READ",
            Some(VersionState::Phi) => "PHI",
            Some(VersionState::DeadRead) => "DEAD_READ",
            Some(VersionState::Phantom) => "PHANTOM",
            Some(VersionState::Param) => "PARAM",
            Some(VersionState::Catch) => "CATCH",
            None => "~",
        };
        let edges = |entries: &indexmap::IndexSet<VarVersionPair>| {
            entries.iter().sorted().map(pair_text).join(",")
        };
        write!(
            fields,
            "node{}={state}|{}|{}|{}|{}|{};",
            pair_text(&node.as_pair()),
            edges(&node.predecessors),
            edges(&node.successors),
            optional_pair(node.phantom_node),
            optional_pair(node.phantom_parent_node),
            live_map(node.live.as_ref()),
        )
        .unwrap();
    }
    append_entries(&mut fields, "assign", &ssau.versions.assignments, pair_text);
    append_entries(
        &mut fields,
        "range",
        &ssau.versions.first_range,
        i32::to_string,
    );
    for (expr, var) in ssau
        .versions
        .field_vars
        .iter()
        .sorted_by_key(|&(expr, _)| expr)
    {
        write!(fields, "field{expr}={var};").unwrap();
    }
    append_entries(&mut fields, "read", &ssau.read_counts, i32::to_string);
    fields
}

fn pair_text(pair: &VarVersionPair) -> String {
    format!("{}:{}", pair.var, pair.version)
}

fn optional_pair(pair: Option<VarVersionPair>) -> String {
    pair.as_ref().map_or_else(|| "~".into(), pair_text)
}

fn live_map(map: Option<&VersionMap>) -> String {
    map.map_or_else(
        || "~".into(),
        |map| {
            map.iter()
                .map(|(var, versions)| format!("{var}:{}", versions.iter().sorted().join(",")))
                .join("/")
        },
    )
}

fn append_entries<'a, V: 'a>(
    out: &mut String,
    prefix: &str,
    entries: impl IntoIterator<Item = (&'a VarVersionPair, &'a V)>,
    format_value: impl Fn(&V) -> String,
) {
    for (pair, value) in entries.into_iter().sorted_by_key(|&(pair, _)| pair) {
        write!(
            out,
            "{prefix}{}:{}={};",
            pair.var,
            pair.version,
            format_value(value)
        )
        .unwrap();
    }
}

fn counters_text(counters: &CounterContainer) -> String {
    format!(
        "{},{},{}",
        counters.get_counter(STATEMENT_COUNTER),
        counters.get_counter(EXPRESSION_COUNTER),
        counters.get_counter(VAR_COUNTER)
    )
}

fn variables(ir: &Ir, root: StatId) -> String {
    let mut vars = BTreeMap::new();
    for stat in statements(ir, root) {
        let statement = &ir[stat];
        let mut extras = stat.stat_exprents(ir);
        if let StatementKind::CatchAll { vars, monitor, .. } = &statement.kind {
            extras.extend(vars);
            extras.extend(*monitor);
        }
        let body = statement
            .exprents
            .map_or(&[][..], |list| ir[list].as_slice());
        for &expr in body.iter().chain(&extras).chain(&statement.var_definitions) {
            for child in Expr::all_exprents(ir, expr, true, true) {
                if let ExprKind::Variable(_) = &ir[child].kind
                    && let Some(previous) = vars.insert(ir[child].id, child)
                {
                    assert_eq!(previous, child, "duplicate variable expression ID");
                }
            }
        }
    }
    vars.into_iter()
        .map(|(id, expr)| {
            let ExprKind::Variable(var) = &ir[expr].kind else {
                unreachable!()
            };
            format!("v{id}={}:{};", var.index, var.version)
        })
        .collect()
}

fn rewrites(ir: &Ir, root: StatId, rewrites: &InstructionRewrites) -> String {
    let mut located = HashSet::new();
    let mut entries = String::new();
    for stat in statements(ir, root)
        .into_iter()
        .sorted_by_key(|&stat| ir[stat].id)
    {
        let StatementKind::BasicBlock { block } = ir[stat].kind else {
            continue;
        };
        for (offset, instruction) in ir[block].seq.iter().enumerate() {
            if let Some(index) = rewrites.get(instruction) {
                located.insert(Arc::as_ptr(instruction));
                write!(entries, "i{}:{offset}={index};", ir[stat].id).unwrap();
            }
        }
    }
    assert_eq!(
        located.len(),
        rewrites.iter().count(),
        "rewrite points to an instruction outside the statement tree"
    );
    entries
}

fn statements(ir: &Ir, root: StatId) -> Vec<StatId> {
    let StatementKind::Root { dummy_exit, .. } = ir[root].kind else {
        unreachable!()
    };
    let mut statements = vec![root, dummy_exit];
    let mut index = 0;
    while let Some(&stat) = statements.get(index) {
        statements.extend(ir[stat].stats.iter().copied());
        index += 1;
    }
    statements
}
