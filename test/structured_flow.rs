// SPDX-License-Identifier: Apache-2.0

use std::collections::BTreeSet;
use std::fs;
use std::io::{self, BufWriter, Write};
use std::panic::{AssertUnwindSafe, catch_unwind};
#[path = "support/upstream_reference.rs"]
mod upstream_reference;
use std::sync::Arc;

use itertools::Itertools;

use vineflower_rs::code::cfg::ControlFlowGraph;
use vineflower_rs::decompiler::ir::{EdgeId, ExprId, ExprKind, Ir, StatId};
use vineflower_rs::decompiler::stats::stat_edge::EdgeType;
use vineflower_rs::decompiler::stats::{LastBasicType, STATEDGE_ALL, StatementKind};
use vineflower_rs::engine::counter_container::{
    EXPRESSION_COUNTER, STATEMENT_COUNTER, VAR_COUNTER,
};
use vineflower_rs::engine::method_processor::{
    StructuredMethod, initial_statement_graph, structured_statement_graph,
};
use vineflower_rs::engine::{Cx, Options};
use vineflower_rs::structs::{StructClass, StructContext};
use vineflower_rs::util::data_input::DataInputFullStream;

#[path = "support/direct_graph_snapshot.rs"]
mod direct_graph_snapshot;

#[test]
fn structure_retains_statement_and_edge_links() {
    let classes: &[&[u8]] = &[
        include_bytes!("smoke/java8/TestSimpleWhile.class"),
        include_bytes!("smoke/java8/TestClassSwitch.class"),
        include_bytes!("smoke/java8/TestCompoundAssignment.class"),
        include_bytes!("smoke/java16/TestRecordMixup.class"),
        include_bytes!("smoke/jasm/TestEnumStaticField.class"),
    ];
    let mut kinds = BTreeSet::new();
    for bytes in classes {
        let options = Arc::new(Options::default());
        let mut cx = make_context(&options);
        let class = parse_class(bytes, &options).unwrap();
        for method in &class.methods {
            let Some(structured) = structured_statement_graph(&mut cx, &class, method).unwrap()
            else {
                assert!(!method.contains_code());
                continue;
            };
            let ir = &cx.ir;
            let StatementKind::Root {
                dummy_exit,
                method: owner,
                ..
            } = &ir[structured.root].kind
            else {
                panic!("expected method root");
            };
            assert!(Arc::ptr_eq(owner, method));
            assert!(matches!(ir[*dummy_exit].kind, StatementKind::DummyExit));

            let mut pending = vec![structured.root];
            let mut visited = BTreeSet::new();
            while let Some(stat) = pending.pop() {
                assert!(
                    visited.insert(ir[stat].id),
                    "duplicate statement ID in {method}"
                );
                kinds.insert(kind_name(&ir[stat].kind));
                if let Some(first) = ir[stat].first {
                    assert!(ir[stat].stats.contains(&first));
                }
                for &child in &ir[stat].stats {
                    assert_eq!(ir[child].parent, Some(stat), "{method}");
                    pending.push(child);
                }
                for edge in stat.get_successor_edges(ir, STATEDGE_ALL) {
                    assert_eq!(ir[edge].source, stat, "{method}");
                    assert!(
                        ir[edge]
                            .destination
                            .get_predecessor_edges(ir, STATEDGE_ALL)
                            .contains(&edge),
                        "{method}"
                    );
                    // Upstream relabels switch case edges as regular without
                    // clearing their closure fields.
                    if ir[edge].edge_type != EdgeType::Regular
                        && let Some(closure) = ir[edge].closure
                    {
                        assert!(ir[closure].label_edges.contains(&edge), "{method}");
                    }
                }
                for &edge in &ir[stat].label_edges {
                    assert_eq!(ir[edge].closure, Some(stat), "{method}");
                }
            }
        }
    }
    for kind in ["ROOT", "BASIC_BLOCK", "DO", "SWITCH"] {
        assert!(
            kinds.contains(kind),
            "smoke classes did not exercise {kind}"
        );
    }
}

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn structured_flow_matches_upstream() {
    let corpus = upstream_reference::Corpus::discover();
    let paths = &corpus.classes;
    let mut transfer = tempfile::NamedTempFile::new().unwrap();
    let mut snapshots = Vec::new();
    {
        let mut transfer = BufWriter::new(transfer.as_file_mut());
        for path in paths {
            let bytes = fs::read(path).unwrap();
            for force_jsr_inline in [false, true] {
                let mut options = Options::default();
                options.force_jsr_inline = force_jsr_inline;
                let options = Arc::new(options);
                let class = parse_class(&bytes, &options).unwrap();
                let mut cx = make_context(&options);
                for method in &class.methods {
                    if !method.contains_code() {
                        continue;
                    }
                    let initial = initial_statement_graph(&mut cx, &class, method)
                        .unwrap()
                        .unwrap();
                    let record = i32::try_from(snapshots.len()).unwrap();
                    write_int(&mut transfer, record).unwrap();
                    write_text(&mut transfer, path.to_str().unwrap()).unwrap();
                    write_text(&mut transfer, &method.name).unwrap();
                    write_text(&mut transfer, &method.descriptor).unwrap();
                    write_flag(&mut transfer, force_jsr_inline).unwrap();
                    write_cfg(&mut transfer, &cx.ir, &initial.flow.graph).unwrap();

                    let result = catch_unwind(AssertUnwindSafe(|| initial.structure(&mut cx)));
                    let (snapshot, direct) = match result {
                        Ok(Ok(method)) => {
                            let statement = structure_snapshot(&cx.ir, &method);
                            let direct = catch_unwind(AssertUnwindSafe(|| {
                                direct_graph_snapshot::snapshot(&mut cx.ir, method.root)
                            }))
                            .unwrap_or_else(|error| format!("panic={}", panic_text(&*error)));
                            (statement, Some(direct))
                        }
                        Ok(Err(error))
                            if error.kind() == io::ErrorKind::InvalidData
                                && error.to_string() == "parsing failure!" =>
                        {
                            ("rejected=parsing failure!".to_owned(), None)
                        }
                        Ok(Err(error)) => (format!("error={error}"), None),
                        Err(error) => (format!("panic={}", panic_text(&*error)), None),
                    };
                    snapshots.push((
                        format!("{} {method} force-jsr={force_jsr_inline}", path.display()),
                        snapshot,
                        direct,
                    ));
                }
            }
        }
        write_int(&mut transfer, -1).unwrap();
        transfer.flush().unwrap();
    }

    let reference = corpus.run(
        "StructureReference",
        &["DirectGraphSnapshot"],
        transfer.path(),
    );
    let mut mismatches = Vec::new();
    let mut rejected = 0;
    let mut rows = reference.lines();
    for (index, (method, rust, rust_direct)) in snapshots.iter().enumerate() {
        let (row_id, java) = rows
            .next()
            .expect("missing Java result")
            .split_once('\t')
            .unwrap();
        assert_eq!(row_id.parse::<usize>().unwrap(), index);
        let (java, java_direct) = match java.split_once('\t') {
            Some((statement, direct)) => (statement, Some(direct)),
            None => (java, None),
        };
        if java == "rejected=parsing failure!" && java == rust {
            rejected += 1;
        } else if java != rust || java.starts_with("error=") {
            mismatches.push(format!("{method}\n  Structure {}", difference(java, rust)));
        } else if let (Some(java_direct), Some(rust_direct)) = (java_direct, rust_direct) {
            if java_direct != rust_direct || java_direct.starts_with("error=") {
                mismatches.push(format!(
                    "{method}\n  Direct graph {}",
                    difference(java_direct, rust_direct)
                ));
            }
        } else {
            mismatches.push(format!("{method}\n  Missing direct graph"));
        }
    }
    assert!(rows.next().is_none(), "unexpected extra Java results");
    assert!(
        mismatches.is_empty(),
        "{} of {} method snapshots differ:\n{}",
        mismatches.len(),
        snapshots.len(),
        mismatches.iter().take(30).join("\n")
    );
    eprintln!(
        "{} exact statement trees and direct graphs, and {rejected} matching decomposition rejections from {} class files",
        snapshots.len() - rejected,
        paths.len()
    );
}

fn difference(java: &str, rust: &str) -> String {
    java.split(';')
        .zip_longest(rust.split(';'))
        .find(|fields| !matches!(fields, itertools::EitherOrBoth::Both(java, rust) if java == rust))
        .map_or_else(
            || format!("both reported {java}"),
            |fields| format!("{fields:?}"),
        )
}

fn make_context(options: &Arc<Options>) -> Cx {
    Cx::new(Arc::new(StructContext::new(Arc::clone(options), None)))
}

fn parse_class(bytes: &[u8], options: &Options) -> io::Result<StructClass> {
    StructClass::create(&mut DataInputFullStream::new(bytes), true, options, None)
}

fn panic_text(error: &(dyn std::any::Any + Send)) -> &str {
    error
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| error.downcast_ref::<&str>().copied())
        .unwrap_or("unknown panic")
}

fn write_cfg(out: &mut impl Write, ir: &Ir, graph: &ControlFlowGraph) -> io::Result<()> {
    write_int(out, ir[graph.first].id)?;
    write_int(out, ir[graph.last].id)?;
    write_int(out, graph.last_id)?;
    write_flag(out, graph.add_error_comment)?;
    write_count(out, graph.comment_lines.len())?;
    for comment in &graph.comment_lines {
        write_text(out, comment)?;
    }
    write_count(out, graph.blocks.len())?;
    for &block in &graph.blocks {
        let block = &ir[block];
        write_int(out, block.id)?;
        write_ints(out, block.instr_old_offsets.iter().copied())?;
        write_ints(out, block.succs.iter().map(|&next| ir[next].id))?;
        write_ints(
            out,
            block.succ_exceptions.iter().map(|&handler| ir[handler].id),
        )?;
        write_int(out, block.seq.length())?;
        for instruction in &block.seq {
            write_int(out, i32::from(instruction.opcode))?;
            write_flag(out, instruction.wide)?;
            write_int(out, i32::from(instruction.group))?;
            write_int(out, instruction.start_offset)?;
            write_int(out, instruction.length)?;
            write_ints(
                out,
                (0..instruction.operands_count()).map(|index| instruction.operand(index)),
            )?;
        }
    }
    write_count(out, graph.exceptions.len())?;
    for range in &graph.exceptions {
        write_int(out, ir[range.handler].id)?;
        write_ints(out, range.protected_range.iter().map(|&block| ir[block].id))?;
        write_flag(out, range.exception_types.is_some())?;
        if let Some(types) = &range.exception_types {
            write_count(out, types.len())?;
            for class in types {
                write_text(out, class)?;
            }
        }
    }
    write_ints(out, graph.finally_exits.iter().map(|&block| ir[block].id))
}

fn write_ints(out: &mut impl Write, ints: impl ExactSizeIterator<Item = i32>) -> io::Result<()> {
    write_count(out, ints.len())?;
    for value in ints {
        write_int(out, value)?;
    }
    Ok(())
}

fn write_count(out: &mut impl Write, count: usize) -> io::Result<()> {
    write_int(out, i32::try_from(count).unwrap())
}

fn write_int(out: &mut impl Write, value: i32) -> io::Result<()> {
    out.write_all(&value.to_be_bytes())
}

fn write_flag(out: &mut impl Write, value: bool) -> io::Result<()> {
    out.write_all(&[u8::from(value)])
}

fn write_text(out: &mut impl Write, text: &str) -> io::Result<()> {
    write_count(out, text.len())?;
    out.write_all(text.as_bytes())
}

fn structure_snapshot(ir: &Ir, method: &StructuredMethod) -> String {
    let root = &ir[method.root];
    let StatementKind::Root {
        dummy_exit,
        comment_lines,
        add_error_comment,
        ..
    } = &root.kind
    else {
        unreachable!()
    };
    let counters = &method.flow.counters;
    let mut fields = vec![
        format!(
            "counters={},{},{}",
            counters.get_counter(STATEMENT_COUNTER),
            counters.get_counter(EXPRESSION_COUNTER),
            counters.get_counter(VAR_COUNTER)
        ),
        format!("error={add_error_comment}"),
        format!("comments={}", comment_lines.iter().flatten().join("|")),
    ];
    let mut pending = vec![*dummy_exit, method.root];
    while let Some(stat) = pending.pop() {
        let node = &ir[stat];
        let id = |stat| statement_id(ir, stat);
        let edge = |edge| edge_id(ir, edge);
        fields.push(format!("stat={}:{}", node.id, kind_name(&node.kind)));
        fields.push(format!(
            "tree={}/{}/{}/{}",
            id(node.parent),
            id(node.first),
            id(node.post),
            node.stats.iter().map(|&stat| ir[stat].id).join(",")
        ));
        let last_basic = match node.last_basic_type {
            LastBasicType::General => "GENERAL",
            LastBasicType::If => "IF",
            LastBasicType::Switch => "SWITCH",
        };
        fields.push(format!(
            "flags={last_basic}/{}/{}/{}/{}",
            node.is_monitor_enter,
            node.contains_monitor_exit_or_athrow(),
            node.contains_monitor_exit,
            node.copied
        ));
        fields.push(format!(
            "out={}",
            stat.get_successor_edges(ir, STATEDGE_ALL)
                .iter()
                .map(|&e| edge(Some(e)))
                .join("|")
        ));
        fields.push(format!(
            "labels={}",
            node.label_edges
                .iter()
                .map(|&e| edge(Some(e)))
                .sorted()
                .join("|")
        ));
        match &node.kind {
            StatementKind::If(branch) => fields.push(format!(
                "if={}/{}/{}/{}/{}/{}",
                branch.has_else,
                branch.negated,
                id(branch.if_stat),
                id(branch.else_stat),
                edge(branch.if_edge),
                edge(branch.else_edge),
            )),
            StatementKind::Switch(switch) => fields.push(format!(
                "switch={}/{}",
                edge(switch.default_edge),
                switch
                    .cases
                    .iter()
                    .map(|case| format!(
                        "{}:{}:{}",
                        ir[case.statement].id,
                        case.edges.iter().map(|&e| edge(Some(e))).join("|"),
                        case.values
                            .iter()
                            .map(|&expr| expression(ir, expr))
                            .join("|")
                    ))
                    .join("/")
            )),
            StatementKind::Catch {
                exceptions, vars, ..
            } => fields.push(format!(
                "catch={}/{}",
                exceptions
                    .iter()
                    .map(|types| types.iter().join(","))
                    .join("|"),
                vars.iter()
                    .map(|&expr| expression(ir, Some(expr)))
                    .join("|")
            )),
            StatementKind::CatchAll {
                handler,
                is_finally,
                monitor,
                vars,
            } => fields.push(format!(
                "catch-all={}/{}/{}/{}",
                id(*handler),
                is_finally,
                expression(ir, *monitor),
                vars.iter()
                    .map(|&expr| expression(ir, Some(expr)))
                    .join("|")
            )),
            StatementKind::Synchronized { body, .. } => {
                fields.push(format!("monitor={}", ir[*body].id))
            }
            _ => {}
        }
        pending.extend(node.stats.iter().rev().copied());
    }
    fields.join(";")
}

fn kind_name(kind: &StatementKind) -> &'static str {
    match kind {
        StatementKind::BasicBlock { .. } => "BASIC_BLOCK",
        StatementKind::General { .. } => "GENERAL",
        StatementKind::Sequence => "SEQUENCE",
        StatementKind::Do => "DO",
        StatementKind::If(_) => "IF",
        StatementKind::Switch(_) => "SWITCH",
        StatementKind::Catch { .. } => "TRY_CATCH",
        StatementKind::CatchAll { .. } => "CATCH_ALL",
        StatementKind::Synchronized { .. } => "SYNCHRONIZED",
        StatementKind::Root { .. } => "ROOT",
        StatementKind::DummyExit => "DUMMY_EXIT",
    }
}

fn statement_id(ir: &Ir, stat: Option<StatId>) -> String {
    stat.map_or_else(|| "-".to_owned(), |stat| ir[stat].id.to_string())
}

fn edge_id(ir: &Ir, edge: Option<EdgeId>) -> String {
    edge.map_or_else(
        || "-".to_owned(),
        |edge| {
            let edge = &ir[edge];
            format!(
                "{},{},{},{},{},{},{},{},{}",
                edge.edge_type.mask(),
                ir[edge.source].id,
                ir[edge.destination].id,
                statement_id(ir, edge.closure),
                edge.labeled,
                edge.explicit,
                edge.can_inline,
                edge.phantom_continue,
                edge.exceptions
                    .as_ref()
                    .map_or_else(|| "*".to_owned(), |types| types.iter().join(","))
            )
        },
    )
}

fn expression(ir: &Ir, expr: Option<ExprId>) -> String {
    expr.map_or_else(
        || "-".to_owned(),
        |expr| {
            let expr = &ir[expr];
            match expr.kind {
                ExprKind::IntConstant { value, .. } => format!("{}={value}", expr.id),
                ExprKind::Variable { index } => format!(
                    "{}={index}:{}",
                    expr.id,
                    expr.var_type.value.as_deref().unwrap_or("*")
                ),
            }
        },
    )
}
