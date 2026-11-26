// SPDX-License-Identifier: Apache-2.0

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::fs;
use std::io::{self, Write as _};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::PathBuf;
#[path = "support/control_flow_snapshot.rs"]
mod control_flow_snapshot;
use control_flow_snapshot::snapshot;

#[path = "support/upstream_reference.rs"]
mod upstream_reference;
use std::sync::Arc;

use itertools::Itertools;

use vineflower_rs::code::cfg::ControlFlowGraph;
use vineflower_rs::decompiler::decompose::dom_helper::graph_to_statement;
use vineflower_rs::decompiler::decompose::extended_postdominance::extended_postdominators;
use vineflower_rs::decompiler::decompose::statement_order::{
    calc_post_dominators, components, post_reverse_post_order, reverse_post_order,
};
use vineflower_rs::decompiler::ir::{Ir, StatId};
use vineflower_rs::decompiler::stats::StatementKind;
use vineflower_rs::engine::counter_container::{STATEMENT_COUNTER, VAR_COUNTER};
use vineflower_rs::engine::method_processor::{DecodedMethod, initial_statement_graph};
use vineflower_rs::engine::{Cx, Options};
use vineflower_rs::structs::{StructClass, StructContext};
use vineflower_rs::util::data_input::DataInputFullStream;

#[test]
fn control_flow_invariants_with_bundled_classes() {
    let classes: &[&[u8]] = &[
        include_bytes!("smoke/java8/TestSimpleWhile.class"),
        include_bytes!("smoke/java8/TestClassSwitch.class"),
        include_bytes!("smoke/java8/TestCompoundAssignment.class"),
        include_bytes!("smoke/java16/TestRecordMixup.class"),
        include_bytes!("smoke/jasm/TestEnumStaticField.class"),
    ];
    for &bytes in classes {
        for force_jsr_inline in [false, true] {
            let mut options = Options::default();
            options.force_jsr_inline = force_jsr_inline;
            let class = parse_class(bytes, &options).unwrap();
            let mut ir = Ir::default();
            for method in &class.methods {
                let Some(decoded) = DecodedMethod::from_method(&mut ir, &class, method).unwrap()
                else {
                    continue;
                };
                let label = format!(
                    "{}.{}{}",
                    class.qualified_name, method.name, method.descriptor
                );
                check_graph(&label, &ir, &decoded.flow.graph, false);
                let common = decoded.prepare_control_flow(&mut ir, &options);
                check_graph(&label, &ir, &common.flow.graph, true);
                let method_graph = common.prepare_java_graph(&mut ir, &options);
                check_graph(&label, &ir, &method_graph.graph, true);
            }
        }
    }
}

#[test]
fn initial_statements_keep_method_identity_and_counters() {
    let options = Arc::new(Options::default());
    let mut cx = Cx::new(Arc::new(StructContext::new(Arc::clone(&options), None)));
    let bytes: &[u8] = include_bytes!("upstream/testData/classes/custom/TestJsr.class");
    let class = parse_class(bytes, &options).unwrap();
    let mut roots = Vec::new();
    for method in &class.methods {
        let Some(initial) = initial_statement_graph(&mut cx, &class, method).unwrap() else {
            assert!(!method.contains_code());
            continue;
        };
        let root = &cx.ir[initial.root];
        let StatementKind::Root {
            dummy_exit,
            comment_lines,
            add_error_comment,
            ..
        } = &root.kind
        else {
            panic!("expected a root statement for {method}");
        };
        assert!(matches!(
            cx.ir[*dummy_exit].kind,
            StatementKind::DummyExit { .. }
        ));
        assert_eq!(cx.ir[root.first.unwrap()].parent, Some(initial.root));
        assert_eq!(
            root.id + 1,
            initial.flow.counters.get_counter(STATEMENT_COUNTER)
        );
        assert_eq!(
            method.local_variables,
            initial.flow.counters.get_counter(VAR_COUNTER)
        );
        assert!(
            comment_lines
                .iter()
                .flat_map(|lines| lines.iter())
                .eq(&initial.flow.graph.comment_lines)
        );
        assert_eq!(*add_error_comment, initial.flow.graph.add_error_comment);
        roots.push((initial.root, Arc::clone(method)));
    }

    assert!(roots.len() > 1);
    for (root, method) in roots {
        assert!(
            matches!(&cx.ir[root].kind, StatementKind::Root { method: owner, .. } if Arc::ptr_eq(owner, &method))
        );
    }

    let library =
        StructClass::create(&mut DataInputFullStream::new(bytes), false, &options, None).unwrap();
    for method in &library.methods {
        assert!(
            initial_statement_graph(&mut cx, &library, method)
                .unwrap()
                .is_none()
        );
    }
}

fn check_graph(label: &str, ir: &Ir, graph: &ControlFlowGraph, connected_exit: bool) {
    let real_blocks: HashSet<_> = graph.blocks.iter().copied().collect();
    assert_eq!(real_blocks.len(), graph.blocks.len(), "{label}");
    assert!(real_blocks.contains(&graph.first), "{label}");
    assert!(!real_blocks.contains(&graph.last), "{label}");
    assert!(ir[graph.last].succs.is_empty(), "{label}");
    for &block in &graph.blocks {
        assert_eq!(
            graph.blocks.get_with_key(&ir[block].id),
            Some(&block),
            "{label}"
        );
        for &target in &ir[block].succs {
            assert!(
                real_blocks.contains(&target) || target == graph.last && connected_exit,
                "{label}"
            );
            assert_eq!(
                ir[block]
                    .succs
                    .iter()
                    .filter(|&&next| next == target)
                    .count(),
                ir[target]
                    .preds
                    .iter()
                    .filter(|&&previous| previous == block)
                    .count(),
                "{label} regular edge {} -> {}",
                ir[block].id,
                ir[target].id
            );
        }
        for &predecessor in &ir[block].preds {
            assert!(real_blocks.contains(&predecessor), "{label}");
            assert!(ir[predecessor].succs.contains(&block), "{label}");
        }
        for &handler in &ir[block].succ_exceptions {
            assert!(real_blocks.contains(&handler), "{label}");
            assert!(ir[handler].pred_exceptions.contains(&block), "{label}");
            assert!(
                graph.get_exception_range(handler, block).is_some(),
                "{label}"
            );
        }
        for &protected in &ir[block].pred_exceptions {
            assert!(real_blocks.contains(&protected), "{label}");
            assert!(ir[protected].succ_exceptions.contains(&block), "{label}");
        }
    }
    for range in &graph.exceptions {
        assert!(real_blocks.contains(&range.handler), "{label}");
        for &protected in &range.protected_range {
            assert!(real_blocks.contains(&protected), "{label}");
            assert!(
                ir[protected].succ_exceptions.contains(&range.handler),
                "{label}"
            );
        }
    }
    for &predecessor in &ir[graph.last].preds {
        assert!(real_blocks.contains(&predecessor), "{label}");
        assert_eq!(
            ir[predecessor].succs.contains(&graph.last),
            connected_exit,
            "{label}"
        );
    }

    let mut reachable = HashSet::new();
    let mut pending = vec![graph.first];
    while let Some(block) = pending.pop() {
        if reachable.insert(block) {
            pending.extend(
                ir[block]
                    .succs
                    .iter()
                    .chain(&ir[block].succ_exceptions)
                    .copied(),
            );
        }
    }
    let rpo = graph.get_reverse_post_order(ir);
    assert_eq!(rpo.first(), Some(&graph.first), "{label}");
    assert_eq!(rpo.len(), reachable.len(), "{label}");
    assert_eq!(
        rpo.into_iter().collect::<HashSet<_>>(),
        reachable,
        "{label}"
    );
}

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn control_flow_matches_upstream() {
    let corpus = upstream_reference::Corpus::discover();
    let class_paths = &corpus.classes;
    let mut class_list = tempfile::NamedTempFile::new().unwrap();
    for class_path in class_paths {
        writeln!(class_list, "{}", class_path.display()).unwrap();
    }
    class_list.flush().unwrap();
    let reference = corpus.run("ControlFlowReference", &[], class_list.path());
    let mut expected = BTreeMap::new();
    for line in reference.lines() {
        let (key, snapshot) = line.rsplit_once('\t').unwrap();
        assert!(
            expected.insert(key, snapshot).is_none(),
            "duplicate Java record {key}"
        );
    }
    let actual = rust_snapshots(class_paths);
    let keys: BTreeSet<_> = expected
        .keys()
        .copied()
        .chain(actual.keys().map(String::as_str))
        .collect();
    let mut mismatches = Vec::new();
    let mut exact = 0;
    let mut equivalent = 0;
    let mut reordered_splits = 0;
    let mut postdominance = 0;
    let mut basic_roots = 0;
    let mut remapped_methods = BTreeSet::new();
    let mut remapped_postdominance = 0;
    let mut failures = 0;
    for key in keys {
        let java = expected.get(key).copied();
        let rust = actual.get(key).map(String::as_str);
        let boundary = java.and_then(|value| {
            let (boundary, snapshot) = value
                .strip_prefix("handler-order-boundary=")?
                .split_once(';')?;
            let (last_id, range_count) = boundary.split_once(',')?;
            Some((
                last_id.parse::<i32>().unwrap(),
                range_count.parse::<usize>().unwrap(),
                snapshot,
            ))
        });
        let java = boundary.map(|(_, _, snapshot)| snapshot).or(java);
        let dominance_method = key.strip_suffix("\tpostdominance");
        if dominance_method.is_none()
            && java.is_some_and(|snapshot| snapshot.starts_with("error="))
            && rust.is_some_and(|snapshot| snapshot.starts_with("error="))
        {
            failures += 1;
        } else if java == rust
            && let Some(snapshot) = java.filter(|value| !value.starts_with("error="))
        {
            if dominance_method.is_some() {
                if snapshot.starts_with("basic=") {
                    basic_roots += 1;
                } else {
                    postdominance += 1;
                }
            } else if !key.ends_with("\tload") {
                exact += 1;
            }
        } else if let Some((last_id, _, java)) = boundary
            && let Some(rust) = rust.filter(|value| !value.starts_with("error="))
            && matching_new_handlers(java, rust, last_id, None)
        {
            equivalent += 1;
            remapped_methods.insert(key.strip_suffix("\tjava").unwrap());
        } else if let Some((last_id, range_count, java)) = boundary
            && let Some(rust) = rust.filter(|value| !value.starts_with("error="))
            && matching_new_handlers(java, rust, last_id, Some(range_count))
        {
            reordered_splits += 1;
            remapped_methods.insert(key.strip_suffix("\tjava").unwrap());
        } else if dominance_method.is_some_and(|method| remapped_methods.contains(method))
            && java.is_some_and(|snapshot| !snapshot.starts_with("error="))
            && rust.is_some_and(|snapshot| !snapshot.starts_with("error="))
        {
            // The preceding Java CFG comparison established a difference in the
            // input block order or IDs. Both dominance computations must succeed.
            remapped_postdominance += 1;
        } else {
            let (index, method) = key.split_once('\t').unwrap();
            let class = &class_paths[index.parse::<usize>().unwrap()];
            let difference = describe_difference(java, rust);
            mismatches.push(format!("{} {method}: {difference}", class.display()));
        }
    }
    eprintln!(
        "{} class files, default and forced-JSR: {exact} exact CFG snapshots, {equivalent} equivalent after mapping new handler IDs, {reordered_splits} equivalent after also ordering disjoint split ranges, {failures} matched failure stages.",
        class_paths.len(),
    );
    eprintln!(
        "{postdominance} exact postdominance snapshots, {basic_roots} matched single-block roots, and {remapped_postdominance} pairs with equivalent CFGs and different inputs to postdominance."
    );
    assert!(
        mismatches.is_empty(),
        "{} control-flow mismatches:\n{}",
        mismatches.len(),
        mismatches.iter().take(30).join("\n")
    );
}

fn parse_class(bytes: &[u8], options: &Options) -> io::Result<StructClass> {
    StructClass::create(&mut DataInputFullStream::new(bytes), true, options, None)
}

fn rust_snapshots(paths: &[PathBuf]) -> BTreeMap<String, String> {
    let mut records = BTreeMap::new();
    for (index, path) in paths.iter().enumerate() {
        let bytes = fs::read(path).unwrap();
        for (mode, force_jsr_inline) in [("default", false), ("force-jsr", true)] {
            let key = format!("{index}\t{mode}");
            let mut options = Options::default();
            options.force_jsr_inline = force_jsr_inline;
            let Some(class) = record_stage(&mut records, format!("{key}\t<class>\tload"), || {
                let class = parse_class(&bytes, &options).map_err(|error| error.to_string())?;
                let name = class.qualified_name.to_string();
                Ok((class, name))
            }) else {
                continue;
            };
            let mut ir = Ir::default();
            for method in &class.methods {
                if !method.contains_code() {
                    continue;
                }
                let key = format!("{key}\t{}{}", method.name, method.descriptor);
                let Some(decoded) = record_stage(&mut records, format!("{key}\tconstruct"), || {
                    let graph = DecodedMethod::from_method(&mut ir, &class, method)
                        .map_err(|error| error.to_string())?
                        .ok_or("missing graph for method with code")?;
                    let snapshot = snapshot(&ir, &graph.flow.graph, true);
                    Ok((graph, snapshot))
                }) else {
                    continue;
                };
                let common = record_stage(&mut records, format!("{key}\tcommon"), || {
                    let common = decoded.prepare_control_flow(&mut ir, &options);
                    let snapshot = snapshot(&ir, &common.flow.graph, false);
                    Ok((common, snapshot))
                });
                if let Some(common) = common
                    && let Some(mut flow) =
                        record_stage(&mut records, format!("{key}\tjava"), || {
                            let flow = common.prepare_java_graph(&mut ir, &options);
                            let snapshot = snapshot(&ir, &flow.graph, false);
                            Ok((flow, snapshot))
                        })
                {
                    record_stage(&mut records, format!("{key}\tpostdominance"), || {
                        let root = graph_to_statement(
                            &mut ir,
                            &mut flow.counters,
                            &flow.graph,
                            Arc::clone(method),
                        );
                        Ok(((), postdominance_snapshot(&ir, ir[root].first.unwrap())))
                    });
                }
            }
        }
    }
    records
}

fn record_stage<T>(
    records: &mut BTreeMap<String, String>,
    key: String,
    run: impl FnOnce() -> Result<(T, String), String>,
) -> Option<T> {
    let result = catch_unwind(AssertUnwindSafe(run)).unwrap_or_else(|panic| {
        let message = panic
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| panic.downcast_ref::<&str>().copied())
            .unwrap_or("unknown panic");
        Err(message.to_owned())
    });
    match result {
        Ok((value, snapshot)) => {
            assert!(records.insert(key, snapshot).is_none());
            Some(value)
        }
        Err(error) => {
            assert!(records.insert(key, format!("error={error}")).is_none());
            None
        }
    }
}

fn postdominance_snapshot(ir: &Ir, statement: StatId) -> String {
    if !matches!(ir[statement].kind, StatementKind::General { .. }) {
        return format!("basic={}", ir[statement].id);
    }
    let ids = |statements: &[StatId]| statements.iter().map(|&stat| ir[stat].id).join(",");
    let rpo = ids(&reverse_post_order(ir, statement));
    let post_rpo = ids(&post_reverse_post_order(ir, statement));
    let components = components(ir, statement)
        .iter()
        .map(|component| ids(component))
        .join("/");
    let postdominators = calc_post_dominators(ir, statement);
    let post = postdominators
        .lst_keys()
        .iter()
        .zip(postdominators.iter())
        .map(|(head, posts)| format!("{}:{}", head.unwrap(), posts.iter().join(",")))
        .join("/");
    let extended = extended_postdominators(ir, statement)
        .iter()
        .map(|(head, posts)| format!("{head}:{}", posts.iter().join(",")))
        .join("/");
    format!("rpo={rpo};post-rpo={post_rpo};components={components};post={post};extended={extended}")
}

fn matching_new_handlers(
    java: &str,
    rust: &str,
    last_id: i32,
    original_range_count: Option<usize>,
) -> bool {
    normalize_handler_ids(java, last_id, original_range_count)
        .zip(normalize_handler_ids(rust, last_id, original_range_count))
        .is_some_and(|(java, rust)| java == rust)
}

// Java's final handler deduplication visits a map keyed by object identity.
// Give only those appended handler blocks stable IDs, in exception-table order.
// A single bijection applies to block records, all graph references and RPO.
fn normalize_handler_ids(
    snapshot: &str,
    old_last_id: i32,
    original_range_count: Option<usize>,
) -> Option<String> {
    let mut fields: Vec<_> = snapshot.split(';').collect();
    let last_id: i32 = fields[2].strip_prefix("last-id=")?.parse().ok()?;
    if old_last_id >= last_id {
        return None;
    }

    if let Some(original_range_count) = original_range_count {
        order_disjoint_split_ranges(&mut fields, original_range_count, old_last_id)?;
    }

    let mut handler_ids = BTreeMap::new();
    for range in fields
        .iter()
        .filter_map(|field| field.strip_prefix("range="))
    {
        let (handler, _) = range.split_once(':')?;
        let handler: i32 = handler.parse().ok()?;
        if handler > old_last_id {
            let stable_id = old_last_id + 1 + handler_ids.len() as i32;
            if handler_ids.insert(handler, stable_id).is_some() {
                return None;
            }
        }
    }
    if !handler_ids.keys().copied().eq(old_last_id + 1..=last_id) {
        return None;
    }

    let remap = |id: &str| {
        let id: i32 = id.parse().unwrap();
        handler_ids.get(&id).copied().unwrap_or(id)
    };
    let remap_list = |ids: &str| {
        ids.split(',')
            .filter(|id| !id.is_empty())
            .map(remap)
            .collect::<Vec<_>>()
            .into_iter()
    };
    let rewrite = |field: &str| {
        let (name, value) = field.split_once('=').unwrap();
        let value = match name {
            "first" | "last" | "block" => remap(value).to_string(),
            "edges" | "exception-edges" | "rpo" => remap_list(value).join(","),
            "exit-predecessors" | "finally-exits" => remap_list(value).sorted().join(","),
            "range" => {
                let (handler, rest) = value.split_once(':').unwrap();
                let (types, members) = rest.rsplit_once(':').unwrap();
                format!(
                    "{}:{types}:{}",
                    remap(handler),
                    remap_list(members).sorted().join(",")
                )
            }
            _ => value.to_owned(),
        };
        format!("{name}={value}")
    };

    let block_end = fields
        .iter()
        .position(|field| field.starts_with("exit-predecessors="))?;
    let mut blocks = fields[3..block_end].chunks_exact(5);
    let mut original = Vec::new();
    let mut appended = BTreeMap::new();
    for fields in blocks.by_ref() {
        let id = remap(fields[0].strip_prefix("block=")?);
        let block = fields.iter().map(|field| rewrite(field)).join(";");
        if id > old_last_id {
            if appended.insert(id, block).is_some() {
                return None;
            }
        } else if appended.is_empty() {
            original.push(block);
        } else {
            return None;
        }
    }
    if !blocks.remainder().is_empty() || !appended.keys().copied().eq(old_last_id + 1..=last_id) {
        return None;
    }
    Some(
        fields[..3]
            .iter()
            .map(|field| rewrite(field))
            .chain(original)
            .chain(appended.into_values())
            .chain(fields[block_end..].iter().map(|field| rewrite(field)))
            .join(";"),
    )
}

// When splitting a range, Java picks the next entry from an identity set.
// Compare only the changed and appended tail of the table out of order, and
// only when its coverage is disjoint and every handler comes from deduplication.
fn order_disjoint_split_ranges(
    fields: &mut [&str],
    original_range_count: usize,
    old_last_id: i32,
) -> Option<()> {
    let first_range = fields
        .iter()
        .position(|field| field.starts_with("range="))?;
    let range_end = fields
        .iter()
        .position(|field| field.starts_with("finally-exits="))?;
    let split_ranges = fields.get_mut(first_range + original_range_count..range_end)?;
    if split_ranges.len() < 2 {
        return None;
    }
    let mut all_members = HashSet::new();
    for range in split_ranges.iter() {
        let (handler, rest) = range.strip_prefix("range=")?.split_once(':')?;
        let (_, members) = rest.rsplit_once(':')?;
        if handler.parse::<i32>().ok()? <= old_last_id
            || members.is_empty()
            || !members.split(',').all(|member| all_members.insert(member))
        {
            return None;
        }
    }
    split_ranges.sort_unstable_by_key(|range| range.split_once(':').unwrap().1);
    Some(())
}

fn describe_difference(java: Option<&str>, rust: Option<&str>) -> String {
    let (Some(java), Some(rust)) = (java, rust) else {
        return format!(
            "record present in {} only",
            if java.is_some() { "Java" } else { "Rust" }
        );
    };
    let mut block = "";
    for field in java.split(';').zip_longest(rust.split(';')) {
        match field {
            itertools::EitherOrBoth::Both(java, rust) if java == rust => {
                if java.starts_with("block=") {
                    block = java;
                }
            }
            field => return format!("after {block:?}, Java vs Rust {field:?}"),
        }
    }
    format!("both reported {java:?}")
}
