// SPDX-License-Identifier: Apache-2.0

use std::collections::{BTreeSet, HashMap};
use std::fs;
use std::io::{self, BufRead, BufReader, BufWriter, Seek, Write};
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
    CounterContainer, EXPRESSION_COUNTER, STATEMENT_COUNTER, VAR_COUNTER,
};
use vineflower_rs::engine::import_collector::ImportCollector;
use vineflower_rs::engine::method_processor::{
    initial_statement_graph, structured_statement_graph,
};
use vineflower_rs::engine::{Cx, Options};
use vineflower_rs::structs::{StructClass, StructContext, consts::ConstantValue};
use vineflower_rs::util::data_input::DataInputFullStream;

#[path = "support/direct_graph_snapshot.rs"]
mod direct_graph_snapshot;
#[path = "support/expression_snapshot.rs"]
mod expression_snapshot;
#[path = "support/finally_snapshot.rs"]
mod finally_snapshot;
#[path = "support/ssa_snapshot.rs"]
mod ssa_snapshot;
#[path = "support/stack_snapshot.rs"]
mod stack_snapshot;

const REFERENCE_HELPERS: &[&str] = &[
    "DirectGraphSnapshot",
    "ExpressionSnapshot",
    "SsaSnapshot",
    "FinallySnapshot",
    "StackSnapshot",
    "VariableSnapshot",
];

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
fn structured_method_lifts_switch_expressions() {
    let options = Arc::new(Options::default());
    let mut cx = make_context(&options);
    let class = parse_class(
        include_bytes!("smoke/java8/TestClassSwitch.class"),
        &options,
    )
    .unwrap();
    let method = class.get_method("testCaseOrder", "(I)V").unwrap();
    let mut structured = structured_statement_graph(&mut cx, &class, method)
        .unwrap()
        .unwrap();
    let initial_count = structured.flow.counters.get_counter(EXPRESSION_COUNTER);

    structured.process_expressions(&mut cx, &class).unwrap();

    assert!(structured.flow.counters.get_counter(EXPRESSION_COUNTER) > initial_count);
    let ir = &cx.ir;
    let mut pending = vec![structured.root];
    while let Some(stat) = pending.pop() {
        let statement = &ir[stat];
        if let StatementKind::Switch(branch) = &statement.kind {
            let head = ir[branch.head_exprents.expect("switch header")][0];
            let ExprKind::SwitchHead { value, .. } = &ir[head].kind else {
                panic!("expected a switch head expression");
            };
            assert!(matches!(&ir[*value].kind, ExprKind::Variable(var) if var.stack));
            let body = ir[statement.first.unwrap()].exprents.unwrap();
            assert!(
                ir[body]
                    .iter()
                    .any(|&expr| { matches!(&ir[expr].kind, ExprKind::Assignment { .. }) })
            );
            return;
        }
        pending.extend(statement.stats.iter().copied());
    }
    panic!("fixture contains no switch");
}

#[test]
fn stack_simplification_inlines_switch_selector_and_call_operands() {
    use vineflower_rs::decompiler::exps::Expr;
    use vineflower_rs::engine::method_processor::expression_method;

    let options = Arc::new(Options::default());
    let class = parse_class(
        include_bytes!("smoke/java8/TestClassSwitch.class"),
        &options,
    )
    .unwrap();
    let method = class.get_method("testCaseOrder", "(I)V").unwrap();
    let mut cx = make_context(&options);
    let mut lifted = expression_method(&mut cx, &class, method).unwrap().unwrap();
    lifted.simplify_stack_vars(&mut cx, &class);

    let ir = &cx.ir;
    let mut pending = vec![lifted.root];
    let mut arguments = Vec::new();
    let mut selectors = Vec::new();
    while let Some(stat) = pending.pop() {
        pending.extend(ir[stat].stats.iter().copied());
        if let StatementKind::Switch(switch) = &ir[stat].kind {
            let head = ir[switch.head_exprents.unwrap()][0];
            let ExprKind::SwitchHead { value, .. } = ir[head].kind else {
                panic!("expected switch head");
            };
            let ExprKind::Variable(var) = &ir[value].kind else {
                panic!("expected the switch argument");
            };
            assert!(!var.stack);
            selectors.push((var.index, var.version));
        }
        for &expr in ir[stat].exprents.into_iter().flat_map(|list| &ir[list]) {
            for id in Expr::all_exprents(ir, expr, true, true) {
                let ExprKind::Invocation(call) = &ir[id].kind else {
                    continue;
                };
                assert_eq!(call.name, "println");
                let receiver = call.instance.expect("PrintStream receiver");
                assert!(matches!(&ir[receiver].kind, ExprKind::Field(f)
                    if f.classname.as_deref() == Some("java/lang/System") && f.name == "out"));
                let [arg] = call.parameters[..] else {
                    panic!("expected one argument")
                };
                let ExprKind::Constant {
                    value: ConstantValue::Integer(n),
                    ..
                } = ir[arg].kind
                else {
                    panic!("expected the case's integer argument")
                };
                arguments.push(n);
            }
        }
    }
    arguments.sort_unstable();
    assert_eq!(selectors, [(1, 0)]);
    assert_eq!(arguments, [5, 13]);
}

#[test]
fn inferred_receiver_types_follow_their_own_methods() {
    use vineflower_rs::decompiler::exps::{Expr, InvocationFunction};
    use vineflower_rs::engine::method_processor::{ExpressionMethod, expression_method};
    use vineflower_rs::types::CodeType;

    fn receiver(cx: &mut Cx, method: &ExpressionMethod) -> ExprId {
        let graph =
            vineflower_rs::decompiler::flow::flatten::build_direct_graph(&mut cx.ir, method.root);
        graph
            .regular_breadth_first()
            .flat_map(|node| &cx.ir[graph[node].exprents])
            .find_map(|&expr| match &cx.ir[expr].kind {
                ExprKind::Invocation(call) if call.function == InvocationFunction::Init => {
                    call.instance
                }
                _ => None,
            })
            .expect("the constructor calls its superclass")
    }

    let mut options = Options::default();
    options.use_lvt_names = false;
    let options = Arc::new(options);
    let mut cx = make_context(&options);
    let mut receivers = Vec::new();
    for bytes in [
        include_bytes!("smoke/java8/TestClassSwitch.class").as_slice(),
        include_bytes!("smoke/java8/TestSimpleWhile.class"),
    ] {
        let class = parse_class(bytes, &options).unwrap();
        let ctor = class.get_method("<init>", "()V").unwrap();
        let mut method = expression_method(&mut cx, &class, ctor).unwrap().unwrap();
        method.process_increments(&mut cx, &class).unwrap();
        receivers.push((receiver(&mut cx, &method), class.qualified_name));
    }
    for (id, class_name) in receivers {
        let ExprKind::Variable(var) = &cx.ir[id].kind else {
            panic!("expected local this")
        };
        assert_eq!(var.index, 0);
        assert_eq!(var.var_type.ty, CodeType::Unknown);
        assert_eq!(Expr::expr_type(&cx, id).value, Some(class_name));
    }
}

#[test]
fn pre_main_recovers_the_order_of_dynamic_string_concatenation() {
    use vineflower_rs::decompiler::exps::FunctionType;
    use vineflower_rs::engine::method_processor::pre_main_method;

    let options = Arc::new(Options::default());
    let class = parse_class(
        include_bytes!("upstream/testData/classes/custom/TestStringConcatJ19.class"),
        &options,
    )
    .unwrap();
    let mut cx = make_context(&options);
    let descriptor = "(Ljava/lang/String;Ljava/lang/Object;Ljava/lang/Number;)Ljava/lang/String;";
    let method = class.get_method("test", descriptor).unwrap();
    let result = pre_main_method(&mut cx, &class, method).unwrap().unwrap();
    let head = result.root.get_basic_head(&cx.ir);
    let [ret] = cx.ir[cx.ir[head].exprents.unwrap()][..] else {
        panic!("expected one return")
    };
    let ExprKind::Exit {
        value: Some(sum), ..
    } = cx.ir[ret].kind
    else {
        panic!("expected a return value")
    };
    let operands = |id: ExprId| match &cx.ir[id].kind {
        ExprKind::Function {
            op: FunctionType::StrConcat,
            operands,
            ..
        } => operands.as_slice(),
        expr => panic!("expected string concatenation, got {expr:?}"),
    };
    let &[prefix, last] = operands(sum) else {
        panic!("expected binary concatenation")
    };
    let &[first, second] = operands(prefix) else {
        panic!("expected binary concatenation")
    };
    let slots = [first, second, last].map(|id| match &cx.ir[id].kind {
        ExprKind::Variable(var) => var.index,
        expr => panic!("expected a method argument, got {expr:?}"),
    });
    assert_eq!(slots, [1, 2, 3]);
}

#[test]
fn redundant_loop_elimination_keeps_the_enclosing_loops() {
    use vineflower_rs::engine::method_processor::pre_main_method;

    let options = Arc::new(Options::default());
    let class = parse_class(
        include_bytes!("smoke/java8/TestNestedLoops.class"),
        &options,
    )
    .unwrap();
    let mut cx = make_context(&options);
    let method = class.get_method("decomp", "()V").unwrap();
    let mut result = pre_main_method(&mut cx, &class, method).unwrap().unwrap();
    result.clean_up_edges(&mut cx);
    let root = result.root;
    let loop_count = |ir: &Ir| {
        structure_statements(ir, root)
            .filter(|&stat| matches!(ir[stat].kind, StatementKind::Do))
            .count()
    };
    let before = loop_count(&cx.ir);
    assert!(result.eliminate_loops(&mut cx, &class).unwrap());
    assert_eq!(loop_count(&cx.ir), before - 1);
    assert!(before > 2);
    assert!(!result.eliminate_loops(&mut cx, &class).unwrap());
}

#[test]
fn expression_method_recovers_finally_around_a_synchronized_body() {
    use vineflower_rs::engine::method_processor::expression_method;

    let bytes = include_bytes!("upstream/testData/classes/custom/TestJava1Synchronized.class");
    for deinline in [true, false] {
        let mut options = Options::default();
        options.decompile_finally = deinline;
        let options = Arc::new(options);
        let class = parse_class(bytes, &options).unwrap();
        let mut cx = make_context(&options);
        let method = class.get_method("test3", "()V").unwrap();
        let result = expression_method(&mut cx, &class, method).unwrap().unwrap();
        assert!(Arc::ptr_eq(result.root.method(&cx.ir), method));
        assert_eq!(result.synthetic_semaphores.is_empty(), deinline);

        let mut synchronized = false;
        let mut finally = false;
        let mut pending = vec![result.root];
        while let Some(stat) = pending.pop() {
            let statement = &cx.ir[stat];
            match &statement.kind {
                StatementKind::Synchronized { head_exprents, .. } => {
                    synchronized = true;
                    assert_eq!(statement.stats.len(), 2);
                    assert!(head_exprents.is_some());
                }
                StatementKind::CatchAll {
                    is_finally: true,
                    monitor,
                    ..
                } => {
                    finally = true;
                    assert_eq!(monitor.is_none(), deinline);
                }
                _ => {}
            }
            pending.extend(statement.stats.iter().copied());
        }
        assert!(finally);
        // With forced semaphores the inner monitor remains an explicit
        // monitorenter plus a catch-all containing monitorexit.
        assert_eq!(synchronized, deinline);
    }
}

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn structured_flow_matches_upstream() {
    check_flow(Check::Structure);
}

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn ssa_matches_upstream() {
    check_flow(Check::Ssa);
}

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn finally_matches_upstream() {
    check_flow(Check::Finally);
}

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn stack_vars_match_upstream() {
    stack_snapshot::check(
        &upstream_reference::Corpus::discover(),
        stack_snapshot::Check::Stack,
    );
}

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn variable_versions_and_increments_match_upstream() {
    stack_snapshot::check(
        &upstream_reference::Corpus::discover(),
        stack_snapshot::Check::Increments,
    );
}

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn pre_main_matches_upstream() {
    stack_snapshot::check(
        &upstream_reference::Corpus::discover(),
        stack_snapshot::Check::PreMain,
    );
}

#[test]
#[ignore = "requires the upstream +local.jar and JDK 17 or later"]
fn edge_cleanup_and_loop_elimination_match_upstream() {
    stack_snapshot::check(
        &upstream_reference::Corpus::discover(),
        stack_snapshot::Check::LoopElimination,
    );
}

#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
enum Check {
    Structure,
    Ssa,
    Finally,
}

fn check_flow(check: Check) {
    let corpus = upstream_reference::Corpus::discover();
    let paths = &corpus.classes;
    let mut transfer = tempfile::NamedTempFile::new().unwrap();
    let mut rust_snapshots = tempfile::tempfile().unwrap();
    let mut methods = Vec::new();
    let mut finally_coverage = finally_snapshot::Coverage::default();
    let profiles: &[(bool, bool, bool, bool)] = match check {
        Check::Structure => &[
            (false, true, false, true),
            (true, true, false, true),
            (false, false, false, true),
            (false, true, true, true),
        ],
        Check::Ssa => &[(false, true, false, true), (true, true, false, true)],
        Check::Finally => &[(false, true, false, true), (false, true, false, false)],
    };
    {
        let mut transfer = BufWriter::new(transfer.as_file_mut());
        let mut rust_snapshots = BufWriter::new(&mut rust_snapshots);
        transfer.write_all(&[check as u8]).unwrap();
        for path in paths {
            let bytes = fs::read(path).unwrap();
            for &(
                force_jsr_inline,
                use_lvt_names,
                decompile_complex_constant_dynamic,
                decompile_finally,
            ) in profiles
            {
                let mut options = Options::default();
                options.force_jsr_inline = force_jsr_inline;
                options.use_lvt_names = use_lvt_names;
                options.decompile_complex_constant_dynamic = decompile_complex_constant_dynamic;
                options.decompile_finally = decompile_finally;
                let options = Arc::new(options);
                let class = parse_class(&bytes, &options).unwrap();
                let mut cx = make_context(&options);
                cx.imports = ImportCollector::for_class(&cx.struct_context, &class);
                for method in &class.methods {
                    if !method.contains_code() {
                        continue;
                    }
                    let initial = initial_statement_graph(&mut cx, &class, method)
                        .unwrap()
                        .unwrap();
                    let record = i32::try_from(methods.len()).unwrap();
                    write_int(&mut transfer, record).unwrap();
                    write_text(&mut transfer, path.to_str().unwrap()).unwrap();
                    write_text(&mut transfer, &method.name).unwrap();
                    write_text(&mut transfer, &method.descriptor).unwrap();
                    write_flag(&mut transfer, force_jsr_inline).unwrap();
                    write_flag(&mut transfer, use_lvt_names).unwrap();
                    write_flag(&mut transfer, decompile_complex_constant_dynamic).unwrap();
                    write_flag(&mut transfer, decompile_finally).unwrap();
                    write_cfg(&mut transfer, &cx.ir, &initial.flow.graph).unwrap();

                    let result = catch_unwind(AssertUnwindSafe(|| initial.structure(&mut cx)));
                    let snapshot = match result {
                        Ok(Ok(structured)) if check == Check::Finally => finally_snapshot::run(
                            &mut cx,
                            structured,
                            &class,
                            &mut finally_coverage,
                        ),
                        Ok(Ok(mut structured)) => {
                            let mut snapshot = String::new();
                            if check == Check::Structure {
                                let statement = structure_snapshot(
                                    &cx,
                                    structured.root,
                                    &structured.flow.counters,
                                );
                                let direct = catch_unwind(AssertUnwindSafe(|| {
                                    format!(
                                        "graph={}",
                                        direct_graph_snapshot::snapshot(
                                            &mut cx.ir,
                                            structured.root
                                        )
                                    )
                                }))
                                .unwrap_or_else(|error| format!("panic={}", panic_text(&*error)));
                                snapshot = format!("{statement}\t{direct}\t");
                            }
                            let lifted = catch_unwind(AssertUnwindSafe(|| {
                                structured.process_expressions(&mut cx, &class)
                            }));
                            let expressions = match lifted {
                                Ok(Ok(())) if check == Check::Ssa => {
                                    ssa_snapshot::run(&mut cx.ir, &structured, method)
                                }
                                Ok(Ok(())) => catch_unwind(AssertUnwindSafe(|| {
                                    expression_snapshot::snapshot(
                                        &cx,
                                        structured.root,
                                        &structured.flow.counters,
                                    )
                                }))
                                .unwrap_or_else(|error| {
                                    format!("snapshot-error={}", panic_text(&*error))
                                }),
                                Ok(Err(error)) => {
                                    format!("lift-error={}", one_line(&error.to_string()))
                                }
                                Err(error) => format!("lift-panic={}", panic_text(&*error)),
                            };
                            snapshot.push_str(&expressions);
                            snapshot
                        }
                        Ok(Err(error))
                            if error.kind() == io::ErrorKind::InvalidData
                                && error.to_string() == "parsing failure!" =>
                        {
                            "rejected=parsing failure!".to_owned()
                        }
                        Ok(Err(error)) => {
                            format!("structure-error={}", one_line(&error.to_string()))
                        }
                        Err(error) => format!("structure-panic={}", panic_text(&*error)),
                    };
                    writeln!(rust_snapshots, "{snapshot}").unwrap();
                    methods.push(format!(
                        "{} {method} force-jsr={force_jsr_inline} lvt={use_lvt_names} \
                         complex-condy={decompile_complex_constant_dynamic} finally={decompile_finally}",
                        path.display()
                    ));
                }
            }
        }
        write_int(&mut transfer, -1).unwrap();
        transfer.flush().unwrap();
        rust_snapshots.flush().unwrap();
    }

    let mut reference = tempfile::tempfile().unwrap();
    corpus.run_to(
        "StructureReference",
        REFERENCE_HELPERS,
        transfer.path(),
        &reference,
    );
    reference.rewind().unwrap();
    rust_snapshots.rewind().unwrap();
    let mut rust_rows = BufReader::new(rust_snapshots).lines();
    let mut java_rows = BufReader::new(reference).lines();
    let stages: &[(&str, &str)] = match check {
        Check::Ssa => &[
            ("SSA splitting", "split="),
            ("SSA reassignment", "reassigned="),
            ("SSA version reset", "reset="),
            ("SSAU splitting", "ssau="),
            ("SSAU version reset", "ssau-reset="),
        ],
        Check::Structure => &[
            ("Structure", "counters="),
            ("Direct graph", "graph="),
            ("Expression lifting", "counters="),
        ],
        Check::Finally => &[
            ("Transferred CFG", "input="),
            ("Finally recovery CFG and semaphores", "recovered="),
            ("Recovered statement tree", "counters="),
            ("Post-finally statement tree", "counters="),
            ("Post-finally expressions", "counters="),
        ],
    };
    let mut mismatches = Vec::new();
    let mut rejected = 0;
    let mut recovery_rejected = 0;
    let mut predecessor_order_only = 0;
    for (index, method) in methods.iter().enumerate() {
        let row = java_rows.next().expect("missing Java result").unwrap();
        let (row_id, java) = row.split_once('\t').unwrap();
        let rust = rust_rows.next().expect("missing Rust result").unwrap();
        assert_eq!(row_id.parse::<usize>().unwrap(), index);
        if java == "rejected=parsing failure!" && java == rust {
            rejected += 1;
        } else {
            match compare_snapshots(java, &rust, stages) {
                Ok(Comparison::Exact) => {}
                Ok(Comparison::PredecessorOrderOnly) => predecessor_order_only += 1,
                Ok(Comparison::RecoveryRejected) => recovery_rejected += 1,
                Err(diff) => mismatches.push(format!("{method}\n  {diff}")),
            }
        }
    }
    assert!(java_rows.next().is_none(), "unexpected extra Java results");
    assert!(rust_rows.next().is_none(), "unexpected extra Rust results");
    if check == Check::Finally {
        finally_coverage.report();
    }
    assert!(
        mismatches.is_empty(),
        "{} of {} method snapshots differ:\n{}",
        mismatches.len(),
        methods.len(),
        mismatches.iter().take(30).join("\n")
    );
    let checked = match check {
        Check::Ssa => "SSA splits, reassignments, SSAU splits and version resets",
        Check::Structure => "statement trees, direct graphs and expression snapshots",
        Check::Finally => "finally CFG recoveries, statement trees and post-finally expressions",
    };
    eprintln!(
        "{} exact {checked}, and {rejected} matching decomposition rejections from {} class files",
        methods.len() - rejected - recovery_rejected - predecessor_order_only,
        paths.len()
    );
    if check == Check::Finally {
        eprintln!(
            "{predecessor_order_only} finally recoveries matching modulo predecessor order, {recovery_rejected} matching recovery rejections"
        );
    }
}

enum Comparison {
    Exact,
    PredecessorOrderOnly,
    RecoveryRejected,
}

fn compare_snapshots(
    java: &str,
    rust: &str,
    stages: &[(&str, &str)],
) -> Result<Comparison, String> {
    let mut java = java.split('\t');
    let mut rust = rust.split('\t');
    let mut comparison = Comparison::Exact;
    for &(stage, prefix) in stages {
        match (java.next(), rust.next()) {
            (Some(java), Some(rust)) if java == rust && java.starts_with(prefix) => {}
            (Some(j), Some(r))
                if prefix == "recovered=" && j == r && j.starts_with("recovery-rejected=") =>
            {
                if java.next().is_none() && rust.next().is_none() {
                    return Ok(Comparison::RecoveryRejected);
                }
                return Err("Unexpected stages after rejected recovery".into());
            }
            (Some(java), Some(rust))
                if prefix == "recovered="
                    && java.starts_with(prefix)
                    && rust.starts_with(prefix)
                    && finally_snapshot::same_predecessor_membership(java, rust) =>
            {
                comparison = Comparison::PredecessorOrderOnly;
            }
            (Some(java), Some(rust)) => {
                let stage = if [java, rust].iter().any(|result| {
                    result.starts_with("structure-") || result.starts_with("rejected=")
                }) {
                    "Structure"
                } else if [java, rust]
                    .iter()
                    .any(|result| result.starts_with("lift-"))
                {
                    "Expression lifting"
                } else {
                    stage
                };
                return Err(format!("{stage} {}", difference(java, rust)));
            }
            _ => return Err(format!("Missing {stage}")),
        }
    }
    if java.next().is_some() || rust.next().is_some() {
        return Err("Unexpected extra stages".into());
    }
    Ok(comparison)
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

fn panic_text(error: &(dyn std::any::Any + Send)) -> String {
    one_line(
        error
            .downcast_ref::<String>()
            .map(String::as_str)
            .or_else(|| error.downcast_ref::<&str>().copied())
            .unwrap_or("unknown panic"),
    )
}

fn one_line(text: &str) -> String {
    text.replace(['\r', '\n', '\t'], " ")
}

fn write_cfg(out: &mut impl Write, ir: &Ir, graph: &ControlFlowGraph) -> io::Result<()> {
    write_int(out, ir[graph.first].id)?;
    write_int(out, ir[graph.last].id)?;
    write_int(out, graph.last_id)?;
    write_ints(out, ir[graph.last].preds.iter().map(|&block| ir[block].id))?;
    write_ints(
        out,
        ir[graph.last]
            .pred_exceptions
            .iter()
            .map(|&block| ir[block].id),
    )?;
    write_flag(out, graph.add_error_comment)?;
    write_count(out, graph.comment_lines.len())?;
    for comment in &graph.comment_lines {
        write_text(out, comment)?;
    }
    write_count(out, graph.blocks.len())?;
    let originals: HashMap<_, _> = graph
        .sequence
        .instructions
        .iter()
        .enumerate()
        .map(|(index, instruction)| (Arc::as_ptr(instruction), i32::try_from(index).unwrap()))
        .collect();
    let mut instructions = HashMap::new();
    for &block in &graph.blocks {
        let block = &ir[block];
        write_int(out, block.id)?;
        write_ints(out, block.instr_old_offsets.iter().copied())?;
        write_ints(out, block.succs.iter().map(|&next| ir[next].id))?;
        write_ints(
            out,
            block.succ_exceptions.iter().map(|&handler| ir[handler].id),
        )?;
        write_ints(out, block.preds.iter().map(|&pred| ir[pred].id))?;
        write_ints(
            out,
            block.pred_exceptions.iter().map(|&thrower| ir[thrower].id),
        )?;
        write_int(out, block.seq.length())?;
        for instruction in &block.seq {
            let next = i32::try_from(instructions.len()).unwrap();
            let identity = *instructions.entry(Arc::as_ptr(instruction)).or_insert(next);
            write_int(out, identity)?;
            if identity != next {
                continue;
            }
            let original = originals
                .get(&Arc::as_ptr(instruction))
                .copied()
                .unwrap_or(-1);
            write_int(out, original)?;
            if original >= 0 {
                continue;
            }
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
    write_ints(out, graph.finally_exits.iter().map(|&block| ir[block].id))?;
    write_count(out, graph.subroutines.len())?;
    for (&entry, &exit) in &graph.subroutines {
        write_int(out, ir[entry].id)?;
        write_int(out, ir[exit].id)?;
    }
    Ok(())
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

fn structure_snapshot(cx: &Cx, root: StatId, counters: &CounterContainer) -> String {
    structure_snapshot_with_edges(cx, root, counters, false)
}

fn structure_snapshot_with_edges(
    cx: &Cx,
    root: StatId,
    counters: &CounterContainer,
    loop_stage: bool,
) -> String {
    let ir = &cx.ir;
    let StatementKind::Root {
        comment_lines,
        add_error_comment,
        ..
    } = &ir[root].kind
    else {
        unreachable!()
    };
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
    for stat in structure_statements(ir, root) {
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
        if loop_stage {
            fields.push(format!(
                "in={}",
                stat.get_predecessor_edges(ir, STATEDGE_ALL)
                    .iter()
                    .map(|&e| edge(Some(e)))
                    .join("|")
            ));
        }
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
                            .map(|&expr| expression(cx, expr))
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
                    .map(|&expr| expression(cx, Some(expr)))
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
                expression(cx, *monitor),
                vars.iter()
                    .map(|&expr| expression(cx, Some(expr)))
                    .join("|")
            )),
            StatementKind::Synchronized { body, .. } => {
                fields.push(format!("monitor={}", ir[*body].id))
            }
            StatementKind::Do if loop_stage => fields.push("loop=INFINITE".to_owned()),
            _ => {}
        }
    }
    fields.join(";")
}

fn structure_statements(ir: &Ir, root: StatId) -> impl Iterator<Item = StatId> + '_ {
    let StatementKind::Root { dummy_exit, .. } = ir[root].kind else {
        unreachable!();
    };
    let mut pending = vec![dummy_exit, root];
    std::iter::from_fn(move || {
        let stat = pending.pop()?;
        pending.extend(ir[stat].stats.iter().rev().copied());
        Some(stat)
    })
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

fn expression(cx: &Cx, expr: Option<ExprId>) -> String {
    expr.map_or_else(
        || "-".to_owned(),
        |id| {
            let expr = &cx.ir[id];
            match &expr.kind {
                ExprKind::Constant {
                    value: ConstantValue::Integer(value),
                    ..
                } => format!("{}={value}", expr.id),
                ExprKind::Variable(var) => format!(
                    "{}={}:{}",
                    expr.id,
                    var.index,
                    vineflower_rs::decompiler::exps::Expr::expr_type(cx, id)
                        .value
                        .as_deref()
                        .unwrap_or("*")
                ),
                _ => panic!("unexpected expression before lifting: {:?}", expr.kind),
            }
        },
    )
}
