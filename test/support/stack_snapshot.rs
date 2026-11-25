// SPDX-License-Identifier: Apache-2.0

use std::cell::Cell;
use std::collections::{BTreeMap, HashMap};
use std::fmt::Write as _;
use std::fs;
use std::io::{self, BufRead, BufReader, BufWriter, Seek, Write};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use itertools::Itertools;
use rustc_hash::FxHashSet;
use vineflower_rs::decompiler::ir::{EdgeId, Ir, StatId};
use vineflower_rs::decompiler::sforms::split_ssa;
use vineflower_rs::decompiler::stack::simplify_statement;
use vineflower_rs::decompiler::stats::{ContentFlags, STATEDGE_ALL, StatementKind};
use vineflower_rs::decompiler::vars::versions::{FinalType, VarVersions};
use vineflower_rs::engine::class_nodes::{ClassNodeId, load_classes};
use vineflower_rs::engine::class_processor::prepare_class;
use vineflower_rs::engine::context_source::{ContextSource, RuntimeImage};
use vineflower_rs::engine::import_collector::ImportCollector;
use vineflower_rs::engine::method_processor::{
    ExpressionMethod, InitialMethod, initial_statement_graph,
};
use vineflower_rs::engine::{Cx, Options};
use vineflower_rs::structs::single_file_context_source::SingleFileContextSource;
use vineflower_rs::structs::{StructClass, StructContext, StructMethod};

use super::upstream_reference::{Corpus, jdk_home};
use super::{
    REFERENCE_HELPERS, compare_snapshots, direct_graph_snapshot, edge_id, expression_snapshot,
    one_line, panic_text, parse_class, structure_snapshot_with_edges, structure_statements,
    write_cfg, write_count, write_flag, write_int, write_text,
};

#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub(super) enum Check {
    Stack = 3,
    Increments = 4,
    PreMain = 5,
    LoopElimination = 6,
    LoopEnhancement = 7,
    LoopMerge = 8,
    MainLoopLabels = 9,
}

#[derive(Clone, Copy)]
struct Profile {
    simplify: bool,
    ternary: bool,
    lvt: bool,
    boolean_as_int: bool,
    assertions: bool,
}

const DEFAULT: Profile = Profile {
    simplify: true,
    ternary: true,
    lvt: true,
    boolean_as_int: true,
    assertions: true,
};

const STACK_PROFILES: &[Profile] = &[
    DEFAULT,
    Profile {
        simplify: false,
        ..DEFAULT
    },
    Profile {
        ternary: false,
        ..DEFAULT
    },
];

const INCREMENT_PROFILES: &[Profile] = &[
    DEFAULT,
    Profile {
        lvt: false,
        ..DEFAULT
    },
    Profile {
        boolean_as_int: false,
        ..DEFAULT
    },
];

const PRE_MAIN_PROFILES: &[Profile] = &[
    DEFAULT,
    Profile {
        assertions: false,
        ..DEFAULT
    },
];

const STACK_STAGES: &[(&str, &str)] = &[
    ("First stack simplification structure", "counters="),
    ("First stack simplification expressions", "counters="),
    ("Settled stack structure", "counters="),
    ("Settled stack expressions", "counters="),
];

const INCREMENT_STAGES: &[(&str, &str)] = &[
    ("First variable version structure", "counters="),
    ("First variable version expressions", "counters="),
    ("First variable versions", "versions="),
    ("Settled increment structure", "counters="),
    ("Settled increment expressions", "counters="),
    ("Settled variable versions", "versions="),
];

const PRE_MAIN_STAGES: &[(&str, &str)] = &[
    ("Concat structure", "counters="),
    ("Concat expressions", "counters="),
    ("Concat variable versions and assertion result", "versions="),
    ("Before main structure", "counters="),
    ("Before main expressions", "counters="),
    ("Before main variable versions", "versions="),
];

const LOOP_ELIMINATION_STAGES: &[(&str, &str)] = &[
    ("Edge cleanup structure", "counters="),
    ("Edge cleanup expressions", "counters="),
    ("Edge cleanup variable versions", "versions="),
    ("Loop elimination results", "iterations="),
    ("Loop elimination input structure", "counters="),
    ("Loop elimination input expressions", "counters="),
    ("Loop elimination input variable versions", "versions="),
];

const ELIMINATED_STAGES: &[(&str, &str)] = &[
    ("After removing a loop, structure", "counters="),
    ("After removing a loop, expressions", "counters="),
    ("After removing a loop, variable versions", "versions="),
];

const TERMINAL_LOOP_STAGES: &[(&str, &str)] = &[
    (
        "After loop elimination returns false, structure",
        "counters=",
    ),
    (
        "After loop elimination returns false, expressions",
        "counters=",
    ),
    (
        "After loop elimination returns false, variable versions",
        "versions=",
    ),
];

const LOOP_ENHANCEMENT_STAGES: &[(&str, &str)] = &[
    ("Enhanced loop structure and return value", "counters="),
    ("Enhanced loop expressions and headers", "counters="),
    ("Enhanced loop variable versions", "versions="),
    ("Direct graph of enhanced loops", "graph="),
];

const LOOP_MERGE_STAGES: &[(&str, &str)] = &[
    ("Structure after loop merging", "counters="),
    ("Loop expressions and headers after merging", "counters="),
    ("Variable versions after loop merging", "versions="),
    ("Direct graph after loop merging", "graph="),
];

const MAIN_LOOP_LABEL_STAGES: &[(&str, &str)] = &[
    (
        "Structure and labels after label identification",
        "counters=",
    ),
    ("Expressions after label identification", "counters="),
    ("Variable versions after label identification", "versions="),
    ("Direct graph after label identification", "graph="),
];

fn loop_iterations(row: &str) -> impl Iterator<Item = &str> {
    row.split('\t')
        .nth(3)
        .and_then(|field| field.strip_prefix("iterations="))
        .into_iter()
        .flat_map(|trace| trace.split(',').filter(|result| !result.is_empty()))
}

impl Check {
    fn profiles(self) -> &'static [Profile] {
        match self {
            Self::Stack => STACK_PROFILES,
            Self::Increments => INCREMENT_PROFILES,
            Self::PreMain => PRE_MAIN_PROFILES,
            Self::LoopElimination
            | Self::LoopEnhancement
            | Self::LoopMerge
            | Self::MainLoopLabels => &[DEFAULT],
        }
    }

    fn stages(self) -> &'static [(&'static str, &'static str)] {
        match self {
            Self::Stack => STACK_STAGES,
            Self::Increments => INCREMENT_STAGES,
            Self::PreMain => PRE_MAIN_STAGES,
            Self::LoopElimination => LOOP_ELIMINATION_STAGES,
            Self::LoopEnhancement => LOOP_ENHANCEMENT_STAGES,
            Self::LoopMerge => LOOP_MERGE_STAGES,
            Self::MainLoopLabels => MAIN_LOOP_LABEL_STAGES,
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::Stack => "stack",
            Self::Increments => "increments",
            Self::PreMain => "pre-main",
            Self::LoopElimination => "loop-elimination",
            Self::LoopEnhancement => "loop-enhancement",
            Self::LoopMerge => "loop-merge",
            Self::MainLoopLabels => "main-loop-labels",
        }
    }

    fn uses_loop_headers(self) -> bool {
        matches!(
            self,
            Self::LoopEnhancement | Self::LoopMerge | Self::MainLoopLabels
        )
    }
}

#[derive(Default)]
struct LoopCoverage {
    removed_edges: usize,
    rewritten_edges: usize,
    successful_calls: usize,
    removed_loops: usize,
    terminal_calls: usize,
    terminal_changes: usize,
}

impl LoopCoverage {
    fn record(&mut self, row: &str) {
        let cleanup = row.split('\t').next().unwrap();
        for field in cleanup.split(';') {
            if let Some(removed) = field.strip_prefix("cleanup-removed=") {
                self.removed_edges += removed.parse::<usize>().unwrap();
            }
            if let Some(rewritten) = field.strip_prefix("cleanup-rewritten=") {
                self.rewritten_edges += rewritten.parse::<usize>().unwrap();
            }
        }

        let mut snapshots = row.split('\t').skip(4).tuples::<(_, _, _)>();
        let mut previous = snapshots.next().unwrap();
        for (repeat, current) in loop_iterations(row).zip(snapshots) {
            if repeat == "true" {
                self.successful_calls += 1;
                self.removed_loops += loop_ids(previous.0)
                    .difference(&loop_ids(current.0))
                    .count();
            } else {
                self.terminal_calls += 1;
                self.terminal_changes += usize::from(previous != current);
            }
            previous = current;
        }
    }

    fn report(&self) {
        eprintln!(
            "Edge cleanup removed {} edges and rewrote {} retained edges",
            self.removed_edges, self.rewritten_edges,
        );
        eprintln!(
            "{} successful calls removed {} loop statements; {} terminal false calls changed {} method snapshots",
            self.successful_calls, self.removed_loops, self.terminal_calls, self.terminal_changes,
        );
    }
}

fn loop_ids(tree: &str) -> FxHashSet<&str> {
    tree.split(';')
        .filter_map(|field| field.strip_prefix("stat=")?.strip_suffix(":DO"))
        .collect()
}

#[derive(Default)]
struct EnhancementCoverage {
    changed_methods: usize,
    loops: BTreeMap<String, usize>,
    foreach_sources: BTreeMap<String, usize>,
    list_iterator: bool,
}

impl EnhancementCoverage {
    fn record(&mut self, method: &str, row: &str) {
        let mut snapshots = row.split('\t');
        let tree = snapshots.next().unwrap();
        self.changed_methods += usize::from(tree.ends_with(";enhanced=true"));
        for kind in tree
            .split(';')
            .filter_map(|field| field.strip_prefix("loop="))
        {
            *self.loops.entry(kind.to_owned()).or_default() += 1;
        }
        for field in snapshots.next().unwrap().split(';') {
            if let Some((_, kind)) = field
                .strip_prefix("foreach")
                .and_then(|entry| entry.split_once('='))
            {
                *self.foreach_sources.entry(kind.to_owned()).or_default() += 1;
                self.list_iterator |= kind == "iterator"
                    && method.contains("TestListIteratorHierarchy.class print (Ljava/util/List;)V");
            }
        }
    }

    fn report(&self, check: Check) {
        assert!(
            self.list_iterator,
            "the ListIterator fixture must recover a foreach loop"
        );
        if check == Check::LoopEnhancement {
            eprintln!(
                "{} methods reported a change from loop enhancement",
                self.changed_methods
            );
        }
        for kind in ["INFINITE", "DO_WHILE", "WHILE", "FOR", "FOR_EACH"] {
            eprintln!(
                "{} {kind} loops",
                self.loops.get(kind).copied().unwrap_or(0)
            );
        }
        for source in ["array", "iterator"] {
            eprintln!(
                "{} foreach loops over an {source}",
                self.foreach_sources.get(source).copied().unwrap_or(0)
            );
        }
    }
}

struct Fixture {
    path: PathBuf,
    name: String,
}

fn class_groups(corpus: &Corpus) -> Vec<Vec<Fixture>> {
    let mut groups: BTreeMap<&Path, Vec<Fixture>> = BTreeMap::new();
    for path in &corpus.classes {
        let class = parse_class(&fs::read(path).unwrap(), &Options::default()).unwrap();
        let name = class.qualified_name.to_string();
        let package_depth = name.bytes().filter(|&byte| byte == b'/').count();
        let group = path.ancestors().nth(package_depth + 1).unwrap();
        groups.entry(group).or_default().push(Fixture {
            path: path.clone(),
            name,
        });
    }
    groups.into_values().collect()
}

pub(super) fn check(corpus: &Corpus, check: Check) {
    let mut groups = class_groups(corpus);
    let runtime = check.uses_loop_headers().then(|| {
        let name = "TestListIteratorHierarchy";
        let path = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("test/smoke/java8")
            .join(format!("{name}.class"));
        if !corpus.classes.contains(&path) {
            groups.push(vec![Fixture {
                path,
                name: name.to_owned(),
            }]);
        }
        let home = jdk_home();
        Arc::new(RuntimeImage::open(&home).unwrap_or_else(|error| {
            panic!("loading runtime at {}: {error}", home.display());
        })) as Arc<dyn ContextSource>
    });
    let mut input = tempfile::NamedTempFile::new().unwrap();
    let mut snapshots = tempfile::tempfile().unwrap();
    let mut methods = Vec::new();
    {
        let mut input = BufWriter::new(input.as_file_mut());
        let mut snapshots = BufWriter::new(&mut snapshots);
        input.write_all(&[check as u8]).unwrap();
        write_count(&mut input, groups.len()).unwrap();
        for group in &groups {
            write_count(&mut input, group.len()).unwrap();
            for fixture in group {
                write_text(&mut input, fixture.path.to_str().unwrap()).unwrap();
            }
        }
        for &profile in check.profiles() {
            for (group_index, group) in groups.iter().enumerate() {
                write_group(
                    &mut input,
                    &mut snapshots,
                    &mut methods,
                    group_index,
                    group,
                    profile,
                    check,
                    runtime.as_ref(),
                );
            }
        }
        write_int(&mut input, -1).unwrap();
        input.flush().unwrap();
        snapshots.flush().unwrap();
    }

    let mut reference = tempfile::tempfile().unwrap();
    corpus.run_to(
        "StructureReference",
        REFERENCE_HELPERS,
        input.path(),
        &reference,
    );
    snapshots.rewind().unwrap();
    reference.rewind().unwrap();
    let mut java_rows = BufReader::new(reference).lines();
    let mut rust_rows = BufReader::new(snapshots).lines();
    let mut errors = Vec::new();
    let mut rejected = 0;
    let mut hidden_changes = [0, 0];
    let mut repeats = 0;
    let mut changed_original = 0;
    let mut concats = 0;
    let mut assertion_changes = 0;
    let mut loop_coverage = LoopCoverage::default();
    let mut enhancement_coverage = EnhancementCoverage::default();
    for (index, method) in methods.iter().enumerate() {
        let row = java_rows
            .next()
            .expect("missing Java stack snapshot")
            .unwrap();
        let (id, java) = row.split_once('\t').unwrap();
        let rust = rust_rows
            .next()
            .expect("missing Rust stack snapshot")
            .unwrap();
        assert_eq!(id.parse::<usize>().unwrap(), index);
        let mut loop_stages;
        let stages = if check == Check::LoopElimination {
            loop_stages = check.stages().to_vec();
            for repeat in loop_iterations(&rust) {
                loop_stages.extend_from_slice(if repeat == "true" {
                    ELIMINATED_STAGES
                } else {
                    TERMINAL_LOOP_STAGES
                });
            }
            &loop_stages
        } else {
            check.stages()
        };
        if java == rust && (java.starts_with("rejected=") || java.starts_with("class-rejected=")) {
            rejected += 1;
        } else if let Err(diff) = compare_snapshots(java, &rust, stages) {
            errors.push(format!("{method}\n  {diff}"));
        } else if check.uses_loop_headers() {
            enhancement_coverage.record(method, &rust);
        } else {
            let stage_size = if check == Check::Stack { 2 } else { 3 };
            let first = rust.split('\t').next().unwrap();
            let settled = rust.rsplit('\t').nth(stage_size - 1).unwrap();
            for (tree, changes) in [first, settled].into_iter().zip(&mut hidden_changes) {
                if tree.split(';').any(|field| {
                    field
                        .strip_prefix("hidden-added=")
                        .is_some_and(|added| !added.is_empty())
                }) {
                    *changes += 1;
                }
            }
            if check == Check::Increments {
                let mut maps = rust.split('\t').skip(2).step_by(stage_size);
                let first = maps.next().unwrap();
                let settled = maps.next().unwrap();
                if first.ends_with(";repeat=true") {
                    repeats += 1;
                    let original = |field: &&str| field.starts_with("original");
                    changed_original += usize::from(
                        !first
                            .split(';')
                            .filter(original)
                            .eq(settled.split(';').filter(original)),
                    );
                }
            }
            if check == Check::PreMain {
                let mut first = rust.split('\t').skip(1);
                concats += usize::from(first.next().unwrap().contains("|STR_CONCAT|"));
                assertion_changes +=
                    usize::from(first.next().unwrap().ends_with(";assert-changed=true"));
            }
            if check == Check::LoopElimination {
                loop_coverage.record(&rust);
            }
        }
    }
    assert!(java_rows.next().is_none() && rust_rows.next().is_none());
    assert!(
        errors.is_empty(),
        "{} of {} {} snapshots differ:\n{}",
        errors.len(),
        methods.len(),
        check.name(),
        errors
            .iter()
            .take(30)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
    let stages = if check.uses_loop_headers() {
        ""
    } else {
        "first and settled "
    };
    eprintln!(
        "{} exact {stages}{} snapshots and {rejected} matching rejections across {} class files",
        methods.len() - rejected,
        check.name(),
        groups.iter().map(Vec::len).sum::<usize>()
    );
    if check.uses_loop_headers() {
        enhancement_coverage.report(check);
        return;
    }
    let [first, settled] = hidden_changes;
    eprintln!("{first} first simplifications and {settled} settled runs added hidden members");
    if check == Check::Increments {
        eprintln!(
            "{repeats} first passes scheduled another iteration, with {changed_original} changed original variable maps"
        );
    }
    if check == Check::PreMain {
        eprintln!(
            "{concats} concat checkpoints contain string concatenation; {assertion_changes} assertion passes changed their tree"
        );
    }
    if check == Check::LoopElimination {
        loop_coverage.report();
    }
}

fn write_group(
    input: &mut impl Write,
    snapshots: &mut impl Write,
    methods: &mut Vec<String>,
    group_index: usize,
    group: &[Fixture],
    profile: Profile,
    check: Check,
    runtime: Option<&Arc<dyn ContextSource>>,
) {
    let mut options = Options::default();
    options.simplify_stack = profile.simplify;
    options.ternary_in_if = profile.ternary;
    options.use_lvt_names = profile.lvt;
    options.boolean_as_int = profile.boolean_as_int;
    options.decompile_assert = profile.assertions;
    let options = Arc::new(options);
    let mut context = StructContext::new(Arc::clone(&options), None);
    if let Some(runtime) = runtime {
        context.add_space(Arc::clone(runtime), false);
    }
    for fixture in group {
        let source = SingleFileContextSource::open(&fixture.path, &options, None).unwrap();
        context.add_space(Arc::new(source), true);
    }
    let mut cx = Cx::new(Arc::new(context));
    cx.class_nodes = load_classes(
        &cx.struct_context,
        &options,
        |_| true,
        |_| true,
        |_, _| None,
    );
    let mut prepared = HashMap::new();
    for fixture in group {
        let id = cx.class_nodes.id(&fixture.name).unwrap();
        let class = Arc::clone(&cx.class_nodes[id].class);
        let mut root = id;
        while let Some(parent) = cx.class_nodes[root].parent {
            root = parent;
        }
        let imports: &Result<ImportCollector, String> = prepared.entry(root).or_insert_with(|| {
            cx.current_class_node = None;
            prepare_class(&mut cx, root)
                .map(|()| cx.imports.clone())
                .map_err(|err| err.to_string())
        });
        cx.current_class_node = Some(class.qualified_name.clone());
        for method in &class.methods {
            if !method.contains_code() {
                continue;
            }
            cx.ir = Default::default();
            let initial = initial_statement_graph(&mut cx, &class, method)
                .unwrap()
                .unwrap();
            write_int(input, i32::try_from(methods.len()).unwrap()).unwrap();
            write_text(input, fixture.path.to_str().unwrap()).unwrap();
            write_text(input, &method.name).unwrap();
            write_text(input, &method.descriptor).unwrap();
            for flag in [
                options.force_jsr_inline,
                options.use_lvt_names,
                options.decompile_complex_constant_dynamic,
                options.decompile_finally,
            ] {
                write_flag(input, flag).unwrap();
            }
            write_count(input, group_index).unwrap();
            write_flag(input, profile.simplify).unwrap();
            write_flag(input, profile.ternary).unwrap();
            write_flag(input, profile.boolean_as_int).unwrap();
            write_flag(input, profile.assertions).unwrap();
            write_text(input, &fixture.name).unwrap();
            write_cfg(input, &cx.ir, &initial.flow.graph).unwrap();

            let snapshot = match imports {
                Ok(imports) => describe(&mut cx, id, &class, method, initial, imports, check),
                Err(error) => format!("class-rejected={}", one_line(error)),
            };
            writeln!(snapshots, "{snapshot}").unwrap();
            methods.push(format!(
                "{} {method} simplify-stack={} ternary-in-if={} lvt={} boolean-as-int={} assertions={}",
                fixture.path.display(),
                profile.simplify,
                profile.ternary,
                profile.lvt,
                profile.boolean_as_int,
                profile.assertions,
            ));
        }
    }
}

fn describe(
    cx: &mut Cx,
    owner: ClassNodeId,
    class: &StructClass,
    method: &Arc<StructMethod>,
    initial: InitialMethod,
    imports: &ImportCollector,
    check: Check,
) -> String {
    let initial_hidden = cx.class_nodes[owner].hidden_members.clone();
    cx.imports = imports.clone();
    let first = stage(cx, owner, class, initial, &initial_hidden, true, check);
    cx.class_nodes[owner]
        .hidden_members
        .clone_from(&initial_hidden);
    if check.uses_loop_headers() || first == "rejected=parsing failure!" {
        return first;
    }

    cx.ir = Default::default();
    cx.imports = imports.clone();
    let initial = initial_statement_graph(cx, class, method).unwrap().unwrap();
    let settled = stage(cx, owner, class, initial, &initial_hidden, false, check);
    format!("{first}\t{settled}")
}

fn stage(
    cx: &mut Cx,
    owner: ClassNodeId,
    class: &StructClass,
    initial: InitialMethod,
    initial_hidden: &FxHashSet<String>,
    first: bool,
    check: Check,
) -> String {
    let operation = Cell::new("structure");
    let result = catch_unwind(AssertUnwindSafe(|| {
        let structured = initial.structure(cx)?;
        operation.set("finally");
        let recovered = structured.recover_finally(cx, class)?;
        operation.set("lift");
        let mut method = recovered.into_expressions(cx, class)?;
        operation.set("simplify-stack");
        match (check, first) {
            (Check::Increments, true) => {
                method.simplify_stack_vars(cx, class);
                operation.set("set-var-versions");
                method.set_var_versions(cx, class)?;
            }
            (Check::Increments, false) | (Check::PreMain, true) => {
                operation.set("process-increments");
                method.process_increments(cx, class)?;
                if check == Check::PreMain {
                    operation.set("simplify-concat");
                    method.simplify_string_concat(cx, class)?;
                }
            }
            (Check::PreMain, false) => {
                operation.set("prepare-main-loop");
                method.prepare_main_loop(cx, class)?;
            }
            (
                Check::LoopElimination
                | Check::LoopEnhancement
                | Check::LoopMerge
                | Check::MainLoopLabels,
                _,
            ) => {
                loop {
                    operation.set("simplify-stack");
                    method.simplify_stack_vars(cx, class);
                    operation.set("set-var-versions");
                    method.set_var_versions(cx, class)?;
                    operation.set("find-increments");
                    if !method.find_increments(cx) {
                        break;
                    }
                }
                operation.set("inline-increments");
                method.inline_increments_in_conditions(cx);
                operation.set("simplify-concat");
                method.simplify_string_concat(cx, class)?;
                operation.set("build-assertions");
                method.build_assertions(cx, class)?;

                operation.set("snapshot");
                let original_edges = (first && check == Check::LoopElimination)
                    .then(|| edge_states(&cx.ir, method.root));
                if check != Check::MainLoopLabels {
                    operation.set("clean-up-edges");
                    method.clean_up_edges(cx);
                }
                if check.uses_loop_headers() {
                    let details = if check == Check::LoopEnhancement {
                        operation.set("eliminate-loops");
                        while method.eliminate_loops(cx, class)? {}
                        operation.set("enhance-loops");
                        format!(";enhanced={}", method.enhance_loops(cx)?)
                    } else if check == Check::LoopMerge {
                        operation.set("merge-loops");
                        method.merge_loops(cx, class)?;
                        String::new()
                    } else {
                        operation.set("identify-main-loop-labels");
                        method.identify_main_loop_labels(cx, class)?;
                        String::new()
                    };
                    operation.set("snapshot");
                    let result = snapshot(cx, owner, &method, initial_hidden, check, &details);
                    let graph = direct_graph_snapshot::enhanced(&mut cx.ir, method.root);
                    return Ok(format!("{result}\t{graph}"));
                }
                operation.set("snapshot");
                if let Some(original_edges) = original_edges {
                    let cleaned_edges = edge_states(&cx.ir, method.root);
                    let removed = original_edges
                        .keys()
                        .filter(|edge| !cleaned_edges.contains_key(edge))
                        .count();
                    let rewritten = original_edges
                        .iter()
                        .filter(|(edge, old)| {
                            cleaned_edges.get(edge).is_some_and(|new| *old != new)
                        })
                        .count();
                    let details =
                        format!(";cleanup-removed={removed};cleanup-rewritten={rewritten}");
                    return Ok(snapshot(
                        cx,
                        owner,
                        &method,
                        initial_hidden,
                        check,
                        &details,
                    ));
                }

                let mut states = vec![snapshot(cx, owner, &method, initial_hidden, check, "")];
                let mut iterations = Vec::new();
                if root_content_flags(cx, method.root).has_loops {
                    loop {
                        operation.set("eliminate-loops");
                        let repeat = method.eliminate_loops(cx, class)?;
                        iterations.push(repeat);
                        operation.set("snapshot");
                        states.push(snapshot(cx, owner, &method, initial_hidden, check, ""));
                        if !repeat {
                            break;
                        }
                    }
                }
                return Ok(format!(
                    "iterations={}\t{}",
                    iterations.iter().join(","),
                    states.join("\t")
                ));
            }
            (Check::Stack, true) => {
                let owner = Arc::clone(method.root.method(&cx.ir));
                let ssa = split_ssa(&mut cx.ir, method.root, &owner);
                let mut reordered = FxHashSet::default();
                while simplify_statement(
                    cx,
                    &mut method.flow.counters,
                    method.root,
                    &mut reordered,
                    &ssa,
                    class,
                    true,
                ) {}
            }
            (Check::Stack, false) => method.simplify_stack_vars(cx, class),
        }
        operation.set("snapshot");
        let mut snapshot = snapshot(cx, owner, &method, initial_hidden, check, "");
        if check == Check::Increments && first {
            operation.set("find-increments");
            write!(snapshot, ";repeat={}", method.find_increments(cx)).unwrap();
        } else if check == Check::PreMain && first {
            operation.set("build-assertions");
            write!(
                snapshot,
                ";assert-changed={}",
                method.build_assertions(cx, class)?
            )
            .unwrap();
        }
        Ok::<_, io::Error>(snapshot)
    }));
    match result {
        Ok(Ok(snapshot)) => snapshot,
        Ok(Err(error))
            if error.kind() == io::ErrorKind::InvalidData
                && error.to_string() == "parsing failure!" =>
        {
            "rejected=parsing failure!".into()
        }
        Ok(Err(error)) => stage_error(
            check,
            operation.get(),
            "error",
            &one_line(&error.to_string()),
        ),
        Err(error) => stage_error(check, operation.get(), "panic", &panic_text(&*error)),
    }
}

fn snapshot(
    cx: &Cx,
    owner: ClassNodeId,
    method: &ExpressionMethod,
    initial_hidden: &FxHashSet<String>,
    check: Check,
    details: &str,
) -> String {
    let loop_stage = check == Check::LoopElimination || check.uses_loop_headers();
    let mut tree =
        structure_snapshot_with_edges(cx, method.root, &method.flow.counters, loop_stage);
    if check == Check::PreMain || loop_stage {
        let content = root_content_flags(cx, method.root);
        write!(
            tree,
            ";content={},{},{}",
            content.has_try_catch, content.has_loops, content.has_switch,
        )
        .unwrap();
    }
    let hidden = &cx.class_nodes[owner].hidden_members;
    let all_members = hidden_members(hidden.iter());
    let added = hidden_members(hidden.difference(initial_hidden));
    let expressions = expression_snapshot::snapshot_with_loops(
        cx,
        method.root,
        &method.flow.counters,
        check.uses_loop_headers(),
    );
    let mut snapshot =
        format!("{tree};hidden={all_members};hidden-added={added}{details}\t{expressions}");
    if check != Check::Stack {
        let versions = variable_snapshot(&cx.ir[method.flow.variables]);
        write!(snapshot, "\t{versions}").unwrap();
    }
    snapshot
}

fn root_content_flags(cx: &Cx, root: StatId) -> ContentFlags {
    let StatementKind::Root { content_flags, .. } = cx.ir[root].kind else {
        unreachable!()
    };
    content_flags
}

fn edge_states(ir: &Ir, root: StatId) -> HashMap<EdgeId, String> {
    structure_statements(ir, root)
        .flat_map(|stat| stat.get_successor_edges(ir, STATEDGE_ALL))
        .map(|edge| (edge, edge_id(ir, Some(edge))))
        .collect()
}

fn stage_error(check: Check, operation: &str, kind: &str, message: &str) -> String {
    if check == Check::Stack {
        format!("stack-{kind}={message}")
    } else {
        format!("{}-{operation}-{kind}={message}", check.name())
    }
}

fn variable_snapshot(versions: &VarVersions) -> String {
    let mut fields = String::from("versions=");
    for (pair, ty) in versions
        .lower
        .iter()
        .sorted_unstable_by_key(|entry| *entry.0)
    {
        write!(
            fields,
            ";lower{},{}={}",
            pair.var,
            pair.version,
            expression_snapshot::var_type(Some(ty))
        )
        .unwrap();
    }
    for (pair, ty) in versions
        .upper
        .iter()
        .sorted_unstable_by_key(|entry| *entry.0)
    {
        write!(
            fields,
            ";upper{},{}={}",
            pair.var,
            pair.version,
            expression_snapshot::var_type(ty.as_ref())
        )
        .unwrap();
    }
    for (pair, final_type) in versions
        .final_vars
        .iter()
        .sorted_unstable_by_key(|entry| *entry.0)
    {
        let name = match final_type {
            FinalType::Final => "FINAL",
            FinalType::NonFinal => "NON_FINAL",
            FinalType::ExplicitFinal => "EXPLICIT_FINAL",
        };
        write!(fields, ";final{},{}={name}", pair.var, pair.version).unwrap();
    }
    for (index, pair) in versions
        .original
        .iter()
        .sorted_unstable_by_key(|entry| *entry.0)
    {
        write!(fields, ";original{index}={},{}", pair.var, pair.version).unwrap();
    }
    fields
}

fn hidden_members<'a>(members: impl Iterator<Item = &'a String>) -> String {
    members
        .sorted_unstable_by(|left, right| left.encode_utf16().cmp(right.encode_utf16()))
        .map(|member| expression_snapshot::text(Some(member)))
        .join(",")
}
