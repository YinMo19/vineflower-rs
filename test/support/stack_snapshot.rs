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
use vineflower_rs::decompiler::vars::processor::VarProcessor;
use vineflower_rs::decompiler::vars::var_version_pair::VarVersionPair;
use vineflower_rs::decompiler::vars::versions::{FinalType, VarVersions};
use vineflower_rs::engine::class_nodes::{ClassNodeId, load_classes};
use vineflower_rs::engine::class_processor::{prepare_class, process_class_methods};
use vineflower_rs::engine::context_source::{ContextSource, RuntimeImage};
use vineflower_rs::engine::counter_container::{
    CounterContainer, EXPRESSION_COUNTER, STATEMENT_COUNTER, VAR_COUNTER,
};
use vineflower_rs::engine::import_collector::ImportCollector;
use vineflower_rs::engine::method_processor::{
    ExpressionMethod, InitialMethod, initial_statement_graph,
};
use vineflower_rs::engine::{Cx, Options};
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
    SecondaryFunctions = 10,
    PatternMatchingEntry = 11,
    IfPatterns = 12,
    SwitchEntry = 13,
    SwitchPasses = 14,
    TryEntry = 15,
    TryResources = 16,
    InlineBlocks = 17,
    LateLoopPasses = 18,
    ExitEntry = 19,
    ExitCondensation = 20,
    MainLoopEnd = 21,
    PostSwitches = 22,
    AfterMain = 23,
    VariableDefinitions = 24,
    MethodEnd = 25,
}

#[derive(Clone, Copy)]
struct Profile {
    simplify: bool,
    ternary: bool,
    ternary_constants: bool,
    lvt: bool,
    boolean_as_int: bool,
    assertions: bool,
}

const DEFAULT: Profile = Profile {
    simplify: true,
    ternary: true,
    ternary_constants: false,
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

const SECONDARY_PROFILES: &[Profile] = &[
    DEFAULT,
    Profile {
        ternary_constants: true,
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

const SECONDARY_FUNCTION_STAGES: &[(&str, &str)] = &[
    (
        "Structure and return value after secondary functions",
        "counters=",
    ),
    (
        "Expressions and cast/boxing flags after secondary functions",
        "counters=",
    ),
    ("Variable versions after secondary functions", "versions="),
    ("Direct graph after secondary functions", "graph="),
];

const PATTERN_MATCHING_ENTRY_STAGES: &[(&str, &str)] = &[
    ("Structure before pattern matching", "counters="),
    (
        "Expressions and intersection casts before pattern matching",
        "counters=",
    ),
    ("Variable versions before pattern matching", "versions="),
    ("Direct graph before pattern matching", "graph="),
];

const IF_PATTERN_STAGES: &[(&str, &str)] = &[
    (
        "Structure and return value after instanceof pattern matching",
        "counters=",
    ),
    ("Type and record pattern expressions", "counters="),
    (
        "Variable versions after instanceof pattern matching",
        "versions=",
    ),
    ("Direct graph after instanceof pattern matching", "graph="),
];

const SWITCH_ENTRY_STAGES: &[(&str, &str)] = &[
    ("Structure before switch processing", "counters="),
    ("Expressions before switch processing", "counters="),
    ("Variable versions before switch processing", "versions="),
    ("Direct graph before switch processing", "graph="),
];

const SWITCH_PASS_STAGES: &[(&str, &str)] = &[
    (
        "Structure and pass results after switch recovery",
        "counters=",
    ),
    (
        "Switch and yield expressions after switch recovery",
        "counters=",
    ),
    ("Variable versions after switch recovery", "versions="),
    ("Direct graph after switch recovery", "graph="),
];

const TRY_ENTRY_STAGES: &[(&str, &str)] = &[
    ("Structure before try processing", "counters="),
    ("Expressions before try processing", "counters="),
    ("Variable versions before try processing", "versions="),
    ("Direct graph before try processing", "graph="),
];

const TRY_RESOURCE_STAGES: &[(&str, &str)] = &[
    ("Structure and return value after try recovery", "counters="),
    ("Resources and expressions after try recovery", "counters="),
    ("Variable versions after try recovery", "versions="),
    ("Direct graph after try recovery", "graph="),
];

const INLINE_BLOCK_STAGES: &[(&str, &str)] = &[
    (
        "Structure and return value after single-block inlining",
        "counters=",
    ),
    (
        "Resources and expressions after single-block inlining",
        "counters=",
    ),
    ("Variable versions after single-block inlining", "versions="),
    ("Direct graph after single-block inlining", "graph="),
];

const LATE_LOOP_PASS_STAGES: &[(&str, &str)] = &[
    (
        "Structure and return values after late loop passes",
        "counters=",
    ),
    (
        "Loop headers and expressions after late loop passes",
        "counters=",
    ),
    ("Variable versions after late loop passes", "versions="),
    ("Direct graph after late loop passes", "graph="),
];

const EXIT_ENTRY_STAGES: &[(&str, &str)] = &[
    ("Structure before exit condensation", "counters="),
    ("Expressions before exit condensation", "counters="),
    ("Variable versions before exit condensation", "versions="),
    ("Direct graph before exit condensation", "graph="),
];

const EXIT_CONDENSATION_STAGES: &[(&str, &str)] = &[
    (
        "Structure and return value after exit condensation",
        "counters=",
    ),
    ("Expressions after exit condensation", "counters="),
    ("Variable versions after exit condensation", "versions="),
    ("Direct graph after exit condensation", "graph="),
];

const MAIN_LOOP_END_STAGES: &[(&str, &str)] = &[
    ("Structure at main loop completion", "counters="),
    ("Expressions at main loop completion", "counters="),
    ("Variable versions at main loop completion", "versions="),
    ("Direct graph at main loop completion", "graph="),
];

const POST_SWITCH_STAGES: &[(&str, &str)] = &[
    (
        "Structure and return value after post-main switch simplification",
        "counters=",
    ),
    (
        "Expressions after post-main switch simplification",
        "counters=",
    ),
    (
        "Variable versions after post-main switch simplification",
        "versions=",
    ),
    (
        "Direct graph after post-main switch simplification",
        "graph=",
    ),
];

const AFTER_MAIN_STAGES: &[(&str, &str)] = &[
    ("Structure before AFTER_MAIN plugins", "counters="),
    (
        "Expressions and monitor assignments before AFTER_MAIN plugins",
        "counters=",
    ),
    ("Variable versions before AFTER_MAIN plugins", "versions="),
    ("Direct graph before AFTER_MAIN plugins", "graph="),
];

const VARIABLE_DEFINITION_STAGES: &[(&str, &str)] = &[
    ("Structure after variable definitions", "counters="),
    (
        "Declarations and expressions after variable definitions",
        "counters=",
    ),
    (
        "Variable names, types and scopes after variable definitions",
        "versions=",
    ),
    ("Direct graph after variable definitions", "graph="),
];

const METHOD_END_STAGES: &[(&str, &str)] = &[
    ("Structure before AT_END plugins", "counters="),
    ("Expressions before AT_END plugins", "counters="),
    ("Variables before AT_END plugins", "versions="),
    ("Final method structure", "counters="),
    ("Final method expressions", "counters="),
    ("Final method variables", "versions="),
    ("Final phantom continue edges", "phantom-continues="),
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
            | Self::MainLoopLabels
            | Self::PatternMatchingEntry
            | Self::IfPatterns
            | Self::SwitchEntry
            | Self::SwitchPasses
            | Self::TryEntry
            | Self::TryResources
            | Self::InlineBlocks
            | Self::LateLoopPasses
            | Self::ExitEntry
            | Self::ExitCondensation
            | Self::MainLoopEnd
            | Self::PostSwitches
            | Self::AfterMain
            | Self::VariableDefinitions
            | Self::MethodEnd => &[DEFAULT],
            Self::SecondaryFunctions => SECONDARY_PROFILES,
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
            Self::SecondaryFunctions => SECONDARY_FUNCTION_STAGES,
            Self::PatternMatchingEntry => PATTERN_MATCHING_ENTRY_STAGES,
            Self::IfPatterns => IF_PATTERN_STAGES,
            Self::SwitchEntry => SWITCH_ENTRY_STAGES,
            Self::SwitchPasses => SWITCH_PASS_STAGES,
            Self::TryEntry => TRY_ENTRY_STAGES,
            Self::TryResources => TRY_RESOURCE_STAGES,
            Self::InlineBlocks => INLINE_BLOCK_STAGES,
            Self::LateLoopPasses => LATE_LOOP_PASS_STAGES,
            Self::ExitEntry => EXIT_ENTRY_STAGES,
            Self::ExitCondensation => EXIT_CONDENSATION_STAGES,
            Self::MainLoopEnd => MAIN_LOOP_END_STAGES,
            Self::PostSwitches => POST_SWITCH_STAGES,
            Self::AfterMain => AFTER_MAIN_STAGES,
            Self::VariableDefinitions => VARIABLE_DEFINITION_STAGES,
            Self::MethodEnd => METHOD_END_STAGES,
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
            Self::SecondaryFunctions => "secondary-functions",
            Self::PatternMatchingEntry => "pattern-matching-entry",
            Self::IfPatterns => "if-patterns",
            Self::SwitchEntry => "switch-entry",
            Self::SwitchPasses => "switch-passes",
            Self::TryEntry => "try-entry",
            Self::TryResources => "try-resources",
            Self::InlineBlocks => "inline-blocks",
            Self::LateLoopPasses => "late-loop-passes",
            Self::ExitEntry => "exit-entry",
            Self::ExitCondensation => "exit-condensation",
            Self::MainLoopEnd => "main-loop-end",
            Self::PostSwitches => "post-switches",
            Self::AfterMain => "after-main",
            Self::VariableDefinitions => "variable-definitions",
            Self::MethodEnd => "method-end",
        }
    }

    fn uses_loop_headers(self) -> bool {
        matches!(
            self,
            Self::LoopEnhancement
                | Self::LoopMerge
                | Self::MainLoopLabels
                | Self::SecondaryFunctions
        ) || self.settles_pattern_entry()
    }

    fn identifies_labels(self) -> bool {
        matches!(self, Self::MainLoopLabels | Self::SecondaryFunctions)
            || self.settles_pattern_entry()
    }

    fn settles_pattern_entry(self) -> bool {
        self == Self::PatternMatchingEntry || self.matches_if_patterns()
    }

    fn matches_if_patterns(self) -> bool {
        matches!(self, Self::IfPatterns | Self::SwitchEntry) || self.recovers_switches()
    }

    fn recovers_switches(self) -> bool {
        matches!(self, Self::SwitchPasses | Self::TryEntry) || self.recovers_resources()
    }

    fn recovers_resources(self) -> bool {
        matches!(
            self,
            Self::TryResources
                | Self::InlineBlocks
                | Self::LateLoopPasses
                | Self::ExitEntry
                | Self::ExitCondensation
                | Self::MainLoopEnd
                | Self::PostSwitches
                | Self::AfterMain
                | Self::VariableDefinitions
                | Self::MethodEnd
        )
    }

    fn publishes_wrappers(self) -> bool {
        self == Self::PostSwitches || self.finishes_post_processing()
    }

    fn finishes_post_processing(self) -> bool {
        self == Self::AfterMain || self.defines_variables()
    }

    fn defines_variables(self) -> bool {
        matches!(self, Self::VariableDefinitions | Self::MethodEnd)
    }

    fn expression_detail(self) -> expression_snapshot::Detail {
        use expression_snapshot::Detail;
        match self {
            Self::MethodEnd => Detail::MethodEnd,
            Self::VariableDefinitions => Detail::VariableDefinitions,
            Self::AfterMain => Detail::AfterMain,
            _ if self.recovers_resources() => Detail::Resources,
            _ if self.recovers_switches() => Detail::Switches,
            _ if self.settles_pattern_entry() => Detail::IntersectionCasts,
            Self::SecondaryFunctions => Detail::SecondaryFunctions,
            _ if self.uses_loop_headers() => Detail::LoopHeaders,
            _ => Detail::Base,
        }
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
    optional_casts: usize,
    forced_boxing: usize,
    intersection_casts: usize,
    intersection_variables: usize,
}

impl EnhancementCoverage {
    fn record(&mut self, check: Check, method: &str, row: &str) {
        let mut snapshots = row.split('\t');
        let tree = snapshots.next().unwrap();
        self.changed_methods +=
            usize::from(tree.ends_with(";enhanced=true") || tree.ends_with(";secondary=true"));
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
            if check.expression_detail() >= expression_snapshot::Detail::SecondaryFunctions
                && field.starts_with('e')
                && let Some((_, node)) = field.split_once('=')
            {
                self.optional_casts +=
                    usize::from(node.starts_with("FUNCTION|") && node.ends_with("|false"));
                self.forced_boxing +=
                    usize::from(node.starts_with("INVOCATION|") && node.ends_with("|true"));
                if check == Check::PatternMatchingEntry {
                    self.intersection_variables +=
                        usize::from(node.starts_with("VAR|") && node.ends_with("|true"));
                    let mut fields = node.split('|');
                    if fields.next() == Some("FUNCTION") && fields.nth(2) == Some("CAST") {
                        self.intersection_casts +=
                            usize::from(fields.next().unwrap().split(',').count() > 2);
                    }
                }
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
        } else if check == Check::SecondaryFunctions {
            eprintln!(
                "{} methods reported a change from secondary functions",
                self.changed_methods
            );
            eprintln!(
                "{} expressions omit casts and {} invocations retain explicit boxing",
                self.optional_casts, self.forced_boxing
            );
        } else if check == Check::PatternMatchingEntry {
            eprintln!(
                "{} intersection casts and {} variable expressions marked as intersection types",
                self.intersection_casts, self.intersection_variables
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

#[derive(Default)]
struct SecondaryComparison {
    baseline: Vec<String>,
    return_changes: usize,
    tree_changes: usize,
    expression_changes: usize,
    counter_changes: usize,
}

#[derive(Default)]
struct IfPatternCoverage {
    changed_methods: usize,
    methods_with_patterns: usize,
    matched_conditionals: usize,
    record_patterns: usize,
    record_bounds: usize,
    changed_with_counter_updates: usize,
    unchanged_with_counter_updates: usize,
}

#[derive(Default)]
struct SwitchCoverage {
    pattern_methods: usize,
    expression_methods: usize,
    both_methods: usize,
    phantom: usize,
    guards: usize,
    switch_expressions: usize,
    yields: usize,
    post_methods: usize,
    exit_offsets: usize,
    boxing_retained: usize,
}

#[derive(Default)]
struct ResourceCoverage {
    changed_methods: usize,
    methods_with_resources: usize,
    resource_statements: usize,
    resources: usize,
    changed_do_whiles: usize,
    condensed_loops: usize,
    condensed_exits: usize,
}

impl ResourceCoverage {
    fn record(&mut self, row: &str) {
        let mut snapshots = row.split('\t');
        let tree = snapshots.next().unwrap();
        self.changed_methods += usize::from(
            tree.ends_with(";try-resources=true") || tree.ends_with(";inline-blocks=true"),
        );
        self.changed_do_whiles +=
            usize::from(tree.ends_with(";do-while=true;condense-loops=skipped"));
        self.condensed_loops += usize::from(tree.ends_with(";condense-loops=true"));
        self.condensed_exits += usize::from(tree.ends_with(";condense-exits=true"));
        let mut method_has_resources = false;
        for field in snapshots.next().unwrap().split(';') {
            if let Some((key, list)) = field.split_once('=')
                && key.starts_with("resources")
                && !list.is_empty()
            {
                method_has_resources = true;
                self.resource_statements += 1;
                self.resources += list.split(',').count();
            }
        }
        self.methods_with_resources += usize::from(method_has_resources);
    }

    fn report(&self, check: Check) {
        match check {
            Check::TryResources | Check::InlineBlocks => {
                eprintln!("{} methods reported a change.", self.changed_methods);
            }
            Check::LateLoopPasses => eprintln!(
                "{} methods changed in do-while recovery and {} in infinite-loop return condensation.",
                self.changed_do_whiles, self.condensed_loops
            ),
            Check::ExitCondensation => {
                eprintln!("{} methods condensed exits.", self.condensed_exits)
            }
            _ => {}
        }
        eprintln!(
            "{} methods contain {} resources across {} try statements.",
            self.methods_with_resources, self.resources, self.resource_statements
        );
    }
}

impl SwitchCoverage {
    fn record(&mut self, check: Check, row: &str) {
        let mut snapshots = row.split('\t');
        let tree = snapshots.next().unwrap();
        let patterns = tree.split(';').any(|field| field == "switch-patterns=true");
        let expressions = tree.ends_with(";switch-expressions=true");
        self.pattern_methods += usize::from(patterns);
        self.expression_methods += usize::from(expressions);
        self.both_methods += usize::from(patterns && expressions);
        self.post_methods += usize::from(tree.ends_with(";post-switches=true"));
        self.phantom += tree
            .split(';')
            .filter(|field| *field == "phantom=true")
            .count();
        for field in snapshots.next().unwrap().split(';') {
            if let Some((key, value)) = field.split_once('=') {
                if key.starts_with("guards") {
                    self.guards += value
                        .split(',')
                        .filter(|guard| !guard.is_empty() && *guard != "~")
                        .count();
                } else if key.starts_with('e') {
                    self.switch_expressions += usize::from(value.starts_with("SWITCH|"));
                    self.yields += usize::from(value.starts_with("YIELD|"));
                    if check == Check::AfterMain {
                        self.exit_offsets += usize::from(
                            key.starts_with("exit-offsets") && value != "~" && !value.is_empty(),
                        );
                        self.boxing_retained += usize::from(
                            value.starts_with("INVOCATION|") && value.ends_with("|false"),
                        );
                    }
                }
            }
        }
    }

    fn report(&self, check: Check) {
        if check == Check::SwitchPasses {
            eprintln!(
                "{} methods changed during switch pattern recovery, {} during switch expression recovery, and {} during both",
                self.pattern_methods, self.expression_methods, self.both_methods
            );
        }
        if check.publishes_wrappers() {
            eprintln!(
                "{} methods changed during post-main switch simplification.",
                self.post_methods
            );
        }
        if check == Check::AfterMain {
            eprintln!(
                "{} dummy exits carry bytecode offsets and {} invocations retain boxing in writing",
                self.exit_offsets, self.boxing_retained
            );
        }
        eprintln!(
            "{} switch expressions, {} yields, {} guarded cases, and {} phantom statements",
            self.switch_expressions, self.yields, self.guards, self.phantom
        );
    }
}

impl IfPatternCoverage {
    fn record(&mut self, check: Check, row: &str) {
        let mut snapshots = row.split('\t');
        let tree = snapshots.next().unwrap();
        if check == Check::IfPatterns {
            let (tree, result) = tree.rsplit_once(";if-patterns=").unwrap();
            let (tree, before) = tree.rsplit_once(";pattern-counters-before=").unwrap();
            let after = split_counters(tree).0.strip_prefix("counters=").unwrap();
            let changed = result == "true";
            self.changed_methods += usize::from(changed);
            self.changed_with_counter_updates += usize::from(changed && before != after);
            self.unchanged_with_counter_updates += usize::from(!changed && before != after);
        }
        let mut matched_conditionals = 0;
        for field in snapshots.next().unwrap().split(';') {
            matched_conditionals +=
                usize::from(field.starts_with("pattern") && field.ends_with("=true"));
            if field.starts_with('e')
                && let Some((_, body)) = field.split_once('=')
                && body.starts_with("PATTERN|")
            {
                self.record_patterns += 1;
                if body
                    .rsplit_once('|')
                    .unwrap()
                    .1
                    .split('/')
                    .any(|bound| !bound.is_empty() && bound != "~")
                {
                    self.record_bounds += 1;
                }
            }
        }
        self.matched_conditionals += matched_conditionals;
        self.methods_with_patterns += usize::from(matched_conditionals > 0);
    }

    fn report(&self, check: Check) {
        if check == Check::IfPatterns {
            eprintln!(
                "{} methods reported a pattern change. Counters advanced in {} changed methods and {} unchanged methods.",
                self.changed_methods,
                self.changed_with_counter_updates,
                self.unchanged_with_counter_updates
            );
        }
        eprintln!(
            "{} methods contain {} matched conditionals and {} record patterns, with bound overrides on {} record patterns",
            self.methods_with_patterns,
            self.matched_conditionals,
            self.record_patterns,
            self.record_bounds
        );
    }
}

impl SecondaryComparison {
    fn record_variant(&mut self, index: usize, variant: &str) {
        let mut baseline = self.baseline[index].split('\t');
        let mut variant = variant.split('\t');
        let baseline_tree = baseline.next().unwrap();
        let variant_tree = variant.next().unwrap();
        let (baseline_tree, baseline_result) = baseline_tree
            .rsplit_once(";secondary=")
            .unwrap_or((baseline_tree, ""));
        let (variant_tree, variant_result) = variant_tree
            .rsplit_once(";secondary=")
            .unwrap_or((variant_tree, ""));
        let (baseline_counters, baseline_tree) = split_counters(baseline_tree);
        let (variant_counters, variant_tree) = split_counters(variant_tree);
        self.return_changes += usize::from(baseline_result != variant_result);
        self.tree_changes += usize::from(baseline_tree != variant_tree);
        self.counter_changes += usize::from(baseline_counters != variant_counters);
        let expressions = |field| split_counters(field).1;
        self.expression_changes +=
            usize::from(baseline.next().map(expressions) != variant.next().map(expressions));
    }
}

fn split_counters(snapshot: &str) -> (&str, &str) {
    if snapshot.starts_with("counters=")
        && let Some(fields) = snapshot.split_once(';')
    {
        fields
    } else {
        ("", snapshot)
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
    let mut switch_rejected = 0;
    let mut transferred_continue_order = 0;
    let mut hidden_changes = [0, 0];
    let mut repeats = 0;
    let mut changed_original = 0;
    let mut concats = 0;
    let mut assertion_changes = 0;
    let mut loop_coverage = LoopCoverage::default();
    let mut enhancement_coverage = EnhancementCoverage::default();
    let mut secondary_coverage = EnhancementCoverage::default();
    let mut secondary_comparison = SecondaryComparison::default();
    let mut if_pattern_coverage = IfPatternCoverage::default();
    let mut switch_coverage = SwitchCoverage::default();
    let mut resource_coverage = ResourceCoverage::default();
    let methods_per_profile = methods.len() / check.profiles().len();
    for (index, method) in methods.iter().enumerate() {
        let row = java_rows
            .next()
            .expect("missing Java stack snapshot")
            .unwrap();
        let (id, java) = row.split_once('\t').unwrap();
        let (java, continue_moves) = java.rsplit_once("\tcontinue-moves=").unwrap_or((java, ""));
        let (java, at_end_moves) = java
            .rsplit_once("\tat-end-continue-moves=")
            .unwrap_or((java, ""));
        let rust = rust_rows
            .next()
            .expect("missing Rust stack snapshot")
            .unwrap();
        assert_eq!(id.parse::<usize>().unwrap(), index);
        let secondary_variant = check == Check::SecondaryFunctions && index >= methods_per_profile;
        if check == Check::SecondaryFunctions {
            if secondary_variant {
                secondary_comparison.record_variant(index - methods_per_profile, &rust);
            } else {
                secondary_comparison.baseline.push(rust.clone());
            }
        }
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
            continue;
        } else if same_switch_case_rejection(check, java, &rust) {
            switch_rejected += 1;
            continue;
        }
        if let Err(diff) = compare_snapshots(java, &rust, stages) {
            if same_transferred_continues(check, java, &rust, continue_moves, at_end_moves) {
                transferred_continue_order += 1;
            } else {
                errors.push(format!("{method}\n  {diff}"));
                continue;
            }
        }
        if secondary_variant {
            secondary_coverage.record(check, method, &rust);
        } else if check.uses_loop_headers() {
            enhancement_coverage.record(check, method, &rust);
            if check.matches_if_patterns() {
                if_pattern_coverage.record(check, &rust);
            }
            if check.recovers_switches() {
                switch_coverage.record(check, &rust);
            }
            if check.recovers_resources() {
                resource_coverage.record(&rust);
            }
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
        methods.len() - rejected - switch_rejected - transferred_continue_order,
        check.name(),
        groups.iter().map(Vec::len).sum::<usize>()
    );
    if switch_rejected > 0 {
        eprintln!("{switch_rejected} matching switch case type rejections in variable versioning");
    }
    if transferred_continue_order > 0 {
        eprintln!(
            "{transferred_continue_order} snapshots agree after accounting for continue order in recorded loop-elimination batches"
        );
    }
    if check.uses_loop_headers() {
        if check == Check::SecondaryFunctions {
            eprintln!("With default ternary constant simplification");
        }
        enhancement_coverage.report(check);
        if check.matches_if_patterns() {
            if_pattern_coverage.report(check);
        }
        if check.recovers_switches() {
            switch_coverage.report(check);
        }
        if check.recovers_resources() {
            resource_coverage.report(check);
        }
        if check == Check::SecondaryFunctions {
            eprintln!("With ternary constant simplification enabled");
            secondary_coverage.report(check);
            eprintln!(
                "Relative to the default, {} return values, {} trees, {} expression snapshots and {} method counters changed",
                secondary_comparison.return_changes,
                secondary_comparison.tree_changes,
                secondary_comparison.expression_changes,
                secondary_comparison.counter_changes
            );
        }
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
    options.ternary_constant_simplification = profile.ternary_constants;
    options.use_lvt_names = profile.lvt;
    options.boolean_as_int = profile.boolean_as_int;
    options.decompile_assert = profile.assertions;
    let options = Arc::new(options);
    let mut context = StructContext::new(Arc::clone(&options), None);
    if let Some(runtime) = runtime {
        context.add_space(Arc::clone(runtime), false);
    }
    for fixture in group {
        context.add_file(&fixture.path, true).unwrap();
    }
    let mut cx = Cx::new(Arc::new(context));
    cx.class_nodes = load_classes(
        &cx.struct_context,
        &options,
        |_| true,
        |_| true,
        |_, _| None,
    );
    if check.publishes_wrappers() {
        write_published_group(
            input,
            snapshots,
            methods,
            group_index,
            group,
            profile,
            &mut cx,
            check,
        );
        return;
    }
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
            write_method_input(
                input,
                methods,
                group_index,
                fixture,
                profile,
                check,
                &cx,
                method,
                &initial,
            );

            let snapshot = match imports {
                Ok(imports) => describe(&mut cx, id, &class, method, initial, imports, check),
                Err(error) => format!("class-rejected={}", one_line(error)),
            };
            writeln!(snapshots, "{snapshot}").unwrap();
        }
    }
}

fn write_method_input(
    input: &mut impl Write,
    methods: &mut Vec<String>,
    group_index: usize,
    fixture: &Fixture,
    profile: Profile,
    check: Check,
    cx: &Cx,
    method: &StructMethod,
    initial: &InitialMethod,
) {
    let options = &cx.options;
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
    if check == Check::SecondaryFunctions {
        write_flag(input, profile.ternary_constants).unwrap();
    }
    write_text(input, &fixture.name).unwrap();
    write_cfg(input, &cx.ir, &initial.flow.graph).unwrap();
    methods.push(format!(
        "{} {method} simplify-stack={} ternary-in-if={} lvt={} boolean-as-int={} assertions={} ternary-constant-simplification={}",
        fixture.path.display(),
        profile.simplify,
        profile.ternary,
        profile.lvt,
        profile.boolean_as_int,
        profile.assertions,
        profile.ternary_constants,
    ));
}

fn write_published_group(
    input: &mut impl Write,
    snapshots: &mut impl Write,
    methods: &mut Vec<String>,
    group_index: usize,
    group: &[Fixture],
    profile: Profile,
    cx: &mut Cx,
    check: Check,
) {
    let mut roots = BTreeMap::<ClassNodeId, Vec<&Fixture>>::new();
    let mut order = Vec::new();
    let fixtures: HashMap<_, _> = group
        .iter()
        .map(|fixture| (fixture.name.as_str(), fixture))
        .collect();
    for fixture in group {
        let mut root = cx.class_nodes.id(&fixture.name).unwrap();
        while let Some(parent) = cx.class_nodes[root].parent {
            root = parent;
        }
        if !roots.contains_key(&root) {
            order.push(root);
        }
        roots.entry(root).or_default().push(fixture);
    }
    for root in order {
        let count = methods.len();
        let result = process_class_methods(cx, root, |cx, class, method| {
            let Some(initial) = initial_statement_graph(cx, class, method)? else {
                return Ok(None);
            };
            let fixture = fixtures[class.qualified_name.as_str()];
            write_method_input(
                input,
                methods,
                group_index,
                fixture,
                profile,
                check,
                cx,
                method,
                &initial,
            );
            let owner = cx.class_nodes.id(&class.qualified_name).unwrap();
            let operation = Cell::new("structure");
            let processed = catch_unwind(AssertUnwindSafe(|| {
                let initial_hidden = cx.class_nodes[owner].hidden_members.clone();
                let mut method = lift_method(cx, class, initial, &operation)?;
                operation.set("prepare-main-loop");
                method.prepare_main_loop(cx, class)?;
                operation.set("finish-main-loop");
                method.finish_main_loop(cx, class)?;
                operation.set("simplify-switches");
                let simplified = method.simplify_switches(cx, class)?;
                if check.finishes_post_processing() {
                    operation.set("finish-post-processing");
                    method.finish_post_processing(cx)?;
                }
                if check.defines_variables() {
                    operation.set("set-var-definitions");
                    method.set_var_definitions(cx)?;
                }
                if check == Check::MethodEnd {
                    operation.set("prepare-method-end");
                    method.prepare_method_end(cx)?;
                }
                let details = format!(";post-switches={simplified}");
                operation.set("snapshot");
                let mut state = snapshot(cx, owner, &method, &initial_hidden, check, &details);
                if check == Check::MethodEnd {
                    operation.set("finish-method");
                    method.finish_method(cx, class)?;
                    operation.set("final-snapshot");
                    let final_state =
                        snapshot(cx, owner, &method, &initial_hidden, check, &details);
                    let phantom = phantom_continues(&cx.ir, method.root);
                    write!(state, "\t{final_state}\t{phantom}").unwrap();
                } else {
                    let graph = direct_graph_snapshot::enhanced(&mut cx.ir, method.root);
                    write!(state, "\t{graph}").unwrap();
                }
                writeln!(snapshots, "{state}").unwrap();
                Ok::<_, io::Error>(method)
            }));
            match processed {
                Ok(Ok(method)) => Ok(Some(method)),
                Ok(Err(error)) => {
                    writeln!(
                        snapshots,
                        "{}",
                        io_stage_error(check, operation.get(), &error)
                    )
                    .unwrap();
                    Err(error)
                }
                Err(error) => {
                    let error = panic_text(&*error);
                    writeln!(
                        snapshots,
                        "{}",
                        stage_error(check, operation.get(), "panic", &error)
                    )
                    .unwrap();
                    Err(io::Error::other(error))
                }
            }
        });
        if let Err(error) = result {
            assert_eq!(
                methods.len(),
                count,
                "wrapper processing aborted after a callback"
            );
            for fixture in &roots[&root] {
                let id = cx.class_nodes.id(&fixture.name).unwrap();
                let class = Arc::clone(&cx.class_nodes[id].class);
                for method in &class.methods {
                    let Some(initial) = initial_statement_graph(cx, &class, method).unwrap() else {
                        continue;
                    };
                    write_method_input(
                        input,
                        methods,
                        group_index,
                        fixture,
                        profile,
                        check,
                        cx,
                        method,
                        &initial,
                    );
                    writeln!(snapshots, "class-rejected={}", one_line(&error.to_string())).unwrap();
                }
            }
        }
    }
}

fn lift_method(
    cx: &mut Cx,
    class: &StructClass,
    initial: InitialMethod,
    operation: &Cell<&str>,
) -> io::Result<ExpressionMethod> {
    let structured = initial.structure(cx)?;
    operation.set("finally");
    let recovered = structured.recover_finally(cx, class)?;
    operation.set("lift");
    recovered.into_expressions(cx, class)
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
        let mut method = lift_method(cx, class, initial, &operation)?;
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
                | Check::MainLoopLabels
                | Check::SecondaryFunctions
                | Check::PatternMatchingEntry
                | Check::IfPatterns
                | Check::SwitchEntry
                | Check::SwitchPasses
                | Check::TryEntry
                | Check::TryResources
                | Check::InlineBlocks
                | Check::LateLoopPasses
                | Check::ExitEntry
                | Check::ExitCondensation
                | Check::MainLoopEnd,
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
                if !check.identifies_labels() {
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
                    } else if check == Check::MainLoopEnd {
                        operation.set("finish-main-loop");
                        method.finish_main_loop(cx, class)?;
                        String::new()
                    } else if matches!(check, Check::ExitEntry | Check::ExitCondensation) {
                        operation.set("prepare-exits");
                        method.prepare_exits(cx, class)?;
                        if check == Check::ExitCondensation {
                            operation.set("condense-exits");
                            format!(";condense-exits={}", method.condense_exits(cx)?)
                        } else {
                            String::new()
                        }
                    } else if check == Check::LateLoopPasses {
                        operation.set("prepare-late-loops");
                        method.prepare_late_loops(cx, class)?;
                        operation.set("make-do-while-loops");
                        let changed = method.make_do_while_loops(cx)?;
                        if changed {
                            ";do-while=true;condense-loops=skipped".to_owned()
                        } else {
                            operation.set("condense-infinite-loops");
                            format!(
                                ";do-while=false;condense-loops={}",
                                method.condense_infinite_loops(cx)?
                            )
                        }
                    } else if check == Check::InlineBlocks {
                        operation.set("prepare-inline");
                        method.prepare_inline(cx, class)?;
                        operation.set("inline-single-blocks");
                        format!(";inline-blocks={}", method.inline_single_blocks(cx)?)
                    } else if matches!(check, Check::TryEntry | Check::TryResources) {
                        operation.set("prepare-try");
                        method.prepare_try(cx, class)?;
                        if check == Check::TryResources {
                            operation.set("enhance-try");
                            format!(";try-resources={}", method.enhance_try(cx, class))
                        } else {
                            String::new()
                        }
                    } else if matches!(check, Check::SwitchEntry | Check::SwitchPasses) {
                        operation.set("prepare-switches");
                        method.prepare_switches(cx, class)?;
                        if check == Check::SwitchPasses {
                            operation.set("process-switch-patterns");
                            let patterns = method.process_switch_patterns(cx)?;
                            let counters = counter_snapshot(&method.flow.counters);
                            operation.set("process-switch-expressions");
                            let expressions = method.process_switch_expressions(cx)?;
                            format!(
                                ";switch-patterns={patterns};switch-pattern-counters={counters};switch-expressions={expressions}"
                            )
                        } else {
                            String::new()
                        }
                    } else if check.settles_pattern_entry() {
                        operation.set("prepare-pattern-matching");
                        method.prepare_pattern_matching(cx, class)?;
                        if check == Check::IfPatterns {
                            operation.set("match-if-patterns");
                            let before = counter_snapshot(&method.flow.counters);
                            let changed = method.match_if_patterns(cx, class)?;
                            format!(";pattern-counters-before={before};if-patterns={changed}")
                        } else {
                            String::new()
                        }
                    } else {
                        operation.set("identify-main-loop-labels");
                        method.identify_main_loop_labels(cx, class)?;
                        if check == Check::SecondaryFunctions {
                            operation.set("identify-secondary");
                            format!(";secondary={}", method.identify_secondary(cx)?)
                        } else {
                            String::new()
                        }
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
            (
                Check::PostSwitches
                | Check::AfterMain
                | Check::VariableDefinitions
                | Check::MethodEnd,
                _,
            ) => {
                unreachable!("Post-main methods run in wrapper order")
            }
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
        Ok(Err(error)) => io_stage_error(check, operation.get(), &error),
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
    let mut tree = structure_snapshot_with_edges(
        cx,
        method.root,
        &method.flow.counters,
        loop_stage,
        check.recovers_switches(),
    );
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
    let expressions = expression_snapshot::snapshot_details(
        cx,
        method.root,
        &method.flow.counters,
        check.expression_detail(),
    );
    let mut snapshot =
        format!("{tree};hidden={all_members};hidden-added={added}{details}\t{expressions}");
    if check != Check::Stack {
        let processor = &cx.ir[method.flow.variables];
        let mut versions = variable_snapshot(&processor.versions);
        if check.defines_variables() {
            append_definition_metadata(&mut versions, processor);
        }
        write!(snapshot, "\t{versions}").unwrap();
    }
    snapshot
}

fn phantom_continues(ir: &Ir, root: StatId) -> String {
    let edges = structure_statements(ir, root)
        .flat_map(|stat| ir[stat].all_successors())
        .filter(|&&edge| ir[edge].phantom_continue)
        .map(|&edge| edge_id(ir, Some(edge)))
        .join("|");
    format!("phantom-continues={edges}")
}

fn counter_snapshot(counters: &CounterContainer) -> String {
    format!(
        "{},{},{}",
        counters.get_counter(STATEMENT_COUNTER),
        counters.get_counter(EXPRESSION_COUNTER),
        counters.get_counter(VAR_COUNTER)
    )
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

fn io_stage_error(check: Check, operation: &str, error: &io::Error) -> String {
    let message = error.to_string();
    if error.kind() == io::ErrorKind::InvalidData {
        if message == "parsing failure!" {
            return "rejected=parsing failure!".into();
        }
        if message.starts_with("Invalid switch case set") {
            return stage_error(check, operation, "invalid-data", &one_line(&message));
        }
    }
    stage_error(check, operation, "error", &one_line(&message))
}

fn stage_error(check: Check, operation: &str, kind: &str, message: &str) -> String {
    if check == Check::Stack {
        format!("stack-{kind}={message}")
    } else {
        format!("{}-{operation}-{kind}={message}", check.name())
    }
}

fn same_switch_case_rejection(check: Check, java: &str, rust: &str) -> bool {
    let operation = match check {
        Check::TryEntry | Check::TryResources => "prepare-try",
        Check::InlineBlocks => "prepare-inline",
        Check::LateLoopPasses => "prepare-late-loops",
        Check::ExitEntry | Check::ExitCondensation => "prepare-exits",
        Check::MainLoopEnd => "finish-main-loop",
        Check::PostSwitches | Check::AfterMain | Check::VariableDefinitions | Check::MethodEnd => {
            "finish-main-loop"
        }
        _ => return false,
    };
    let Some(java) = java.strip_prefix(check.name()) else {
        return false;
    };
    let Some(rust) = rust.strip_prefix(check.name()) else {
        return false;
    };
    if !java.starts_with(
        "-set-var-versions-error=java.lang.IllegalStateException: Invalid switch case set:",
    ) || !rust.starts_with(&format!(
        "-{operation}-invalid-data=Invalid switch case set"
    )) {
        return false;
    }
    let selector = " for selector of type ";
    match (java.rsplit_once(selector), rust.rsplit_once(selector)) {
        (Some((_, java)), Some((_, rust))) => !java.is_empty() && java == rust,
        _ => false,
    }
}

fn same_transferred_continues(
    check: Check,
    java: &str,
    rust: &str,
    transfers: &str,
    at_end_transfers: &str,
) -> bool {
    if java == rust || (transfers.is_empty() && at_end_transfers.is_empty()) {
        return false;
    }
    java.split('\t')
        .zip_longest(rust.split('\t'))
        .enumerate()
        .all(|(part, pair)| {
            let itertools::EitherOrBoth::Both(java, rust) = pair else {
                return false;
            };
            java == rust
                || match part {
                    0 if check == Check::MethodEnd => {
                        same_continue_batches(java, rust, at_end_transfers)
                    }
                    0 => same_continue_batches(java, rust, transfers),
                    // The final tree follows the three AT_END fields.
                    3 if check == Check::MethodEnd => same_continue_batches(java, rust, transfers),
                    _ => false,
                }
        })
}

fn same_continue_batches(java: &str, rust: &str, transfers: &str) -> bool {
    if transfers.is_empty() {
        return false;
    }
    let mut batches: HashMap<&str, Vec<Vec<&str>>> = HashMap::new();
    for batch in transfers.split(';') {
        let (loop_id, edges) = batch.split_once(':').unwrap();
        batches
            .entry(loop_id)
            .or_default()
            .push(edges.split('|').collect());
    }
    let mut loop_id = None;
    java.split(';').zip_longest(rust.split(';')).all(|pair| {
        let itertools::EitherOrBoth::Both(java, rust) = pair else {
            return false;
        };
        if let Some(stat) = java.strip_prefix("stat=") {
            loop_id = stat.strip_suffix(":DO");
        }
        java == rust
            || loop_id.is_some_and(|id| {
                batches
                    .get(id)
                    .is_some_and(|batches| matching_incoming_slots(java, rust, batches))
            })
    })
}

fn matching_incoming_slots(java: &str, rust: &str, batches: &[Vec<&str>]) -> bool {
    let (Some(java), Some(rust)) = (java.strip_prefix("in="), rust.strip_prefix("in=")) else {
        return false;
    };
    let java: Vec<_> = java.split('|').collect();
    let rust: Vec<_> = rust.split('|').collect();
    if java.len() != rust.len() {
        return false;
    }
    let mut reordered = FxHashSet::default();
    for batch in batches {
        let slots = java
            .iter()
            .positions(|edge| batch.contains(edge))
            .collect_vec();
        if slots.len() != batch.len()
            || !slots
                .iter()
                .copied()
                .eq(rust.iter().positions(|edge| batch.contains(edge)))
        {
            continue;
        }
        // The same edges must occupy the same slots on both sides.
        if slots
            .iter()
            .map(|&slot| java[slot])
            .sorted()
            .eq(batch.iter().copied().sorted())
            && slots
                .iter()
                .map(|&slot| rust[slot])
                .sorted()
                .eq(batch.iter().copied().sorted())
        {
            reordered.extend(slots);
        }
    }
    java.iter()
        .zip(&rust)
        .enumerate()
        .all(|(slot, (left, right))| left == right || reordered.contains(&slot))
}

pub(super) fn variable_snapshot(versions: &VarVersions) -> String {
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

pub(super) fn append_definition_metadata(fields: &mut String, processor: &VarProcessor) {
    append_variable_bindings(fields, "name", processor.names.iter(), |name| {
        expression_snapshot::text(name.as_deref())
    });
    append_variable_bindings(fields, "this", processor.this_vars.iter(), |name| {
        expression_snapshot::text(Some(name.as_str()))
    });
    append_variable_bindings(fields, "local", processor.local_variables.iter(), |local| {
        expression_snapshot::local_variable(Some(local.as_ref()))
    });
    append_variable_bindings(fields, "clash", processor.clashing_names.iter(), |name| {
        expression_snapshot::text(Some(name.as_str()))
    });
}

fn append_variable_bindings<'a, T: 'a>(
    fields: &mut String,
    label: &str,
    bindings: impl Iterator<Item = (&'a VarVersionPair, &'a T)>,
    format_value: impl Fn(&T) -> String,
) {
    for (pair, value) in bindings.sorted_unstable_by_key(|&(pair, _)| *pair) {
        let value = format_value(value);
        write!(fields, ";{label}{},{}={value}", pair.var, pair.version).unwrap();
    }
}

fn hidden_members<'a>(members: impl Iterator<Item = &'a String>) -> String {
    members
        .sorted_unstable_by(|left, right| left.encode_utf16().cmp(right.encode_utf16()))
        .map(|member| expression_snapshot::text(Some(member)))
        .join(",")
}
