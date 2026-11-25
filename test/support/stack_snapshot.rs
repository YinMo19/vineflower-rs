// SPDX-License-Identifier: Apache-2.0

use std::collections::{BTreeMap, HashMap};
use std::fs;
use std::io::{self, BufRead, BufReader, BufWriter, Seek, Write};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::path::{Path, PathBuf};
use std::sync::Arc;

use itertools::Itertools;
use rustc_hash::FxHashSet;
use vineflower_rs::decompiler::sforms::split_ssa;
use vineflower_rs::decompiler::stack::simplify_statement;
use vineflower_rs::engine::class_nodes::{ClassNodeId, load_classes};
use vineflower_rs::engine::class_processor::prepare_class;
use vineflower_rs::engine::import_collector::ImportCollector;
use vineflower_rs::engine::method_processor::{InitialMethod, initial_statement_graph};
use vineflower_rs::engine::{Cx, Options};
use vineflower_rs::structs::single_file_context_source::SingleFileContextSource;
use vineflower_rs::structs::{StructClass, StructContext, StructMethod};

use super::upstream_reference::Corpus;
use super::{
    compare_snapshots, expression_snapshot, one_line, panic_text, parse_class, structure_snapshot,
    write_cfg, write_count, write_flag, write_int, write_text,
};

#[derive(Clone, Copy)]
struct Profile {
    simplify: bool,
    ternary: bool,
}

const PROFILES: [Profile; 3] = [
    Profile {
        simplify: true,
        ternary: true,
    },
    Profile {
        simplify: false,
        ternary: true,
    },
    Profile {
        simplify: true,
        ternary: false,
    },
];

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

pub fn check(corpus: &Corpus) {
    let groups = class_groups(corpus);
    let mut input = tempfile::NamedTempFile::new().unwrap();
    let mut snapshots = tempfile::tempfile().unwrap();
    let mut methods = Vec::new();
    {
        let mut input = BufWriter::new(input.as_file_mut());
        let mut snapshots = BufWriter::new(&mut snapshots);
        input.write_all(&[3]).unwrap(); // StructureReference's stack phase.
        write_count(&mut input, groups.len()).unwrap();
        for group in &groups {
            write_count(&mut input, group.len()).unwrap();
            for fixture in group {
                write_text(&mut input, fixture.path.to_str().unwrap()).unwrap();
            }
        }
        for profile in PROFILES {
            for (group_index, group) in groups.iter().enumerate() {
                write_group(
                    &mut input,
                    &mut snapshots,
                    &mut methods,
                    group_index,
                    group,
                    profile,
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
        &[
            "DirectGraphSnapshot",
            "ExpressionSnapshot",
            "SsaSnapshot",
            "FinallySnapshot",
            "StackSnapshot",
        ],
        input.path(),
        &reference,
    );
    snapshots.rewind().unwrap();
    reference.rewind().unwrap();
    let mut java_rows = BufReader::new(reference).lines();
    let mut rust_rows = BufReader::new(snapshots).lines();
    let stages = [
        ("First stack simplification structure", "counters="),
        ("First stack simplification expressions", "counters="),
        ("Settled stack structure", "counters="),
        ("Settled stack expressions", "counters="),
    ];
    let mut errors = Vec::new();
    let mut rejected = 0;
    let mut hidden_changes = [0, 0];
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
        if java == rust && (java.starts_with("rejected=") || java.starts_with("class-rejected=")) {
            rejected += 1;
        } else if let Err(diff) = compare_snapshots(java, &rust, &stages) {
            errors.push(format!("{method}\n  {diff}"));
        } else {
            for (tree, changes) in rust.split('\t').step_by(2).zip(&mut hidden_changes) {
                if tree.split(';').any(|field| {
                    field
                        .strip_prefix("hidden-added=")
                        .is_some_and(|added| !added.is_empty())
                }) {
                    *changes += 1;
                }
            }
        }
    }
    assert!(java_rows.next().is_none() && rust_rows.next().is_none());
    assert!(
        errors.is_empty(),
        "{} of {} stack snapshots differ:\n{}",
        errors.len(),
        methods.len(),
        errors
            .iter()
            .take(30)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
    eprintln!(
        "{} exact first and settled stack snapshots and {rejected} matching rejections across {} class files",
        methods.len() - rejected,
        corpus.classes.len()
    );
    let [first, settled] = hidden_changes;
    eprintln!("{first} first simplifications and {settled} settled runs added hidden members");
}

fn write_group(
    input: &mut impl Write,
    snapshots: &mut impl Write,
    methods: &mut Vec<String>,
    group_index: usize,
    group: &[Fixture],
    profile: Profile,
) {
    let mut options = Options::default();
    options.simplify_stack = profile.simplify;
    options.ternary_in_if = profile.ternary;
    let options = Arc::new(options);
    let mut context = StructContext::new(Arc::clone(&options), None);
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
            write_text(input, &fixture.name).unwrap();
            write_cfg(input, &cx.ir, &initial.flow.graph).unwrap();

            let snapshot = match imports {
                Ok(imports) => describe(&mut cx, id, &class, method, initial, imports),
                Err(error) => format!("class-rejected={}", one_line(error)),
            };
            writeln!(snapshots, "{snapshot}").unwrap();
            methods.push(format!(
                "{} {method} simplify-stack={} ternary-in-if={}",
                fixture.path.display(),
                profile.simplify,
                profile.ternary
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
) -> String {
    let initial_hidden = cx.class_nodes[owner].hidden_members.clone();
    cx.imports = imports.clone();
    let first = stage(cx, owner, class, initial, &initial_hidden, true);
    cx.class_nodes[owner]
        .hidden_members
        .clone_from(&initial_hidden);
    if first == "rejected=parsing failure!" {
        return first;
    }

    cx.ir = Default::default();
    cx.imports = imports.clone();
    let initial = initial_statement_graph(cx, class, method).unwrap().unwrap();
    let settled = stage(cx, owner, class, initial, &initial_hidden, false);
    format!("{first}\t{settled}")
}

fn stage(
    cx: &mut Cx,
    owner: ClassNodeId,
    class: &StructClass,
    initial: InitialMethod,
    initial_hidden: &FxHashSet<String>,
    first: bool,
) -> String {
    let result = catch_unwind(AssertUnwindSafe(|| {
        let structured = initial.structure(cx)?;
        let mut method = structured
            .recover_finally(cx, class)?
            .into_expressions(cx, class)?;
        if first {
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
        } else {
            method.simplify_stack_vars(cx, class);
        }
        let tree = structure_snapshot(cx, method.root, &method.flow.counters);
        let hidden = &cx.class_nodes[owner].hidden_members;
        let all_members = hidden_members(hidden.iter());
        let added = hidden_members(hidden.difference(initial_hidden));
        let expressions = expression_snapshot::snapshot(cx, method.root, &method.flow.counters);
        Ok::<_, io::Error>(format!(
            "{tree};hidden={all_members};hidden-added={added}\t{expressions}"
        ))
    }));
    match result {
        Ok(Ok(snapshot)) => snapshot,
        Ok(Err(error))
            if error.kind() == io::ErrorKind::InvalidData
                && error.to_string() == "parsing failure!" =>
        {
            "rejected=parsing failure!".into()
        }
        Ok(Err(error)) => format!("stack-error={}", one_line(&error.to_string())),
        Err(error) => format!("stack-panic={}", panic_text(&*error)),
    }
}

fn hidden_members<'a>(members: impl Iterator<Item = &'a String>) -> String {
    members
        .sorted_unstable_by(|left, right| left.encode_utf16().cmp(right.encode_utf16()))
        .map(|member| expression_snapshot::text(Some(member)))
        .join(",")
}
