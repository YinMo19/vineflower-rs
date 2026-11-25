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
use vineflower_rs::decompiler::sforms::split_ssa;
use vineflower_rs::decompiler::stack::simplify_statement;
use vineflower_rs::decompiler::vars::versions::{FinalType, VarVersions};
use vineflower_rs::engine::class_nodes::{ClassNodeId, load_classes};
use vineflower_rs::engine::class_processor::prepare_class;
use vineflower_rs::engine::import_collector::ImportCollector;
use vineflower_rs::engine::method_processor::{InitialMethod, initial_statement_graph};
use vineflower_rs::engine::{Cx, Options};
use vineflower_rs::structs::single_file_context_source::SingleFileContextSource;
use vineflower_rs::structs::{StructClass, StructContext, StructMethod};

use super::upstream_reference::Corpus;
use super::{
    REFERENCE_HELPERS, compare_snapshots, expression_snapshot, one_line, panic_text, parse_class,
    structure_snapshot, write_cfg, write_count, write_flag, write_int, write_text,
};

#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub(super) enum Check {
    Stack = 3,
    Increments = 4,
}

#[derive(Clone, Copy)]
struct Profile {
    simplify: bool,
    ternary: bool,
    lvt: bool,
    boolean_as_int: bool,
}

const DEFAULT: Profile = Profile {
    simplify: true,
    ternary: true,
    lvt: true,
    boolean_as_int: true,
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

impl Check {
    fn profiles(self) -> &'static [Profile] {
        match self {
            Self::Stack => STACK_PROFILES,
            Self::Increments => INCREMENT_PROFILES,
        }
    }

    fn stages(self) -> &'static [(&'static str, &'static str)] {
        match self {
            Self::Stack => STACK_STAGES,
            Self::Increments => INCREMENT_STAGES,
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::Stack => "stack",
            Self::Increments => "increments",
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
    let groups = class_groups(corpus);
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
        } else if let Err(diff) = compare_snapshots(java, &rust, check.stages()) {
            errors.push(format!("{method}\n  {diff}"));
        } else {
            let stage_size = check.stages().len() / 2;
            for (tree, changes) in rust
                .split('\t')
                .step_by(stage_size)
                .zip(&mut hidden_changes)
            {
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
    eprintln!(
        "{} exact first and settled {} snapshots and {rejected} matching rejections across {} class files",
        methods.len() - rejected,
        check.name(),
        corpus.classes.len()
    );
    let [first, settled] = hidden_changes;
    eprintln!("{first} first simplifications and {settled} settled runs added hidden members");
    if check == Check::Increments {
        eprintln!(
            "{repeats} first passes scheduled another iteration, with {changed_original} changed original variable maps"
        );
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
) {
    let mut options = Options::default();
    options.simplify_stack = profile.simplify;
    options.ternary_in_if = profile.ternary;
    options.use_lvt_names = profile.lvt;
    options.boolean_as_int = profile.boolean_as_int;
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
            write_flag(input, profile.boolean_as_int).unwrap();
            write_text(input, &fixture.name).unwrap();
            write_cfg(input, &cx.ir, &initial.flow.graph).unwrap();

            let snapshot = match imports {
                Ok(imports) => describe(&mut cx, id, &class, method, initial, imports, check),
                Err(error) => format!("class-rejected={}", one_line(error)),
            };
            writeln!(snapshots, "{snapshot}").unwrap();
            methods.push(format!(
                "{} {method} simplify-stack={} ternary-in-if={} lvt={} boolean-as-int={}",
                fixture.path.display(),
                profile.simplify,
                profile.ternary,
                profile.lvt,
                profile.boolean_as_int
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
    if first == "rejected=parsing failure!" {
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
        if check == Check::Increments {
            if first {
                method.simplify_stack_vars(cx, class);
                operation.set("set-var-versions");
                method.set_var_versions(cx, class)?;
            } else {
                operation.set("process-increments");
                method.process_increments(cx, class)?;
            }
        } else if first {
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
        operation.set("snapshot");
        let tree = structure_snapshot(cx, method.root, &method.flow.counters);
        let hidden = &cx.class_nodes[owner].hidden_members;
        let all_members = hidden_members(hidden.iter());
        let added = hidden_members(hidden.difference(initial_hidden));
        let expressions = expression_snapshot::snapshot(cx, method.root, &method.flow.counters);
        let mut snapshot =
            format!("{tree};hidden={all_members};hidden-added={added}\t{expressions}");
        if check == Check::Increments {
            let versions = variable_snapshot(&cx.ir[method.flow.variables]);
            write!(snapshot, "\t{versions}").unwrap();
            if first {
                operation.set("find-increments");
                write!(snapshot, ";repeat={}", method.find_increments(cx)).unwrap();
            }
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

fn stage_error(check: Check, operation: &str, kind: &str, message: &str) -> String {
    if check == Check::Increments {
        format!("increments-{operation}-{kind}={message}")
    } else {
        format!("stack-{kind}={message}")
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
