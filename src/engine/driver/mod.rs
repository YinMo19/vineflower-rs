//! Decompile the own classes in a registered group and write Java source.

mod class_groups;
mod manifest;
mod memory;
mod prepare;
mod runtime;
mod saver;
mod token_dump;

pub use memory::MemorySource;
pub use saver::Output;

use std::{cell::OnceCell, io, path::Path, sync::Arc};

use fancy_regex::Regex;
use rustc_hash::FxHashSet;

use super::class_nodes::{ClassKind, ClassNodeId, load_classes};
use super::class_processor::write_class;
use super::class_wrapper::catch_method_failure;
use super::class_writer::{javadoc::JavadocProvider, write_class_error, write_exception};
use super::context::ClassSession;
use super::context_source::{ContextSource, OutputLayout};
use super::{Cx, Options};
use crate::renamer::{ConverterHelper, IdentifierRenamer, rename, rename_inner_class};
use crate::structs::{StructClass, StructContext, context_unit::ContextUnit};
use crate::util::text_buffer::TextBuffer;

/// One Java compilation unit produced from an own source.
#[derive(Debug)]
pub struct DecompiledClass {
    pub qualified_name: String,
    /// Source output path. Standalone class inputs use their simple file name.
    pub entry_name: String,
    pub source: String,
    /// Alternating original and generated source line numbers, both one-based.
    /// Present when bytecode source mapping is requested.
    pub mapping: Option<Vec<i32>>,
}

/// Inputs in the same session share hierarchy lookups and nested-class discovery.
/// Sources produce output. Libraries participate only in lookups.
pub struct Decompiler {
    context: StructContext,
    include: ClassFilter,
    whitelist: Vec<String>,
    javadoc: Option<Arc<dyn JavadocProvider>>,
    identifier_renamer: Option<Box<dyn IdentifierRenamer>>,
}

impl Decompiler {
    pub fn new(options: Options) -> io::Result<Self> {
        let include = ClassFilter::new(&options)?;
        let options = Arc::new(options);
        let mut context = StructContext::new(Arc::clone(&options), None);
        runtime::register(&mut context, &options)?;
        Ok(Self {
            context,
            include,
            whitelist: Vec::new(),
            javadoc: None,
            identifier_renamer: None,
        })
    }

    pub fn add_source(&mut self, path: impl AsRef<Path>) -> io::Result<()> {
        self.context.add_file(path.as_ref(), true)
    }

    pub fn add_library(&mut self, path: impl AsRef<Path>) -> io::Result<()> {
        self.context.add_file(path.as_ref(), false)
    }

    pub fn add_source_context(&mut self, source: Arc<dyn ContextSource>) -> io::Result<()> {
        self.context.try_add_space(source, true)
    }

    pub fn add_library_context(&mut self, library: Arc<dyn ContextSource>) -> io::Result<()> {
        self.context.try_add_space(library, false)
    }

    pub fn add_whitelist(&mut self, prefix: impl Into<String>) {
        self.whitelist.push(prefix.into());
    }

    pub fn set_javadoc(&mut self, provider: Arc<dyn JavadocProvider>) {
        self.javadoc = Some(provider);
    }

    /// Install a native identifier renamer for sessions with rename-members enabled.
    pub fn set_identifier_renamer(&mut self, renamer: Box<dyn IdentifierRenamer>) {
        self.identifier_renamer = Some(renamer);
    }

    pub fn decompile(self) -> io::Result<Vec<DecompiledClass>> {
        self.run(None)
    }

    /// Save each own unit in input order, including its non-class resources.
    pub fn save(self, output: Output) -> io::Result<()> {
        self.run(Some(output)).map(|_| ())
    }

    fn run(mut self, output: Option<Output>) -> io::Result<Vec<DecompiledClass>> {
        let options = Arc::clone(self.context.options());
        for entry in self
            .context
            .get_units()
            .iter()
            .filter(|unit| unit.own)
            .flat_map(|unit| &unit.class_entries)
        {
            if self.context.get_class(entry).is_none() {
                return Err(io::Error::new(
                    io::ErrorKind::InvalidData,
                    format!("Could not find class {entry}"),
                ));
            }
        }
        let mut helper = ConverterHelper::default();
        let renamer = if options.rename_members {
            if self.identifier_renamer.is_none()
                && let Some(name) = &options.user_renamer_class
            {
                log::warn!("Cannot load renamer '{name}'");
            }
            let renamer = self
                .identifier_renamer
                .as_deref_mut()
                .unwrap_or(&mut helper as &mut dyn IdentifierRenamer);
            rename(&mut self.context, renamer)?;
            Some(renamer)
        } else {
            None
        };
        let nodes = load_classes(
            &self.context,
            &options,
            |name| self.include.matches(name),
            |name| whitelisted(&self.whitelist, name),
            {
                let mut renamer = renamer;
                move |name, simple| {
                    renamer
                        .as_deref_mut()
                        .and_then(|r| rename_inner_class(r, name, simple))
                }
            },
        );
        let context = Arc::new(self.context);
        let mut cx = Cx::new(Arc::clone(&context));
        cx.class_nodes = nodes;
        cx.javadoc = self.javadoc;
        // Driver callers receive source and mappings. Tokens are consumed only by the dump.
        cx.collect_text_tokens = options.dump_text_tokens;

        let mut result = Vec::new();
        let mut reclaim = ReclaimSchedule::default();
        let definitions = OnceCell::new();
        let single_unit = context.get_units().iter().filter(|unit| unit.own).count() == 1;
        for unit in context.get_units().iter().filter(|unit| unit.own) {
            let layout = unit.source.output_layout();
            let mut sink = output
                .as_ref()
                .map(|output| saver::UnitSink::begin(output, unit, &layout, &self.whitelist))
                .transpose()?;

            let mut classes = unit_classes(&mut cx, unit, &layout);
            let mut emit = |class: DecompiledClass| {
                if let Some(sink) = &mut sink {
                    sink.class(&class, options.dump_code_lines)
                } else {
                    result.push(class);
                    Ok(())
                }
            };
            if let Some(plan) = class_groups::plan(&cx, &classes, single_unit)? {
                for (_, class) in class_groups::run(&cx, classes, plan)? {
                    emit(class)?;
                }
            } else {
                let root_session = cx.take_class_session();
                prepare::unit(
                    &mut cx,
                    &mut classes,
                    &mut reclaim,
                    &root_session,
                    &definitions,
                )?;
                render_unit(&mut cx, classes, &mut reclaim, root_session, |_, class| {
                    emit(class)
                })?;
            }
            if let Some(sink) = sink {
                sink.finish()?;
            }
        }
        Ok(result)
    }
}

/// Charge preparation when nodes are allocated and again when the root is
/// retired. This also schedules collections during emission, when a unit can
/// release large method graphs while allocating very little new IR.
#[derive(Default)]
struct ReclaimSchedule {
    retired_bytes: u64,
    next_sweep: u64,
}

impl ReclaimSchedule {
    fn after_root(&mut self, cx: &mut Cx, pending: &[PendingClass], parent: &ClassSession) {
        let work = cx.ir.allocated_bytes() + self.retired_bytes;
        if work >= self.next_sweep {
            let live = cx.reclaim_ir(
                std::iter::once(parent).chain(pending.iter().filter_map(|p| p.session.as_ref())),
            );
            // Amortize the next full traversal over at least its live graph
            // and the class table that owns the wrappers.
            self.next_sweep = work + live + cx.class_nodes.ir_root_scan_bytes();
        }
    }
}

struct PendingClass {
    kotlin: bool,
    prepared_bytes: u64,
    class: Arc<StructClass>,
    entry_name: String,
    node: ClassNodeId,
    session: Option<ClassSession>,
    error: Option<io::Error>,
}

fn unit_classes(cx: &mut Cx, unit: &ContextUnit, layout: &OutputLayout) -> Vec<PendingClass> {
    let mut seen = FxHashSet::default();
    unit.class_entries
        .iter()
        .filter_map(|entry| {
            let class = cx.struct_context.get_class(entry)?;
            let kotlin = crate::kotlin::members::select_language(cx, &class);
            let node = cx.class_nodes.id(&class.qualified_name)?;
            if cx.class_nodes[node].kind != ClassKind::Root {
                return None;
            }
            if !seen.insert(class.qualified_name.clone()) {
                log::error!(
                    "Skipping writing already existing class: {}",
                    class.qualified_name
                );
                return None;
            }
            let mut name = if cx.options.rename_members {
                let simple = basename(&class.qualified_name);
                let prefix = entry.rsplit_once('/').map_or("", |(prefix, _)| prefix);
                if prefix.is_empty() {
                    simple.to_owned()
                } else {
                    format!("{prefix}/{simple}")
                }
            } else {
                entry
                    .rfind(".class")
                    .map_or(entry.as_str(), |suffix| &entry[..suffix])
                    .to_owned()
            };
            if matches!(layout, OutputLayout::SingleFile) {
                name = basename(&name).to_owned();
            }
            name.push_str(if kotlin { ".kt" } else { ".java" });
            Some(PendingClass {
                kotlin,
                prepared_bytes: 0,
                class,
                entry_name: name,
                node,
                session: None,
                error: None,
            })
        })
        .collect()
}

fn render_unit(
    cx: &mut Cx,
    classes: Vec<PendingClass>,
    reclaim: &mut ReclaimSchedule,
    parent: ClassSession,
    mut emit: impl FnMut(usize, DecompiledClass) -> io::Result<()>,
) -> io::Result<()> {
    let mut index = 0;
    let mut classes = classes.into_iter();
    while let Some(pending) = classes.next() {
        reclaim.retired_bytes += pending.prepared_bytes;
        if let Some(class) = render(cx, pending)? {
            emit(index, class)?;
        }
        reclaim.after_root(cx, classes.as_slice(), &parent);
        index += 1;
    }
    cx.restore_class_session(parent);
    Ok(())
}

fn render(cx: &mut Cx, pending: PendingClass) -> io::Result<Option<DecompiledClass>> {
    let PendingClass {
        class,
        entry_name,
        session,
        error,
        ..
    } = pending;
    cx.restore_class_session(session.expect("Class was not preprocessed"));
    let mut buffer = TextBuffer::with_capacity(cx, 16_384);
    let mapping;
    if let Some(error) = error {
        write_exception(cx, &mut buffer, &error);
        mapping = None;
    } else {
        log::info!("Decompiling class {}", class.qualified_name);
        buffer.append(&cx.options.banner);
        let rendered = catch_method_failure(|| {
            write_class(cx, &class, &mut buffer)?;
            if cx.options.dump_text_tokens {
                token_dump::append(cx, &mut buffer);
            }
            Ok(())
        });
        if let Err(error) = rendered {
            if error.kind() == io::ErrorKind::Interrupted {
                return Err(error);
            }
            log::error!(
                "Class {} couldn't be fully decompiled: {error}",
                class.qualified_name
            );
            if !cx.options.dump_exception_on_error {
                return Ok(None);
            }
            buffer = TextBuffer::new(cx);
            write_class_error(cx, &mut buffer, &error);
        }
        mapping = cx
            .options
            .bytecode_source_mapping
            .then(|| cx.source_mapper.original_lines_mapping());
    }
    Ok(Some(DecompiledClass {
        qualified_name: class.qualified_name.to_string(),
        entry_name,
        source: buffer.convert_to_string_and_allow_data_discard(),
        mapping,
    }))
}

fn basename(name: &str) -> &str {
    name.rsplit('/').next().unwrap()
}

fn whitelisted(prefixes: &[String], name: &str) -> bool {
    prefixes.is_empty() || prefixes.iter().any(|prefix| name.starts_with(prefix))
}

struct ClassFilter {
    included: Option<Regex>,
    excluded: Option<Regex>,
}

impl ClassFilter {
    fn new(options: &Options) -> io::Result<Self> {
        fn compile(pattern: &str) -> io::Result<Option<Regex>> {
            if pattern.is_empty() {
                Ok(None)
            } else {
                Regex::new(&format!(r"\A(?:{pattern})\z"))
                    .map(Some)
                    .map_err(|error| io::Error::new(io::ErrorKind::InvalidInput, error))
            }
        }
        Ok(Self {
            included: compile(&options.included_classes)?,
            excluded: compile(&options.excluded_classes)?,
        })
    }

    fn matches(&self, name: &str) -> bool {
        let matches = |pattern: &Regex| match pattern.is_match(name) {
            Ok(equal) => equal,
            Err(error) => {
                log::warn!("Class filter did not match {name}: {error}");
                false
            }
        };
        self.included.as_ref().is_none_or(matches) && !self.excluded.as_ref().is_some_and(matches)
    }
}
