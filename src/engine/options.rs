//! The decompiler preferences of `IFernflowerPreferences` and of the bundled
//! plugins. A field is named after its option key, so `decompile-generics`
//! is `decompile_generics`.

/// The value accepted by a named decompiler preference.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PreferenceKind {
    Bool,
    Integer,
    Text,
}

/// Metadata for a preference accepted by [`Options::set`].
#[derive(Clone, Copy, Debug)]
pub struct PreferenceSpec {
    /// Long preference name without leading dashes.
    pub name: &'static str,
    /// Legacy short name, such as `thr` for `thread-count`.
    pub alias: Option<&'static str>,
    /// Description shared with the corresponding [`Options`] field.
    pub help: &'static str,
    /// Value type used by the native engine.
    pub kind: PreferenceKind,
    /// Default for display, including a description for a runtime-dependent value.
    pub default_help: Option<&'static str>,
}

/// A preference value as it appears in upstream's string-typed property map.
trait Preference: Sized {
    const KIND: PreferenceKind;
    fn parse(value: &str) -> Self;
}

/// Accept the upstream `"1"` flag value and its textual `"true"` equivalent.
impl Preference for bool {
    const KIND: PreferenceKind = PreferenceKind::Bool;

    fn parse(value: &str) -> Self {
        matches!(value, "1" | "true")
    }
}

/// `DecompilerContext.getIntOption`: an unreadable number is zero.
impl Preference for i32 {
    const KIND: PreferenceKind = PreferenceKind::Integer;

    fn parse(value: &str) -> Self {
        value.parse().unwrap_or(0)
    }
}

impl Preference for String {
    const KIND: PreferenceKind = PreferenceKind::Text;

    fn parse(value: &str) -> Self {
        value.to_owned()
    }
}

impl Preference for Option<String> {
    const KIND: PreferenceKind = PreferenceKind::Text;

    fn parse(value: &str) -> Self {
        Some(value.to_owned())
    }
}

macro_rules! preferences {
    (@alias) => { None };
    (@alias $short:literal) => { Some($short) };
    (@value auto) => { available_processors() };
    (@value None) => { None::<String> };
    (@value $value:literal) => { $value };
    (@help auto) => { Some("available processors") };
    (@help None) => { None };
    (@help $value:literal) => { Some(concat!($value)) };
    ($( #[doc = $doc:literal] $field:ident: $ty:ty = $default:tt, $key:literal $(| $short:literal)?; )*) => {
        /// All named preferences in declaration order, including internal test settings.
        pub const PREFERENCES: &[PreferenceSpec] = &[
            $( PreferenceSpec {
                name: $key,
                alias: preferences!(@alias $($short)?),
                help: $doc.trim_ascii_start(),
                kind: <$ty as Preference>::KIND,
                default_help: preferences!(@help $default),
            }, )*
        ];

        /// Settings of one decompilation session.
        #[derive(Clone)]
        #[non_exhaustive]
        pub struct Options {
            $( #[doc = $doc] pub $field: $ty, )*
            /// Whether the Kotlin plugin is installed.
            pub decompile_kotlin: bool,
            /// Whether the IDEA `@NotNull` plugin is installed.
            pub idea_notnull: bool,
        }

        impl Default for Options {
            fn default() -> Self {
                Self {
                    $( $field: preferences!(@value $default).into(), )*
                    decompile_kotlin: false,
                    idea_notnull: false,
                }
            }
        }

        impl Options {
            /// Sets a preference by its long or short name. Returns false for
            /// a name no preference answers to.
            pub fn set(&mut self, name: &str, value: &str) -> bool {
                match name {
                    $( $key $(| $short)? => self.$field = Preference::parse(value), )*
                    _ => return false,
                }
                true
            }
        }
    };
}

preferences! {
    /// Omit compiler-generated bridge methods.
    remove_bridge: bool = true, "remove-bridge" | "rbr";
    /// Omit fields and methods marked synthetic.
    remove_synthetic: bool = true, "remove-synthetic" | "rsy";
    /// Recover nested classes inside their enclosing classes.
    decompile_inner: bool = true, "decompile-inner" | "din";
    /// Recover class literals from the synthetic code emitted by Java 1–4 compilers.
    decompile_java4: bool = true, "decompile-java4" | "dc4";
    /// Recover Java assert statements.
    decompile_assert: bool = true, "decompile-assert" | "das";
    /// Hide no-argument super() calls in constructors.
    hide_empty_super: bool = true, "hide-empty-super" | "hes";
    /// Hide empty default constructors.
    hide_default_constructor: bool = true, "hide-default-constructor" | "hdc";
    /// Use generic signatures for classes, fields, methods, and variables.
    decompile_generics: bool = true, "decompile-generics" | "dgs";
    /// Fold temporary return values into returns in try/catch blocks.
    incorporate_returns: bool = true, "incorporate-returns" | "ner";
    /// Recover synchronized blocks with a missing monitor exit.
    ensure_synchronized_monitors: bool = true, "ensure-synchronized-monitors" | "esm";
    /// Recover enum declarations and constants.
    decompile_enums: bool = true, "decompile-enums" | "den";
    /// Accept the upstream preview-feature preference. The native engine detects features from bytecode versions.
    decompile_preview: bool = true, "decompile-preview" | "dpr";
    /// Remove synthetic getClass() checks around inner class construction.
    remove_getclass: bool = true, "remove-getclass" | "rgn";
    /// Keep numeric literals in place of named constants such as Math.PI.
    keep_literals: bool = false, "keep-literals" | "lit";
    /// Treat integer constants 0 and 1 as possible boolean values.
    boolean_as_int: bool = true, "boolean-as-int" | "bto";
    /// Escape non-ASCII characters in string and character literals.
    ascii_strings: bool = false, "ascii-strings" | "asc";
    /// Recognize compiler-generated constructs even when the synthetic flag is missing.
    synthetic_not_set: bool = false, "synthetic-not-set" | "nns";
    /// Render an undefined reference type as java.lang.Object.
    undefined_as_object: bool = true, "undefined-as-object" | "uto";
    /// Use local variable and parameter names from the LocalVariableTable attribute.
    use_lvt_names: bool = true, "use-lvt-names" | "udv";
    /// Use parameter names from the MethodParameters attribute.
    use_method_parameters: bool = true, "use-method-parameters" | "ump";
    /// Remove empty protected ranges from the exception table.
    remove_empty_try_catch: bool = true, "remove-empty-try-catch" | "rer";
    /// Recover finally blocks by identifying copies of their cleanup code.
    decompile_finally: bool = true, "decompile-finally" | "fdi";
    /// Write lambda expressions as anonymous classes.
    lambda_to_anonymous_class: bool = false, "lambda-to-anonymous-class" | "lac";
    /// Generate line mappings between the original and decompiled source.
    bytecode_source_mapping: bool = false, "bytecode-source-mapping" | "bsm";
    /// Store available line mappings in each source entry's ZIP extra data.
    dump_code_lines: bool = false, "dump-code-lines" | "dcl";
    /// Tolerate missing constructor declarations when resolving synthetic arguments.
    ignore_invalid_bytecode: bool = false, "ignore-invalid-bytecode" | "iib";
    /// Check the superclass, interfaces, and enclosing method of anonymous class candidates.
    verify_anonymous_classes: bool = false, "verify-anonymous-classes" | "vac";
    /// Simplify ternary expressions with boolean constant branches.
    ternary_constant_simplification: bool = false, "ternary-constant-simplification" | "tcs";
    /// Recover patterns in instanceof checks and switch statements.
    pattern_matching: bool = true, "pattern-matching" | "pam";
    /// Repair control flow for try blocks nested in loops.
    try_loop_fix: bool = true, "try-loop-fix" | "tlf";
    /// Collapse eligible if statements with a ternary condition.
    ternary_in_if: bool = true, "ternary-in-if" | "tco";
    /// Recover switch expressions and their yield values.
    decompile_switch_expressions: bool = true, "decompile-switch-expressions" | "swe";
    /// Show normally hidden statements for debugging.
    show_hidden_statements: bool = false, "show-hidden-statements" | "shs";
    /// Add @Override to methods that override a known superclass or interface method.
    override_annotation: bool = true, "override-annotation" | "ovr";
    /// Run additional stack-variable simplification across statement boundaries.
    simplify_stack: bool = true, "simplify-stack" | "ssp";
    /// Apply extra checks before merging local variables.
    verify_merges: bool = false, "verify-merges" | "vvm";
    /// Compare variable references before and after merging locals.
    verify_pre_post_merges: bool = false, "verify-pre-post-merges" | "pvm";
    /// Use the older exception-range repair that inserts dummy exception handlers.
    old_try_dedup: bool = false, "old-try-dedup";
    /// Load class files and JARs from CLASSPATH along with the host Java runtime.
    include_classpath: bool = false, "include-classpath" | "iec";
    /// Select a JDK for type lookup. Use 1 or current for the host JDK, 0 to skip it, or a JDK path.
    include_runtime: String = "1", "include-runtime" | "jrt";
    /// Write explicit generic type arguments on method calls when available.
    explicit_generics: bool = false, "explicit-generics" | "ega";
    /// Omit braces around single-expression lambda bodies.
    inline_simple_lambdas: bool = true, "inline-simple-lambdas" | "isl";
    /// Set the CLI log level to TRACE, INFO, WARN, or ERROR.
    log_level: String = "INFO", "log-level" | "log";
    /// Limit processing time per method in seconds. Zero disables the timeout.
    max_time_per_method: i32 = 0, "max-time-per-method" | "mpm";
    /// Rename eligible classes, fields, and methods during deobfuscation.
    rename_members: bool = false, "rename-members" | "ren";
    /// Accept an upstream Java renamer class name. Native custom renamers use Decompiler::set_identifier_renamer.
    user_renamer_class: Option<String> = None, "user-renamer-class" | "urc";
    /// Use LF line endings when enabled and CRLF when disabled.
    new_line_separator: bool = true, "new-line-separator" | "nls";
    /// Set the text inserted for each indentation level.
    indent_string: String = "   ", "indent-string" | "ind";
    /// Set the preferred line width for wrapping source.
    preferred_line_length: i32 = 160, "preferred-line-length" | "pll";
    /// Prepend this text to each generated compilation unit.
    banner: String = "", "banner" | "ban";
    /// Set the message written alongside decompilation errors.
    error_message: String = "Please report this to the Vineflower issue tracker, at https://github.com/Vineflower/vineflower/issues with a copy of the class file (if you have the rights to distribute it!)", "error-message" | "erm";
    /// Set the number of worker threads. Use 1 for sequential processing or any nonpositive value for automatic selection.
    thread_count: i32 = auto, "thread-count" | "thr";
    /// Annotate generated source with original line numbers when mappings are enabled.
    dump_original_lines: bool = false, "__dump_original_lines__";
    /// Enable test mapping output and disable method timeouts.
    unit_test_mode: bool = false, "__unit_test_mode__";
    /// Skip copying non-class resources to the destination.
    skip_extra_files: bool = false, "skip-extra-files" | "sef";
    /// Warn about inconsistent InnerClasses attributes.
    warn_inconsistent_inner_attributes: bool = true, "warn-inconsistent-inner-attributes" | "win";
    /// Include bytecode in diagnostics for failed methods.
    dump_bytecode_on_error: bool = true, "dump-bytecode-on-error" | "dbe";
    /// Include error details in the generated method or class when decompilation fails.
    dump_exception_on_error: bool = true, "dump-exception-on-error" | "dee";
    /// Include decompiler comments about unusual bytecode and recovery problems.
    decompiler_comments: bool = true, "decompiler-comments" | "dec";
    /// Include the class file's SourceFile attribute in a source comment.
    sourcefile_comments: bool = false, "sourcefile-comments" | "sfc";
    /// Expand complex dynamic constants into non-lazy expressions marked with a comment.
    decompile_complex_constant_dynamic: bool = false, "decompile-complex-constant-dynamic" | "dcc";
    /// Inline JSR subroutines even in newer class file versions.
    force_jsr_inline: bool = false, "force-jsr-inline" | "fji";
    /// Append the collected text tokens to each generated compilation unit.
    dump_text_tokens: bool = false, "dump-text-tokens" | "dtt";
    /// Omit import declarations from generated source.
    remove_imports: bool = false, "remove-imports" | "rim";
    /// Identify the synthetic JVM members behind lambdas and local or anonymous classes.
    mark_corresponding_synthetics: bool = false, "mark-corresponding-synthetics" | "mcs";
    /// Exclude classes whose full JVM internal name matches this regular expression.
    excluded_classes: String = "", "excluded-classes";
    /// Include only classes whose full JVM internal name matches this regular expression.
    included_classes: String = "", "included-classes";
    /// Check the enclosing-class prefix in nested class names before attaching them.
    validate_inner_classes_names: bool = true, "validate-inner-classes-names";
    /// Restructure if statements for readability.
    prettify_ifs: bool = true, "prettify-ifs";
    /// Select one method by JVM name and descriptor, optionally qualified by its owner, as in pkg/Foo.run()V.
    method_to_decompile: String = "", "method-to-decompile";

    // Kotlin plugin
    /// Write explicit public visibility in Kotlin declarations.
    kt_show_public: bool = true, "kt-show-public";
    /// Write Kotlin source for recognized Kotlin classes when the Kotlin plugin is installed.
    kt_enable: bool = true, "kt-enable";
    /// Set the placeholder for unknown Kotlin default arguments. An empty string omits the placeholder.
    kt_unknown_defaults: String = "...", "kt-unknown-defaults";
    /// Recover Kotlin string templates from string concatenations.
    kt_collapse_string_concat: bool = true, "kt-collapse-string-concat";
    /// Parse Kotlin metadata even when Kotlin source generation is disabled.
    kt_export_metadata: bool = false, "kt-export-metadata";
    /// Write wrapper functions for Kotlin multifile facade classes.
    kt_decompile_facades: bool = false, "kt-decompile-facades";

    // Variable renaming plugin
    /// Choose the local variable naming scheme. Built-in schemes are jad and tiny.
    variable_renaming: Option<String> = None, "variable-renaming";
    /// Apply the selected local variable naming scheme to method parameters.
    rename_parameters: bool = false, "rename-parameters";
    /// Select JAD-style local variable names when no other scheme is set. Deprecated.
    jad_style_variable_naming: bool = false, "jad-style-variable-naming" | "jvn";
    /// Apply JAD-style names to parameters when the JAD scheme is active. Deprecated.
    jad_style_parameter_naming: bool = false, "jad-style-parameter-naming" | "jpr";

    // IDEA @NotNull plugin
    /// Remove checks inserted by IntelliJ IDEA for @NotNull parameters and return values.
    resugar_idea_notnull: bool = true, "resugar-idea-notnull" | "inn";
}

fn available_processors() -> i32 {
    std::thread::available_parallelism().map_or(1, |count| count.get() as i32)
}

impl Options {
    /// ClassWrapper times methods with code outside unit test mode.
    pub(super) fn method_time_limit(&self) -> Option<i32> {
        (self.max_time_per_method != 0 && !self.unit_test_mode).then_some(self.max_time_per_method)
    }

    /// ContextUnit uses the processor count for a non-positive preference.
    pub(super) fn worker_count(&self) -> usize {
        if self.thread_count > 0 {
            self.thread_count as usize
        } else {
            available_processors() as usize
        }
    }

    /// `DecompilerContext.getNewLineSeparator`.
    pub fn line_separator(&self) -> &'static str {
        if self.new_line_separator { "\n" } else { "\r\n" }
    }
}
