// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! The decompiler preferences of `IFernflowerPreferences` and of the bundled
//! plugins. A field is named after its option key, so `decompile-generics`
//! is `decompile_generics`.

/// A preference value as it appears in upstream's string-typed property map.
trait Preference: Sized {
    fn parse(value: &str) -> Self;
}

/// `DecompilerContext.getOption`: only `"1"` enables a flag. The command line
/// has already rewritten `true` and `false`.
impl Preference for bool {
    fn parse(value: &str) -> Self {
        matches!(value, "1" | "true")
    }
}

/// `DecompilerContext.getIntOption`: an unreadable number is zero.
impl Preference for i32 {
    fn parse(value: &str) -> Self {
        value.parse().unwrap_or(0)
    }
}

impl Preference for String {
    fn parse(value: &str) -> Self {
        value.to_owned()
    }
}

impl Preference for Option<String> {
    fn parse(value: &str) -> Self {
        Some(value.to_owned())
    }
}

macro_rules! preferences {
    ($( $(#[$doc:meta])* $field:ident: $ty:ty = $default:expr, $key:literal $(| $short:literal)?; )*) => {
        /// Settings of one decompilation session.
        #[derive(Clone)]
        #[non_exhaustive]
        pub struct Options {
            $( $(#[$doc])* pub $field: $ty, )*
            /// Whether the Kotlin plugin is installed.
            pub decompile_kotlin: bool,
            /// Whether the IDEA `@NotNull` plugin is installed.
            pub idea_notnull: bool,
        }

        impl Default for Options {
            fn default() -> Self {
                Self {
                    $( $field: $default.into(), )*
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
    remove_bridge: bool = true, "remove-bridge" | "rbr";
    remove_synthetic: bool = true, "remove-synthetic" | "rsy";
    decompile_inner: bool = true, "decompile-inner" | "din";
    decompile_java4: bool = true, "decompile-java4" | "dc4";
    decompile_assert: bool = true, "decompile-assert" | "das";
    hide_empty_super: bool = true, "hide-empty-super" | "hes";
    hide_default_constructor: bool = true, "hide-default-constructor" | "hdc";
    decompile_generics: bool = true, "decompile-generics" | "dgs";
    incorporate_returns: bool = true, "incorporate-returns" | "ner";
    ensure_synchronized_monitors: bool = true, "ensure-synchronized-monitors" | "esm";
    decompile_enums: bool = true, "decompile-enums" | "den";
    decompile_preview: bool = true, "decompile-preview" | "dpr";
    remove_getclass: bool = true, "remove-getclass" | "rgn";
    keep_literals: bool = false, "keep-literals" | "lit";
    boolean_as_int: bool = true, "boolean-as-int" | "bto";
    ascii_strings: bool = false, "ascii-strings" | "asc";
    synthetic_not_set: bool = false, "synthetic-not-set" | "nns";
    undefined_as_object: bool = true, "undefined-as-object" | "uto";
    use_lvt_names: bool = true, "use-lvt-names" | "udv";
    use_method_parameters: bool = true, "use-method-parameters" | "ump";
    remove_empty_try_catch: bool = true, "remove-empty-try-catch" | "rer";
    decompile_finally: bool = true, "decompile-finally" | "fdi";
    lambda_to_anonymous_class: bool = false, "lambda-to-anonymous-class" | "lac";
    bytecode_source_mapping: bool = false, "bytecode-source-mapping" | "bsm";
    dump_code_lines: bool = false, "dump-code-lines" | "dcl";
    ignore_invalid_bytecode: bool = false, "ignore-invalid-bytecode" | "iib";
    verify_anonymous_classes: bool = false, "verify-anonymous-classes" | "vac";
    ternary_constant_simplification: bool = false, "ternary-constant-simplification" | "tcs";
    pattern_matching: bool = true, "pattern-matching" | "pam";
    try_loop_fix: bool = true, "try-loop-fix" | "tlf";
    ternary_in_if: bool = true, "ternary-in-if" | "tco";
    decompile_switch_expressions: bool = true, "decompile-switch-expressions" | "swe";
    show_hidden_statements: bool = false, "show-hidden-statements" | "shs";
    override_annotation: bool = true, "override-annotation" | "ovr";
    simplify_stack: bool = true, "simplify-stack" | "ssp";
    verify_merges: bool = false, "verify-merges" | "vvm";
    verify_pre_post_merges: bool = false, "verify-pre-post-merges" | "pvm";
    old_try_dedup: bool = false, "old-try-dedup";
    include_classpath: bool = false, "include-classpath" | "iec";
    include_runtime: String = "1", "include-runtime" | "jrt";
    explicit_generics: bool = false, "explicit-generics" | "ega";
    inline_simple_lambdas: bool = true, "inline-simple-lambdas" | "isl";
    log_level: String = "INFO", "log-level" | "log";
    max_time_per_method: i32 = 0, "max-time-per-method" | "mpm";
    rename_members: bool = false, "rename-members" | "ren";
    user_renamer_class: Option<String> = None::<String>, "user-renamer-class" | "urc";
    new_line_separator: bool = true, "new-line-separator" | "nls";
    indent_string: String = "   ", "indent-string" | "ind";
    preferred_line_length: i32 = 160, "preferred-line-length" | "pll";
    banner: String = "", "banner" | "ban";
    error_message: String = "Please report this to the Vineflower issue tracker, at https://github.com/Vineflower/vineflower/issues with a copy of the class file (if you have the rights to distribute it!)", "error-message" | "erm";
    thread_count: i32 = std::thread::available_parallelism().map_or(1, |count| count.get() as i32), "thread-count" | "thr";
    dump_original_lines: bool = false, "__dump_original_lines__";
    unit_test_mode: bool = false, "__unit_test_mode__";
    skip_extra_files: bool = false, "skip-extra-files" | "sef";
    warn_inconsistent_inner_attributes: bool = true, "warn-inconsistent-inner-attributes" | "win";
    dump_bytecode_on_error: bool = true, "dump-bytecode-on-error" | "dbe";
    dump_exception_on_error: bool = true, "dump-exception-on-error" | "dee";
    decompiler_comments: bool = true, "decompiler-comments" | "dec";
    sourcefile_comments: bool = false, "sourcefile-comments" | "sfc";
    decompile_complex_constant_dynamic: bool = false, "decompile-complex-constant-dynamic" | "dcc";
    force_jsr_inline: bool = false, "force-jsr-inline" | "fji";
    dump_text_tokens: bool = false, "dump-text-tokens" | "dtt";
    remove_imports: bool = false, "remove-imports" | "rim";
    mark_corresponding_synthetics: bool = false, "mark-corresponding-synthetics" | "mcs";
    excluded_classes: String = "", "excluded-classes";
    included_classes: String = "", "included-classes";
    validate_inner_classes_names: bool = true, "validate-inner-classes-names";
    prettify_ifs: bool = true, "prettify-ifs";
    method_to_decompile: String = "", "method-to-decompile";

    // Kotlin plugin
    kt_show_public: bool = true, "kt-show-public";
    kt_enable: bool = true, "kt-enable";
    kt_unknown_defaults: String = "...", "kt-unknown-defaults";
    kt_collapse_string_concat: bool = true, "kt-collapse-string-concat";
    kt_export_metadata: bool = false, "kt-export-metadata";
    kt_decompile_facades: bool = false, "kt-decompile-facades";

    // Variable renaming plugin
    variable_renaming: Option<String> = None::<String>, "variable-renaming";
    rename_parameters: bool = false, "rename-parameters";
    jad_style_variable_naming: bool = false, "jad-style-variable-naming" | "jvn";
    jad_style_parameter_naming: bool = false, "jad-style-parameter-naming" | "jpr";

    // IDEA @NotNull plugin
    resugar_idea_notnull: bool = true, "resugar-idea-notnull" | "inn";
}

impl Options {
    /// `DecompilerContext.getNewLineSeparator`.
    pub fn line_separator(&self) -> &'static str {
        if self.new_line_separator { "\n" } else { "\r\n" }
    }
}
