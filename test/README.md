# Upstream fixture parity

`upstream/` is a byte-preserving copy of the tracked core and plugin `testData` trees from Vineflower `b8273988af850e8cfb234ca08d129058502b032f`: 1,336 core and 154 plugin fixtures, plus the upstream Apache-2.0 license. `registrations.tsv` ports 688 active single-class registrations and their effective fixture settings. The parity target also runs the two bulk cases, six CLI file/directory/archive cases, and the lazy-library case. The upstream disabled archive cases and unconfigured external debug test are not active registrations.

From `vineflower-rs/`:

```sh
cargo test --test upstream_parity                                      # original source/CLI/bulk goldens, no JDK
cargo test --test upstream_parity full_parity -- --ignored --nocapture   # all 697 active cases
```

Parity fails on any missing JDK, missing fixture, unsupported capability, source/output mismatch or execution error. Each is reported separately. `VINEFLOWER_RS_PARITY_FILTER` optionally selects a substring of case IDs, such as `core/LVT` or `cli/`. No golden gets created or rewritten. Comparison uses only upstream's newline and outer whitespace normalization, with the three upstream alternate goldens explicitly allowed. Upstream's failable rename case remains a failure on mismatch.

### Compiled inputs

`upstream/` and `registrations.tsv` define the original black-box suite.
`smoke/` holds precompiled upstream inputs for the JDK-free subset.
`cargo test` runs that subset by default; there are no Rust unit tests
or separate self-authored regression targets.

Checked-in class files are used unchanged. For registered Java source groups, set `VINEFLOWER_JDK_8`, `VINEFLOWER_JDK_9`, `VINEFLOWER_JDK_11`, `VINEFLOWER_JDK_16`, `VINEFLOWER_JDK_17`, `VINEFLOWER_JDK_21` and `VINEFLOWER_JDK_25` to the corresponding JDK homes. Set only the JDKs needed for a focused run. The harness validates the JDK major and runs its `javac` once per source group in a temporary directory, with UTF-8, debug info (except `NoDebug`) and preview flags matching the upstream Gradle configuration. A newer `javac --release` is not a substitute. Runtime-backed registrations require their indicated JDK even with prebuilt classes.

Alternatively, set `VINEFLOWER_RS_CLASS_ROOT` to a tree with the upstream layout: `testData/classes/<group>/` and `plugins/<plugin>/testData/classes/<group>/`. From the matching upstream checkout, the recipe for prebuilt fixture classes is:

```sh
./gradlew :testDataClasses :kotlin:testDataClasses :variable-renaming:testDataClasses
```

Point `VINEFLOWER_RS_CLASS_ROOT` at that checkout. Prebuilt outputs are also needed for Jasm, Kotlin (including `ktold` with upstream's old compiler flags), Groovy and Scala. The Scala plugin is not an included Gradle project at this upstream revision; its plugin classes must be built separately using its `testDataClasses` task from a checkout with that plugin enabled. These tasks only prepare inputs; parity testing never invokes the Java decompiler.

### Native scope

The Rust runtime does not require a JVM. `cargo run -- input.class` writes source
to stdout; supplying an output directory or archive writes the recovered
compilation units and resources. Use `cargo run -- --help` for options.
Library callers can use `vineflower_rs::decompile(bytes, &Options::default())`
or register companion and library inputs in a `ClassGroupBuilder`.
`ClassPath` accepts directories, archives, JDK images and lazy providers.
Use `--ignore-invalid-bytecode` (`-iib=1`) only for legacy inputs: it currently
accepts underreported stack bounds, proven misowned ECJ constructor bridges
and handler-free void method tails missing their final return. Unsupported
repairs still produce an error.

The implementation separates class-file decoding, JVM instructions, CFG
analysis, operand-stack lifting, region recovery, and source rendering.
Modules with submodules use `src/<module>/mod.rs`; leaf modules stay in
single files.
Native passes recover stack/local joins, exception regions, declared member
classes, typed lambdas and selected dynamic constants. Kotlin reconstruction
and Java compiler idiom recovery are incomplete; a parseable input can still
produce an explicit unsupported error or source that differs from upstream.

Exact upstream comparison with all fixture bytecode and required JDKs:

| Snapshot | Exact | Unsupported | Different | Missing or execution errors |
| --- | ---: | ---: | ---: | ---: |
| Initial native pipeline | 37 | 537 | 123 | 0 |
| Class groups and structured recovery | 73 | 254 | 370 | 0 |
| Assertions, switch dispatch and array literals | 85 | 227 | 385 | 0 |
| Width-aware source documents and switch expressions | 93 | 227 | 377 | 0 |
| Allocation and stack-bookkeeping source maps | 100 | 227 | 370 | 0 |
| Kotlin when and single-pass JVM pattern switches | 101 | 221 | 375 | 0 |
| Java loops, lexical captures, resource returns and text tokens | 105 | 211 | 381 | 0 |
| Qualified construction, scoped switches and nested resources | 108 | 206 | 383 | 0 |
| Typed assignments, contextual boxing and opt-in source rewrites | 114 | 191 | 392 | 0 |
| Guarded patterns, local joins, post-test loops and anonymous SAMs | 120 | 161 | 416 | 0 |
| Record patterns, resource exits and Kotlin template/member recovery | 124 | 149 | 423 | 1 |
| Instance initializer maps, float literals and optional method signatures | 126 | 149 | 422 | 0 |
| Grouped binary layout and Java UTF-16 literal escaping | 127 | 149 | 421 | 0 |
| Generic local types, assignment widening and Java preview templates | 129 | 146 | 422 | 0 |
| Constructor argument patterns, record `instanceof`, nested resource returns and Kotlin extensions | 129 | 140 | 428 | 0 |
| Boolean layout, compact records, nested monitors/resources and typed calls | 135 | 131 | 431 | 0 |
| Nested record and nullable recovery, proven varargs, switch source maps | 138 | 127 | 432 | 0 |
| Legacy bytecode recovery, subword calls, protected foreach, Kotlin tail calls and preview guards | 138 | 117 | 442 | 0 |
| Primitive class literals, enum/switch edge maps, predicate loops, array assignments and Kotlin infix | 146 | 113 | 438 | 0 |
| Typed preview switches, mirrored loop cleanup, constructor joins, nested classes, and Kotlin locals | 147 | 105 | 445 | 0 |
| Labeled `finally`, array mappings, local classes, string switches, Scala bridges and Kotlin spread | 154 | 100 | 443 | 0 |
| Shared loop headers and compound `finally`, Kotlin sealed class groups, short-circuit local joins | 154 | 98 | 445 | 0 |
| Typed catch loop retries and enum switch arguments | 154 | 95 | 448 | 0 |
| Nested switch exits, multi-entry loops, Groovy checked dispatch and Kotlin suspend closures | 154 | 93 | 450 | 0 |
| Nested finally, Java 25 anonymous classes, Scala boolean joins, and Kotlin constructor delegation | 154 | 88 | 455 | 0 |

All eight upstream CLI and bulk cases match. The full test remains failing
until all 697 comparisons match.

The runner preserves explicit companions, discovers sibling `$*.class` files
and resolves Kotlin file facades. It installs the upstream fixture's selected
plugins and runtime classpath where applicable, and checks the lazy-library
case against the native provider callback. Fixture diagnostics and validation
flags that do not affect source generation are handled separately from source
options. Archive comparisons check entry names and contents, not container
serialization or timestamps.
