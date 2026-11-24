# Upstream fixture parity

`upstream/` is a byte-preserving copy of the tracked core and plugin `testData` trees from Vineflower `b8273988af850e8cfb234ca08d129058502b032f`: 1,336 core and 154 plugin fixtures, plus the upstream Apache-2.0 license. `registrations.tsv` ports 688 active single-class registrations and their effective fixture settings. The parity target also runs the two bulk cases, six CLI file/directory/archive cases, and the lazy-library case. The upstream disabled archive cases and unconfigured external debug test are not active registrations.

From `vineflower-rs/`:

```sh
cargo test --test upstream_parity                                      # original source/CLI/bulk goldens, no JDK
cargo test --test upstream_parity full_parity -- --ignored --nocapture   # all 697 active cases
```

Parity fails on any missing JDK, missing fixture, unsupported capability, source/output mismatch or execution error. Each is reported separately. `VINEFLOWER_RS_PARITY_FILTER` optionally selects a substring of case IDs, such as `core/LVT` or `cli/`. No golden gets created or rewritten. Comparison uses only upstream's newline and outer whitespace normalization, with the three upstream alternate goldens explicitly allowed. Upstream's failable rename case remains a failure on mismatch.

### Compiled inputs

`smoke/` contains class files compiled from the corresponding upstream Java 8,
Java 16 and Jasm inputs with the upstream `testDataClasses` task. The default
test target compares their emitted source (including source maps where used)
against the unchanged goldens, then exercises all six CLI and both bulk cases
with the checked-in archives.

Checked-in class files are used unchanged. For registered Java source groups, set `VINEFLOWER_JDK_8`, `VINEFLOWER_JDK_9`, `VINEFLOWER_JDK_11`, `VINEFLOWER_JDK_16`, `VINEFLOWER_JDK_17`, `VINEFLOWER_JDK_21` and `VINEFLOWER_JDK_25` to the corresponding JDK homes. Set only the JDKs needed for a focused run. The harness validates the JDK major and runs its `javac` once per source group in a temporary directory, with UTF-8, debug info (except `NoDebug`) and preview flags matching the upstream Gradle configuration. A newer `javac --release` is not a substitute. Runtime-backed registrations require their indicated JDK even with prebuilt classes.

Alternatively, set `VINEFLOWER_RS_CLASS_ROOT` to a tree with the upstream layout: `testData/classes/<group>/` and `plugins/<plugin>/testData/classes/<group>/`. From the matching upstream checkout, the recipe for prebuilt fixture classes is:

```sh
./gradlew :testDataClasses :kotlin:testDataClasses :variable-renaming:testDataClasses
```

Point `VINEFLOWER_RS_CLASS_ROOT` at that checkout. Prebuilt outputs are also needed for Jasm, Kotlin (including `ktold` with upstream's old compiler flags), Groovy and Scala. The Scala plugin is not an included Gradle project at this upstream revision; its plugin classes must be built separately using its `testDataClasses` task from a checkout with that plugin enabled. These tasks only prepare inputs; parity testing never invokes the Java decompiler.

### Native scope

The Rust runtime does not require a JVM. `cargo run -- input.class` writes Java
to stdout; `cargo run -- input.jar output-dir` or `cargo run -- input.jar
output.jar` writes Java and resources. Use `cargo run -- --help` for the
supported options. Library callers can use `vineflower_rs::decompile(bytes,
&Options::default())` to obtain the source and optional bytecode line map.

The implementation separates class-file and signature decoding, JVM
instructions, CFG analysis, operand-stack lifting, region recovery, and Java
rendering. Recovery is not yet equivalent to Vineflower: stack/local joins,
complex exception regions, inners and shared classpath context, non-concat
`invokedynamic`, and the language plugins account for many remaining failures.

Baseline with all upstream fixture bytecode and required JDKs available:
37 of 697 cases match, 537 report unsupported behavior, and 123 differ from
the expected source. All eight upstream CLI and bulk cases match.

The manifest preserves explicit companions and registration metadata; the runner also discovers sibling `$*.class` files and resolves Kotlin file facades. Cases that need multiple source classes, plugin rendering, or an active classpath provider are unsupported until those native APIs exist. Fixture diagnostic and validation flags, and a documented set of baseline upstream algorithm settings in `upstream_parity.rs`, are projected to native behavior so reachable cases still attempt the exact goldens. Overrides such as literal resugaring, Javadoc callbacks or member renaming are not silently dropped. Archive comparisons check paths and entry contents, not container serialization or timestamps.
