# Testing the native port

Run the real-class smoke tests and the native source, API and CLI checks with

```sh
cargo test --locked
```

With JDK 17 or later, a matching upstream checkout with its built `build/libs/*+local.jar`, and compiled fixture classes, run the stage comparisons against Java with

```sh
cargo test --locked --test class_nodes --test control_flow --test structured_flow --test driver -- --include-ignored --nocapture
```

`VINEFLOWER_UPSTREAM` defaults to `../vineflower`. `VINEFLOWER_RS_CLASS_ROOT` can point to a directory of compiled classes or an upstream checkout containing `testData/classes`. The CFG comparison runs the default and forced-JSR configurations. It reports differences confined to the numbering of new handlers and the order of disjoint, newly split ranges separately from exact matches. The comparison uses ordered successors in every stage. Protected-block membership and incoming exit edges are compared in order on construction and as multisets after cleanup.

The same handler ID mapping applies to both statement traversals, strongly connected components, and ordinary and extended postdominance. Adjacent new handlers that form singleton components can change order in the component list and the backward traversal. Ordinary postdominance rows follow that traversal and their member order is checked exactly. Extended relations are compared by mapped IDs.

The structured-flow comparison feeds the same prepared CFG to Rust and Java. This isolates statement decomposition from JVM identity hashing during handler allocation. It compares ordered statement trees, typed edges, flags, switch cases, catch variables, method counters and the direct graph. For unreachable direct nodes the comparison checks membership; reachable nodes retain their reverse postorder. An upstream method-level parsing rejection is counted separately and requires the corresponding Rust error.

The expression comparison calls `ExprProcessor.processStatement` on each parsed tree. It compares operand order, expression IDs and types, instruction offsets, local-variable metadata, bootstrap methods and arguments, and sharing of the switch label lists. It covers the default options, forced JSR inlining, disabled debug variable names and complex dynamic constants. The class comparison registers the files on one classpath and checks nested-class relationships, anonymous allocation types, and import resolution with default settings, anonymous-class verification, and inner-class processing disabled.

Root preparation is also compared after lambda discovery and implicit import registration. The snapshot numbers node objects by identity within a root and checks both its child lists and the name lookup, including duplicate names, nested lambdas, target method handles, method references and errors reported by Java.

The class checks also compare the bytecode-derived assertion field and synthetic method-reference flag for each declared method.

The sparse-analysis comparison runs SSA, instruction reassignment, version reset, SSAU and a second reset on the same expressions as Java. It compares reaching definitions at joins, read counts, instruction identity, and the SSAU graph including live variables, field versions, phantom nodes, direct assignments and protected ranges.

The finally comparison runs both the default and forced-semaphore paths, starting from identical CFGs with the original instruction aliases. It checks the recovered graph, semaphore locals and tree, then runs the post-finally cleanup and compares the lifted expressions. Upstream uses an identity-hashed set of incoming blocks when redirecting edges during area removal. A difference confined to their order is reported separately and requires matching multiplicities and identical later stages. Method-level failures are compared at the operation which rejected the input.

The stack comparison prepares the owning classes with the inputs from their compilation group. From identical CFGs it compares the tree and expressions at two points, after the first set of local rewrites reaches a fixed point and after the entire stack-variable pass. The snapshots include expression identity, evaluation order, bytecode offsets, effective and stored types, debug locals, array-initializer and capture flags. Both runs start with the same set of hidden class members and compare changes to that set. The comparison runs with the upstream defaults, with cross-stack simplification disabled, and with ternary conditions in `if` disabled.

The variable comparison checks the first assignment of source variable indices and the fixed point after increment recovery. It compares the lower and upper type bounds, explicit null upper bounds, finality, original slot provenance, expression IDs, effective types and counters. The three profiles exercise default behavior, disabled debug variable names and disabled integer treatment of boolean constants. A JDK-free check also queries two constructors sharing an IR arena and slot zero.

The pre-main comparison runs the full increment fixed point, then checks the method after string concatenation and again after assertion recovery. It compares the tree, expressions, variable state, root flags and comments, hidden class members and the return value of assertion recovery. The two profiles use default options and disabled assertions. A checked-in Java 19 class also exercises the public method entry point and the operand order of dynamic string concatenation without a JDK.

The loop-entry comparison checks the result of edge cleanup and every call to redundant-loop elimination through its first false return. It compares both ordered adjacency lists, closure membership, edge flags, expressions, counters and variables. A JDK-free test uses the upstream Java 8 nested-loop class to check that one elimination preserves the surrounding loops.

The loop-enhancement comparison runs the same entry passes before one call to the loop-enhancement fixed point. Both implementations load the reference JDK as a library so iterator recognition can use its class hierarchy. The checked-in `TestListIteratorHierarchy` smoke fixture exercises a `listIterator()` loop with a subtype of `Iterator`. The snapshot includes the return value, all three nullable header expressions and their contents, and variable bounds retained from removed foreach assignments. A fresh direct graph checks the entry and continue destinations, ordered edges, and expression-list sharing, including the detached list for a counted loop with no initializer.

The loop-merging comparison starts immediately after edge cleanup and compares the native merge loop at its fixed point. Successful loop elimination, loop extraction, and conditional merging all restart the merge loop. The comparison uses the same staged inputs and snapshots of the statement tree and fresh direct graph as the loop-enhancement gate.

The main-loop label comparison starts at the prepared method and runs edge cleanup, the merge loop, stack simplification, variable versioning, and label identification. It checks the resulting ordered adjacency lists, label closures and flags, expressions, counters, variable versions, and a fresh direct graph.

The secondary-function comparison invokes the pass immediately after label identification and checks its return value and complete method snapshots. It includes expression flags that preserve explicit casts and boxing calls. The test runs with default options and with ternary constant simplification enabled, and reports which method results, trees, and expressions change between profiles.

The pattern-matching entry comparison runs the outer main-loop prefix from edge cleanup. A secondary-function or intersection-cast change restarts the prefix. The snapshot follows the iteration in which both passes return false and also checks intersection-cast operand order and variable flags.

The `instanceof` pattern comparison starts from that entry and runs one call to the version-gated pattern pass. It checks the return value, counters on entry and exit, matched conditionals, and record patterns with ordered child expressions and optional bound overrides.

The switch-entry comparison restarts at edge cleanup after each successful `instanceof` pattern pass. It compares the settled tree, expressions, variable state, counters, and fresh direct graph immediately before switch processing.

The switch-pass comparison runs pattern and expression recovery in order on the same method. It checks both return values, counters between the passes and after both, shared case values and edges, case guards, phantom statements, and switch expressions with their backing statements and yields. The try-entry comparison also runs the outer restart after any successful switch pass and compares the settled method immediately before try processing.

The resource comparison checks one try-with-resources recovery pass, including the return value, resource order, catches and their variables, jumps, and return expressions. The single-block comparison restarts the main loop after try recovery until it reaches the inlining pass, then checks that pass's result and the same method state. The graph captures when a try node shares its resource expression list with the statement.

The late-loop comparison checks do-while recovery and infinite-loop return condensation after single-block inlining settles. A successful do-while recovery skips return condensation for that iteration. The exit comparisons check the settled input to exit condensation, one invocation of that pass, and the state after the Java main loop finishes restarting.

The late-loop and exit comparisons separately report incoming continue edges moved in a single Java loop-elimination call. Java iterates those edges from an identity-hashed set. A comparison allows reordering only among the observed edges in each batch and only in the same occupied positions. It checks all other edges and snapshot fields exactly.

The post-main switch comparison runs method callbacks in class wrapper initialization order and publishes complete method roots only once a class finishes its callbacks. This lets switch simplification consult the actual graphs of initialized synthetic enum-table holders while the class being measured remains unpublished. The `AFTER_MAIN` comparison also checks return normalization and monitor rewriting, including bytecode offsets on the dummy exit and boxing flags.

The variable-definition comparison runs the complete declaration phase in both implementations. It compares declaration positions and flags, variable names and types, propagated local-variable records, finality, and switch case scopes.

The method-end comparison takes one snapshot at AT_END and one after the final edge rewrites and diagnostic comments. It compares the statement tree and edge lists directly, including hidden switch defaults and phantom continues.

## Kotlin plugin comparisons

Class-level Kotlin probes use the plugin jar embedded in the upstream distribution. They compare metadata decoding and binding, including partially rejected declarations, JVM accessors, type and contract rendering, compilation-unit headers, and annotation defaults. The method probes compare the plugin's own pass boundaries. To check the final body writers on newly compiled Kotlin, provide the upstream Kotlin compiler classpath and its stdlib jar and run

```sh
KOTLIN_COMPILER_CLASSPATH="..." KOTLIN_STDLIB="..." cargo test --locked --test kotlin_body -- --include-ignored
```

The body comparison covers both string-concatenation settings, reformatted source, method counters, and bytecode-to-source mappings. The full parity harness runs complete Kotlin compilation units using the original test registrations and class files. Select them with `VINEFLOWER_RS_PARITY_FILTER=kotlin/`.

For an independent library comparison, run the pinned Java CLI on JDK 17 with one worker and the native CLI with one, two and automatic workers. Use `--folder --thread-count=1 --include-runtime=1 --dump-exception-on-error=0 --log-level=WARN`, varying the thread count in the native runs. For coroutines, put `-e=<stdlib.jar>` after those options and before the input and output paths.

| Input | External stdlib | Classes | Emitted source files | Method processing / writing failures |
| --- | --- | ---: | --- | ---: |
| kotlinx-coroutines-core-jvm 1.9.0 | 2.0.0 | 826 | 499 Kotlin | 38 / 63 |
| kotlinx-coroutines-core-jvm 1.10.2 | 2.2.20 | 834 | 505 Kotlin | 38 / 66 |
| kotlin-stdlib 2.0.0 | | 983 | 640 Kotlin, 32 Java | 0 / 2 |

At `085199a` all nine native output trees matched Java byte for byte, including resources. Both CLIs reported the same affected classes and method signatures at each failure stage. The counts describe decompiler output and diagnostics. The library sources were not recompiled.

## Java hash collections

The `jhash` target compares insertion, treeification, resizing, and removal order against the actual JDK 17 collections. The class-level hierarchy probe compiles 32 generic interfaces with distinct names that share a Java string hash and compares the declaration order returned by Vineflower's `StructClass.getAllGenerics`.

```sh
cargo test --locked --test jhash -- --include-ignored
cargo test --locked --test class_nodes colliding_interface_names -- --ignored
```

## JDK runtime images

With JDK 17, the runtime-image check compiles a module and uses `jlink` to produce plain, ZIP, shared-constant-pool, layered, and opposite-endian images. It compares individual resources against the JDK extraction, including a class whose name contains a supplementary character. The CLI must resolve an interface from each image to recover an override.

```sh
cargo test --locked --test class_nodes runtime_image -- --include-ignored
```

## End-to-end source and CLI suite

The `upstream_parity` target compares the native library and CLI against the upstream source and archive goldens. The separate `driver` target also runs the original Java CLI on the same input to check configuration, resources, manifests and archived line mappings.

`upstream/` is a byte-preserving copy of the tracked core and plugin `testData` trees from Vineflower `b8273988af850e8cfb234ca08d129058502b032f`: 1,336 core and 154 plugin fixtures, plus the upstream Apache-2.0 license. `registrations.tsv` ports 688 active single-class registrations and their effective fixture settings. The parity target also runs the two bulk cases, six CLI file/directory/archive cases, and the lazy-library case. The upstream disabled archive cases and unconfigured external debug test are not active registrations.

The two end-to-end invocations are

```sh
cargo test --locked --test upstream_parity                                      # original source/CLI/bulk goldens, no JDK
cargo test --locked --test upstream_parity full_parity -- --ignored --nocapture   # all 697 active cases
```

Parity fails on any missing JDK, missing fixture, unsupported capability, source/output mismatch or execution error. Each is reported separately. `VINEFLOWER_RS_PARITY_FILTER` optionally selects a substring of case IDs, such as `core/LVT` or `cli/`. No golden gets created or rewritten. Comparison uses only upstream's newline and outer whitespace normalization, with the three upstream alternate goldens explicitly allowed. Upstream's failable rename case remains a failure on mismatch.

At the pinned revision, the original Java CLI and the native CLI produce identical output for the Scala plugin registrations `TestCaseClasses`, `TestObject` and `TestCompanionObject` when given the same classes and options. Both differ from the three stored plugin goldens. The full suite reports those mismatches.

### Independent Java libraries

Guava 33.3.1-jre, ASM 9.8, Gson 2.11.0, Commons Lang 3.16.0 and SLF4J API 1.7.30 produced 1,024 Java files. Run each library separately with `--folder --include-runtime=<JDK-17-home> --include-classpath=0 --dump-exception-on-error=0`. At `085199a`, automatic workers reproduced all 1,024 previous native files. Comparing with the single-worker Java CLI on JDK 17 gave 1,023 byte-identical files. In Guava's `CharMatcher.java`, the JDK 17 Unicode table escapes U+FDFF and the native Unicode table emits it literally.

As a separate compilation check, run JDK 17 `javac --release 17 -encoding UTF-8 -d <classes>` on all 36 ASM sources in relative-path order, from each output directory. Both compiles produced the same 28 errors. The first, at `AnnotationVisitor.java:13`, references the missing synthetic method `stringConcat$0(int)`. Five other diagnostics report duplicate local declarations. The whole library could not be executed from either set of regenerated sources.

### Compiled inputs

`upstream/` and `registrations.tsv` define the original black-box suite.
`smoke/` holds precompiled upstream inputs for the JDK-free subset.
The stage smoke tests also read classes from this directory.

Checked-in class files are used unchanged. For registered Java source groups, set `VINEFLOWER_JDK_8`, `VINEFLOWER_JDK_9`, `VINEFLOWER_JDK_11`, `VINEFLOWER_JDK_16`, `VINEFLOWER_JDK_17`, `VINEFLOWER_JDK_21` and `VINEFLOWER_JDK_25` to the corresponding JDK homes. Set only the JDKs needed for a focused run. The harness validates the JDK major and runs its `javac` once per source group in a temporary directory, with UTF-8, debug info (except `NoDebug`) and preview flags matching the upstream Gradle configuration. A newer `javac --release` is not a substitute. Runtime-backed registrations require their indicated JDK even with prebuilt classes. For the “Entire Classpath” registrations, include the upstream Gradle runtime libraries in `CLASSPATH`, including Kotlin stdlib, stdlib-jdk7 and stdlib-jdk8 at version 2.0.0.

Alternatively, set `VINEFLOWER_RS_CLASS_ROOT` to a tree with the upstream layout: `testData/classes/<group>/` and `plugins/<plugin>/testData/classes/<group>/`. From the matching upstream checkout, the recipe for prebuilt fixture classes is:

```sh
./gradlew :testDataClasses :kotlin:testDataClasses :variable-renaming:testDataClasses
```

Point `VINEFLOWER_RS_CLASS_ROOT` at that checkout. Prebuilt outputs are also needed for Jasm, Kotlin (including `ktold` with upstream's old compiler flags), Groovy and Scala. The Scala plugin is not an included Gradle project at this upstream revision; its plugin classes must be built separately using its `testDataClasses` task from a checkout with that plugin enabled. These tasks only prepare inputs; parity testing never invokes the Java decompiler.

### IR lifetime on multiple input units

The ignored driver test `nested_constructor_and_switch_map_survive_class_and_unit_order` compiles an inner constructor and an enum-table holder with javac. It compares native output at one and two workers with Java at one worker, using both root orders in one archive and both archive orders across units. It recompiles and executes the emitted sources. The enum switch depends on when the holder's method graph becomes available.

`parallel_method_graphs_preserve_archive_order_and_mappings` compiles three roots with distinct implementations of the same method signature, switch and finally blocks, and methods without Code. The input omits a class referenced by one signature. It compares archive entry order, sources and line mappings at the default worker count, one, two and automatic, repeats the two-worker run, then recompiles and executes the result with the dependency available.

For the larger memory comparison, use the Minecraft 26.3 client (SHA-256 `4508d006323f24fa02876310c192d739af56516eb259000ac50f0909a68c9a2d`). Select the complete class subtrees below in central-directory order. Make one combined archive and one archive per subtree, registering the latter in the order shown. Supply the remaining class entries as one external library.

| Class count | Subtrees |
| ---: | --- |
| 760 | `com/mojang/blaze3d/`, `net/minecraft/advancements/`, `net/minecraft/nbt/`, `net/minecraft/network/chat/`, `net/minecraft/server/commands/` |
| 2,831 | `com/mojang/renderpearl/`, `net/minecraft/client/gui/`, `net/minecraft/network/`, `net/minecraft/server/`, `net/minecraft/world/item/` |

From the repository root, generate either layout set in a fresh directory with

```sh
python3 test/prepare_client.py ~/Downloads/26.3.jar 2831 /tmp/vineflower-2831
```

The script writes `combined.jar`, `part-1.jar` through `part-5.jar` and `external.jar`. It includes explicit directories from the selected subtrees and places `META-INF/LICENSE` in the combined JAR and the first part. The combined JAR for 2,831 classes has SHA-256 `c9e10a42272d5d75139f64285214ac12f05d0f3c3d461a7b4f2140320b8ea3fb`. For the smaller input, pass `760` and a different destination.

Build both revisions with `cargo build --release --locked`. With the same JDK, run each binary on the identical archives and write each output to a fresh directory. The macOS comparison used JDK 25.0.2 and the median maximum resident set size from three runs of each binary. Retain the exact inputs, command lines and output manifests between revisions.

```sh
/usr/bin/time -l "$cli" --folder --thread-count=1 --include-runtime=1 \
  --bytecode-source-mapping=1 --log-level=ERROR "-e=$external" "$@" "$destination"
```

Compare the relative filenames and bytes against both the previous binary and the pinned Java CLI. For archive line mappings use `--legacy-saving --dump-code-lines=1` and compare central-directory entry order, uncompressed contents and the `0x4646` extra field.


With baseline `eb137e2` and execution code `4125b28`, the 2,831-class subset produced 1,762 Java files in both layouts. With a single worker, median peak RSS fell from 1,304.8 to 1,083.5 MiB for one input JAR, and from 1,280.5 to 804.3 MiB for five. Median elapsed time changed from 9.81 to 10.07 seconds and from 9.41 to 10.12 seconds, respectively.

Three paired single-worker runs on the complete client produced identical output trees across revisions and against the Java CLI (7,301 Java files and 21,495 resources). Median peak RSS was 6.410 GiB before and 6.526 GiB after. The separate macOS peak memory footprint decreased in all three pairs, with medians of 5.460 and 4.379 GiB. Median elapsed time was 42.01 and 45.29 seconds. The single input unit retains all published root wrappers through the preparation barrier.

### Root worker comparison

Release `c1b5109` prepares the initial control-flow and statement graphs on root workers. The comparison used the inputs, JDK, directory output and flags above, with release `381a023` as the baseline. Each before/after pair measures one run per release on an Apple M4 Pro after earlier runs on the same archives. RSS is the maximum resident set size reported by macOS.

| Input | Workers | Elapsed before / after (s) | Peak RSS before / after (GiB) |
| --- | --- | ---: | ---: |
| 2,831 classes in one JAR | 1 | 10.17 / 10.20 | 1.059 / 1.059 |
| 2,831 classes in one JAR | auto | 10.13 / 9.89 | 1.058 / 1.066 |
| Complete 26.3 client | 1 | 44.69 / 44.90 | 6.401 / 6.557 |
| Complete 26.3 client | auto | 44.67 / 44.24 | 6.265 / 5.999 |

The automatic setting selected a thread count of 14. User and system CPU time summed to 44.80 s before and 46.44 s after on the full automatic run. At one, two and automatic workers the client's directory tree matched the pinned Java CLI. Both layouts of the 2,831-class subset also preserved archive entry order, source bytes and all 1,520 line maps against the previous native release. Four maps on JDK 25.0.2 have the same line pairs as Java in a different order, as in the baseline.

### Retained bytecode and statement graphs

For a live-object count, use a separate instrumented release and trace the published wrappers after preparing all roots in the input unit, before rendering the first one. Count distinct block handles and instruction Arcs, including instructions retained by variable expressions. The ordinary CLI samples below use the default collection schedule.

On the complete 26.3 client with one worker, moving from `ac822b7` to `42107a8` reduced live blocks at that barrier from 305,549 to 161,109 and distinct instructions from 1,853,691 to 1,672,798. All 161,109 remaining blocks belong to statements. Both builds had 401,862 live statements. Across their incoming and outgoing indexes, 312,507 directions each referred to one distinct edge. The final representation stores its identity and view membership inline. On arm64 macOS the size of a statement fell from 480 to 448 bytes and that of an instruction from 112 to 104 bytes.

The following release CLI runs used the same Apple M4 Pro, JDK and directory output options as the root worker comparison. Each full-client row is one consecutive pair. The subset rows compare the final build with earlier single-run samples of the baseline. The single-worker full-client pair isolates the release of completed CFG links. The other rows include both representation changes as well.

| Input | Workers | Revisions (before / after) | Elapsed (s) | Peak RSS (GiB) | Peak macOS footprint (GiB) |
| --- | ---: | --- | ---: | ---: | ---: |
| Complete 26.3 client | 1 | `566e018` / `42107a8` | 44.93 / 44.50 | 6.157 / 6.273 | 4.102 / 4.229 |
| Complete 26.3 client | auto (14) | `ac822b7` / `42107a8` | 44.36 / 43.46 | 6.386 / 6.486 | 4.476 / 4.137 |
| 2,831 classes in one JAR | 1 | `ac822b7` / `42107a8` | 10.29 / 9.99 | 1.060 / 0.993 | 0.823 / 0.755 |
| 2,831 classes in five JARs | 1 | `ac822b7` / `42107a8` | 10.14 / 9.93 | 0.786 / 0.765 | 0.622 / 0.596 |

The full-client pairs produced the same 7,301 Java files and 21,495 resources as the pinned Java CLI. Peak RSS increased in both pairs despite the reduction in live objects at the preparation barrier.

`public_method_callback_retains_its_cfg_after_wrapper_publication` processes the checked-in `TestSimpleWhile.class` through the public method callback and reads its saved CFG entry after the wrapper is published. It checks the identities and order of its incoming and outgoing blocks.

### Published method tables and direct graphs

At the same single-worker preparation barrier, compare `dfc0263` and `cc92d63` by visiting every published method and its cached graph in class-node allocation order. For each direct node check its statement, expression-list and block handles, the four ordered lists of neighbors, and its enclosing finally node. Include traversal order, branch and destination maps in the comparison. On the complete client both revisions retained 82,030 graphs with 266,886 nodes and the same topology. For each direction there were 217,247 regular edges and 6,343 exception edges.

| Storage at the full-client barrier | Before | After |
| --- | ---: | ---: |
| Reserved slots for 98,739 method wrappers | 139,416 | 98,739 |
| Reserved direct-node slots | 457,864 | 266,886 |
| Bytes per direct node (arm64 macOS) | 136 | 88 |
| Separate adjacency buffers | 377,659 | 3,360 |
| Method, node and adjacency arrays, requested bytes | 117,427,536 | 57,586,296 |
| Same allocations, usable bytes reported by macOS `malloc_size` | 132,738,320 | 68,282,336 |

The byte counts cover the three listed arrays at the barrier. The graphs' traversal vectors and lookup maps are counted separately for the topology check. On the single-JAR 2,831-class subset the same arrays used 36,369,120 and 18,563,328 allocator bytes before and after, with identical topology across 22,548 graphs.

Ordinary release builds on the same M4 Pro and JDK 25.0.2 gave the following paired samples. The before and after binaries processed identical input archives into fresh directories.

| Input | Workers | Elapsed before / after (s) | Peak RSS before / after (GiB) | Peak macOS footprint before / after (GiB) |
| --- | ---: | ---: | ---: | ---: |
| 2,831 classes in one JAR | 1 | 9.83 / 9.78 | 1.002 / 0.982 | 0.759 / 0.743 |
| 2,831 classes in five JARs | 1 | 10.03 / 9.89 | 0.762 / 0.750 | 0.589 / 0.587 |
| Complete 26.3 client | 1 | 44.72 / 44.20 | 7.089 / 6.921 | 4.061 / 3.866 |
| Complete 26.3 client | auto (14) | 43.84 / 43.48 | 7.019 / 6.966 | 3.957 / 3.884 |

The other round used the reverse execution order and a build with identical executable instructions. It also showed lower single-worker peak RSS on all three inputs. Full-client automatic peak RSS changed from 6.974 to 6.999 GiB in that round. The full output trees matched Java at both worker settings. Both subset layouts preserved archive entry order, source bytes and all 1,520 native line maps.

A separate instrumented single-worker run on the combined subset timed the passes inside the ordinary CLI. Of 10.072 s in the driver, 0.326 s went to the existing decode and structure prefix. Finally recovery, final cleanup and expression lifting, and the first stack SSA split took 0.044, 0.121 and 0.236 s respectively. The remainder of the first stack simplification took 3.603 s. These timings exclude nested phases from their parent totals. The instrumented run produced the same files as the ordinary release.

### Stack variable analysis

On the same 2,831-class combined input, 25,130 methods had code. In an instrumented single-worker run at `d8efd3c`, their first stack simplification took 3.943 s in total. All SSA splits in that call took 0.633 s, SSAU splits took 1.822 s, and stack inlining took 0.782 s. These numbers include the final SSAU and inlining pass after convergence.

The SSA sweeps in that call saved 1,316,606 input maps containing 9,910,607 version sets. All 2,754 lookups of the saved inputs from finally edges missed. Vineflower 1.12.0 looks up an uppercase `_FINALLY` suffix, while its graph builder assigns lowercase node IDs. The native sweeps now move the merged input directly into expression processing. The catchable map starts with a separate copy of the incoming locals.

The stack inliner visits a node with the replacement map from its first incoming path in FIFO order. Counting at that boundary showed 320,912 map copies before and 45,948 after, containing 1,621,671 and 222,826 entries respectively. Both runs visited 359,417 nodes and processed 1,081,008 expression positions. The output trees matched the Java CLI.

The driver test `wide_reaching_versions_match_upstream_and_recompile` compiles 150 conditional assignments to one local, followed by a loop with a catch and a finally block. It compares both CLIs' source bytes and checks the rebuilt program against the input class on 256 values.

The ordinary release CLI ran each input twice per revision, reversing the execution order for the second pair. The table gives the means on the same M4 Pro with JDK 25.0.2 and the directory output options above. The before binary is from `cc92d63`, which has the same production code as `d8efd3c`. The after binary is from `b007c8f`. CPU is user plus system time.

| Input | Workers | Elapsed before / after (s) | CPU before / after (s) | Peak RSS before / after (GiB) | Peak macOS footprint before / after (GiB) |
| --- | ---: | ---: | ---: | ---: | ---: |
| 2,831 classes in one JAR | 1 | 9.975 / 8.400 | 9.860 / 8.300 | 0.976 / 1.020 | 0.742 / 0.783 |
| 2,831 classes in five JARs | 1 | 10.005 / 8.365 | 9.925 / 8.345 | 0.757 / 0.791 | 0.590 / 0.609 |
| Complete 26.3 client | 1 | 44.555 / 38.515 | 44.460 / 38.420 | 6.784 / 6.741 | 3.951 / 4.023 |
| Complete 26.3 client | auto (14) | 43.580 / 37.455 | 45.520 / 39.365 | 6.815 / 6.728 | 4.064 / 4.067 |

The pinned Java CLI ran once per worker setting on the full client with the same options and `-Xmx6g`. One worker took 42.37 s elapsed and 120.84 s CPU, with 4.440 GiB peak RSS. Automatic took 14.84 s elapsed and 165.30 s CPU, with 6.301 GiB peak RSS. Every full run produced the same 7,301 Java files and 21,495 resources. The two subset layouts also matched their Java output trees and preserved the same native archive entries and line mappings as before.

### First stack simplification on root workers

On the combined 2,831-class input, an instrumented release prepared 25,130 methods with code. The coordinator reused 25,101 graphs through the first stack simplification. The other 29 methods needed the published sibling wrapper for an interface assertion and ran at their original position. Every recorded class lookup still matched at publication in this input.

Two driver tests exercise the boundaries with one, two and automatic workers. `parallel_stack_preparation_preserves_shared_class_access` compares sources and archive line maps with Java for a constant-dynamic import that loads an annotated library and an assertion that reads a sibling wrapper. A damaged initializer and an invalid return type on a `String.length` reference check that decoding and expression lifting report errors in method order with empty stderr. `worker_allocations_observe_lambdas_published_by_an_earlier_unit` compiles and runs a Java program, renames one class in the constant pool to collide with Vineflower's generated lambda name, and runs it again on the JVM. It compares both orders of two multi-root archives against Java. Publishing the lambda first changes which class the decompiler sees at an allocation site and makes the original writer reject the method.

The following pairs use the ordinary release binaries from `b007c8f` and `085199a` on the same M4 Pro, JDK 25.0.2, inputs and directory output options as above. Each entry is the mean of two runs, reversing the order of both revisions and inputs in the second round.

| Input | Workers | Elapsed before / after (s) | CPU before / after (s) | Peak RSS before / after (GiB) | Peak macOS footprint before / after (GiB) |
| --- | ---: | ---: | ---: | ---: | ---: |
| Complete 26.3 client | 1 | 38.300 / 38.755 | 38.230 / 38.580 | 6.698 / 6.642 | 4.051 / 3.926 |
| Complete 26.3 client | auto (14) | 37.085 / 27.650 | 38.965 / 45.545 | 6.693 / 6.723 | 4.082 / 3.908 |
| 2,831 classes in one JAR | 1 | 8.370 / 8.420 | 8.355 / 8.400 | 1.022 / 1.008 | 0.783 / 0.784 |
| 2,831 classes in one JAR | auto (14) | 8.205 / 6.500 | 8.600 / 10.970 | 1.032 / 1.032 | 0.794 / 0.806 |
| 2,831 classes in five JARs | auto (14) | 8.350 / 5.960 | 8.835 / 10.475 | 0.795 / 0.797 | 0.651 / 0.662 |

All 20 runs matched the pinned Java output trees. Full-client automatic elapsed time fell by 25.4%, with the two new runs taking 27.40 and 27.90 seconds. The Java reference at the same worker setting took 14.84 seconds. Both subset layouts also reproduced the previous native archive entry order, sources and all 1,520 native line mappings at two workers.
