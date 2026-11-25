# Testing the current port

The active method stages cover finally recovery, expression lifting, stack-variable simplification, variable type inference, increment recovery, string concatenation, assertions and the first main-loop rewrites. Intermediate entry points expose statement decomposition and the SSA and SSAU passes used during finally recovery and inlining. Run the checks against the checked-in class files with

```sh
cargo test --locked --test control_flow --test structured_flow
```

With JDK 17 or later, a matching upstream checkout with its built `build/libs/*+local.jar`, and compiled fixture classes, run the stage comparisons against Java with

```sh
cargo test --locked --test class_nodes --test control_flow --test structured_flow -- --include-ignored --nocapture
```

`VINEFLOWER_UPSTREAM` defaults to `../vineflower`. `VINEFLOWER_RS_CLASS_ROOT` can point to a directory of compiled classes or an upstream checkout containing `testData/classes`. The CFG comparison runs the default and forced-JSR configurations. It reports differences confined to the numbering of new handlers and the order of disjoint, newly split ranges separately from exact matches. The comparison uses ordered successors in every stage. Protected-block membership and incoming exit edges are compared in order on construction and as multisets after cleanup.

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

## End-to-end source and CLI suite

The retained `upstream_parity` target covers final source and CLI behavior. It currently requires library and binary entry points that still await migration. Use the explicit stage targets above to test the active implementation. The commands below document the end-to-end gate once those entry points are available.

`upstream/` is a byte-preserving copy of the tracked core and plugin `testData` trees from Vineflower `b8273988af850e8cfb234ca08d129058502b032f`: 1,336 core and 154 plugin fixtures, plus the upstream Apache-2.0 license. `registrations.tsv` ports 688 active single-class registrations and their effective fixture settings. The parity target also runs the two bulk cases, six CLI file/directory/archive cases, and the lazy-library case. The upstream disabled archive cases and unconfigured external debug test are not active registrations.

The two end-to-end invocations are

```sh
cargo test --test upstream_parity                                      # original source/CLI/bulk goldens, no JDK
cargo test --test upstream_parity full_parity -- --ignored --nocapture   # all 697 active cases
```

Parity fails on any missing JDK, missing fixture, unsupported capability, source/output mismatch or execution error. Each is reported separately. `VINEFLOWER_RS_PARITY_FILTER` optionally selects a substring of case IDs, such as `core/LVT` or `cli/`. No golden gets created or rewritten. Comparison uses only upstream's newline and outer whitespace normalization, with the three upstream alternate goldens explicitly allowed. Upstream's failable rename case remains a failure on mismatch.

### Compiled inputs

`upstream/` and `registrations.tsv` define the original black-box suite.
`smoke/` holds precompiled upstream inputs for the JDK-free subset.
The stage smoke tests also read classes from this directory.

Checked-in class files are used unchanged. For registered Java source groups, set `VINEFLOWER_JDK_8`, `VINEFLOWER_JDK_9`, `VINEFLOWER_JDK_11`, `VINEFLOWER_JDK_16`, `VINEFLOWER_JDK_17`, `VINEFLOWER_JDK_21` and `VINEFLOWER_JDK_25` to the corresponding JDK homes. Set only the JDKs needed for a focused run. The harness validates the JDK major and runs its `javac` once per source group in a temporary directory, with UTF-8, debug info (except `NoDebug`) and preview flags matching the upstream Gradle configuration. A newer `javac --release` is not a substitute. Runtime-backed registrations require their indicated JDK even with prebuilt classes.

Alternatively, set `VINEFLOWER_RS_CLASS_ROOT` to a tree with the upstream layout: `testData/classes/<group>/` and `plugins/<plugin>/testData/classes/<group>/`. From the matching upstream checkout, the recipe for prebuilt fixture classes is:

```sh
./gradlew :testDataClasses :kotlin:testDataClasses :variable-renaming:testDataClasses
```

Point `VINEFLOWER_RS_CLASS_ROOT` at that checkout. Prebuilt outputs are also needed for Jasm, Kotlin (including `ktold` with upstream's old compiler flags), Groovy and Scala. The Scala plugin is not an included Gradle project at this upstream revision; its plugin classes must be built separately using its `testDataClasses` task from a checkout with that plugin enabled. These tasks only prepare inputs; parity testing never invokes the Java decompiler.
