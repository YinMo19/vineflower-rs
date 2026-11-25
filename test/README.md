# Testing the current port

The active method pipeline reconstructs structured Java statements through the first `DomHelper.parseGraph` call. Run the checks against the checked-in class files with

```sh
cargo test --locked --test control_flow --test structured_flow
```

With JDK 17 or later, a matching upstream checkout with its built `build/libs/*+local.jar`, and compiled fixture classes, the following command also compares the three CFG stages, statement ordering and postdominators, and the structured method and direct graphs with the Java implementation.

```sh
cargo test --locked --test control_flow --test structured_flow -- --include-ignored --nocapture
```

`VINEFLOWER_UPSTREAM` defaults to `../vineflower`. `VINEFLOWER_RS_CLASS_ROOT` can point to a directory of compiled classes or an upstream checkout containing `testData/classes`. The comparison runs the default and forced-JSR configurations. It reports differences confined to the numbering of new handlers and the order of disjoint, newly split ranges separately from exact matches. The comparison uses ordered successors in every stage. Protected-block membership and incoming exit edges are compared in order on construction and as multisets after cleanup.

The structured-flow comparison feeds the same prepared CFG to Rust and Java. This isolates statement decomposition from JVM identity hashing during handler allocation. It compares ordered statement trees, typed edges, flags, switch cases, catch variables, method counters and the direct graph. For unreachable direct nodes the comparison checks membership; reachable nodes retain their reverse postorder. An upstream method-level parsing rejection is counted separately and requires the corresponding Rust error.

## Historical source and CLI parity suite

The remainder documents the earlier Rust implementation and its corpus. The source and CLI suite depends on library and binary entry points awaiting migration. Its historical numbers describe that implementation.

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
and handler-free void method tails missing their final return. It also
accepts unused receivers omitted by early class files and interprets a
malformed `swap` as an exchange of two whole stack values.

The implementation separates class-file decoding, JVM instructions, CFG
analysis, operand-stack lifting, region recovery, and source rendering.
Modules with submodules use a directory `mod.rs` and ordinary relative
module declarations; leaf modules stay in single files.
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
| Transparent rethrows, qualified enum patterns, and conditional case fallthrough | 154 | 85 | 458 | 0 |
| Finally locals and saved returns, loop continuations, grouped unnamed patterns, and short-circuit assignments | 154 | 80 | 463 | 0 |
| Labeled loops, protected switches, nested predicate state, and named Kotlin suspension | 154 | 75 | 468 | 0 |
| Scoped catch joins, abrupt finally copies, bound preview guards, and Kotlin enum entries | 154 | 68 | 475 | 0 |
| Pattern and resource loop recovery, source maps, and JVM call descriptors | 214 | 34 | 449 | 0 |
| Generic foreach, bound method references, Java coroutine output, and Kotlin callable and retry recovery | 226 | 25 | 446 | 0 |
| Generic invocation and initialization, intersection casts, condition mappings, and protected loops | 236 | 17 | 444 | 0 |
| Lambda targets and source maps, loop scopes, anonymous initializers, and Kotlin declarations | 265 | 13 | 419 | 0 |
| Anonymous captures and annotations, preview switches, finally maps, and Kotlin try expressions | 285 | 11 | 401 | 0 |
| Anonymous class names, nested receivers, synchronized exits, and Kotlin try returns | 292 | 10 | 395 | 0 |
| Field initializers, generic construction and invocation, resource loops, and Kotlin products | 300 | 8 | 389 | 0 |
| Iterable receivers, loop scope and maps, resource catch names, switch expressions, and Kotlin smart casts | 311 | 7 | 379 | 0 |
| Loop continuations, shared switch defaults, constructor delegation, and Kotlin callable objects | 318 | 5 | 374 | 0 |
| Generic calls and SAM targets, exception mappings, pattern switches, and Kotlin parameter shadowing | 331 | 5 | 361 | 0 |
| Nestmate calls, generic casts, anonymous initializer mappings, enum switches, resource loops, and Kotlin ranges | 342 | 5 | 350 | 0 |
| Bounded generic calls, anonymous lambda targets, resource switch exits, record patterns, and Kotlin lambda numbering | 348 | 5 | 344 | 0 |
| Covariant generic calls, stream lambda targets, synchronized returns, switch local scopes, and Kotlin String captures | 351 | 5 | 341 | 0 |
| Generic lambda targets, implicit interface member constructors, finally exits, and deep record mappings | 357 | 5 | 335 | 0 |
| Contextual generic construction, array foreach, assertion operands, finally loops, and Kotlin branch returns | 360 | 5 | 332 | 0 |
| Wrapper overload selection, generic receiver casts, loop terminal branches, typed catches, and Kotlin contracts | 367 | 5 | 325 | 0 |
| Chained lambda target types, boolean switch statements, constructor exits, counted loops, and Kotlin ranges and locals | 371 | 5 | 321 | 0 |
| String hash collisions in predicate switches, generic iterator expressions and casts, and filtered Kotlin companions | 374 | 5 | 318 | 0 |
| Instance constant initialization, constructor and setter mappings, allocation qualifiers, boxed monitors, and Kotlin Boolean decisions | 383 | 5 | 309 | 0 |
| Typed conditional and boxing expressions, nested predicate switches, legacy synchronized control flow, and Kotlin catch cleanup | 392 | 5 | 300 | 0 |
| Constructor varargs after conditional elements, switch stack joins, protected retry loops, and Kotlin Boolean returns | 397 | 5 | 295 | 0 |
| Local array initializers, switch fallthrough bindings, nested catches, and Kotlin protected printing | 400 | 5 | 292 | 0 |

All eight upstream CLI and bulk cases match. The full test continues to
report every difference from the 697 reference outputs.

The runner preserves explicit companions, discovers sibling `$*.class` files
and resolves Kotlin file facades. It installs the upstream fixture's selected
plugins and runtime classpath where applicable, and checks the lazy-library
case against the native provider callback. Fixture diagnostics and validation
flags that do not affect source generation are handled separately from source
options. Archive comparisons check entry names and contents, not container
serialization or timestamps.

### Confirmed behavior exceptions

The port preserves the fixture's JVM behavior when the upstream reference
changes it. These cases still appear as differences in the strict comparison.
Each entry records the specific discrepancy verified against the bytecode.

| Original fixture | Verified difference |
| --- | --- |
| `core/Default/JAVA_8/pkg/TestMethodHandles` | The fixture invokes `MethodHandle.invokeExact` with a `long` argument. Recompiling the upstream source changes `(J)J` to `(I)J` and changes the `PrintStream` call from `(Ljava/io/PrintStream;J)V` to `(Ljava/io/PrintStream;I)V`. The Rust output preserves both descriptors and the required argument conversion. |
| `core/Default/JAVA_8/pkg/TestClassFields` | The fixture writes `names` before evaluating `names.length`. The recompiled upstream source reads `names` before that write, so initialization throws `NullPointerException`. The Rust output preserves the write before the read. |
| `core/Default/CUSTOM/TestJsr2` | In `main`, `main2`, and `main3`, handlers discard the throwable with `pop` at bytecode offset 11 or 23 and proceed to the shared continuation. The upstream empty `finally` would propagate the exception. The Rust output uses an empty `catch (Throwable ...)` and continues normally. |
| `core/Default/JAVA_8/pkg/TestNumberDisambiguation` | The fixture invokes both the `int...` and `float...` overloads. The upstream source recompiles both calls to `([I)V`. The Rust output keeps the cast required to select `([F)V` for the second call. |
| `core/Default/JASM/pkg/TestGoto` | The fixture invokes `PrintStream.println(Object)`. The upstream string literals recompile to `println(String)`. The Rust output casts the arguments to `Object` to preserve the overload and its virtual dispatch. |
| `core/Java Runtime/JAVA_8/pkg/TestTryReturn` | In `testInvalidUse`, the upstream output uses `var15` outside its catch scope. The Rust output retains the stored throwable in the enclosing local and recompiles. |
| `core/Default/JAVA_8/pkg/TestTryCatchNested` | Two ordered `Exception` entries cover the same protected interval. The JVM always selects the first entry. The upstream source has two consecutive `catch (Exception ...)` clauses for that interval, which `javac` rejects. The Rust output emits the reachable handler. |
| `core/Default/JAVA_8/pkg/TestMethodReferenceSameName` | The qualifier of `run()` needs a target type for the method reference. Adding the `Runnable` cast makes the Rust output compile with Java 8 and reproduces the original `Object.getClass` receiver check and `Runnable.run` call. |
| `core/Default/JAVA_21/pkg/TestMethodReferenceJ21` and `core/Default/JAVA_25/pkg/TestMethodReferenceJ25` | The upstream `test6` uses an undeclared `rec$`. The Rust output evaluates the receiver once and retains the capture-time null checks in `test3` and `test6`, before the call to `consume`. |
| `core/Java Runtime/JAVA_8/pkg/TestGenericCast` | The upstream `test1` returns the result of `toArray` on a raw `List`, whose source return type is `Object[]`. Java 8 rejects that return as `String[]`. The Rust output retains the `String[]` cast. |
| `core/Default/JAVA_8/pkg/TestGenericsInvocUnchecked` | Java 8 rejects the upstream `Enum.valueOf(c, s)` because capture of `Class<?>` cannot satisfy `E extends Enum<E>`. The Rust output keeps the unchecked `Class<? extends Enum>` conversion. The recompiled JVM instructions and results for valid, missing, and null enum inputs agree with the fixture. |
| `core/Java Runtime/JAVA_8/pkg/TestGenericCastSuper` | Java 8 rejects the upstream unconverted `this` in both returns and the argument to `consume`. The Rust output restores those conversions and the typed downcast of `super.get()`. The recompiled instructions, bridge dispatch, and receiver identity agree with the fixture. |
| `core/Java Runtime/JAVA_8/pkg/TestGenericCastCall` | Java 8 rejects unary `!` on the upstream raw `Inner2.val()` result, whose source type is `Object`. The Rust output recovers `Inner2<Boolean>`, recompiles to the original Boolean check and unboxing, and preserves the tested null and wrong-receiver failures. |
| `core/Default/JAVA_8/pkg/TestGenericCasts` | Java 8 rejects the upstream raw `List` in the enhanced loop and method reference, and the omitted type-variable conversions in `conv2` and `conv3`. The Rust output recovers typed loop and sort receivers and retains the required return casts. All six classes recompile with matching executable instructions and lambda bootstrap descriptors. |
| `core/Java Runtime/JAVA_8/pkg/TestGenericsHierarchy` | Recompiling the upstream cast on the argument to `List.add` adds a `CHECKCAST Number` after `List.get`. The fixture passes that value with its erased `Object` type. The Rust roundtrip retains the original instructions. A reachable companion probe also preserves forwarding of an unchecked nonnumeric element while keeping the check on a value assigned to a local. |
| `core/Java Runtime/JAVA_8/pkg/TestGenericArrays` | Java 8 rejects the upstream enhanced loop because its `Enum[]` cast leaves elements with type `Enum` and its binding requires `K`. The Rust output keeps the `K[]` source type from `Class<K>.getEnumConstants()` and recompiles to the original array check and `EnumMap.put` descriptor. |
| `core/Java Runtime/JAVA_8/pkg/TestItrLoop` | Java 8 rejects the upstream `String` loop variables over the raw `List`. The Rust output restores the element casts and preserves the `List.iterator` and `Iterable.iterator` descriptors. Recompiled instructions agree with the originals, and the original and rebuilt loops agree for valid, null, and mixed-type inputs. |
| `core/Default/JAVA_8/pkg/TestEnhancedForLoops` | Java 8 rejects the upstream `String` and `int` loop variables over raw `ArrayList` expressions. The Rust output keeps the typed local bindings and recompiles to the original instructions, including String element casts and Integer unboxing. |
| `core/Default/JAVA_8/pkg/TestForeachMultiDimensionalArray` | The upstream source increments an uninitialized `var4` inside the switch. The Rust output keeps the initialized array index and its increment after the switch. The recompiled fixture has the same observed outcome. |
| `core/Java Runtime/JAVA_8/pkg/TestTryWithResourcesReturn` | The upstream `testFinally` moves the overriding return out of `finally`, leaving an undeclared `FileNotFoundException`. Its `testFinallyNested` has no executable return. The Rust output keeps the overriding returns and recompiles. Both original methods and the rebuilt methods return `null` for existing files, missing files, and null input. |
| `core/Default/JAVA_8/pkg/TestLoopFinally` | Java 8 rejects the upstream `<unknown>` type in `testConditionalBreakInFinally` and the uninitialized local in the separately compiled `test5`. The separately compiled upstream `test1` also prints four extra `continue` lines. The Rust rebuild matches the original JVM fixture across 210 observed lines. |
| `core/Default/JAVA_8/pkg/TestFinallyThrow` | The upstream `test1` moves the throw into the protected region. Running the recompiled method prints extra stack traces for an injected exception and for null. The Rust output retains the throw boundary and agrees with the original across 22 output lines after normalizing source line numbers. |
| `core/Default/JAVA_8/pkg/TestFinallyBlockVariableUse` | The upstream return expression skips the local write that the `finally` block reads. With `s = "10"`, `i = 0`, and `j = 2`, the original and Rust rebuild call `accept` with `[6, 10, 8, 2]`. The upstream source skips that call. |
| `core/Default/KOTLIN/pkg/TestSynchronizedUnprotected` | The original synchronized body invokes `PrintStream.println(Object)`. The reference Java source selects `println(String)`, which a replacement stream can observe. The Rust output retains the original descriptor. |
| `core/Java Runtime/JAVA_21/pkg/TestTryWithResourcesJ21` | Java 21 reports missing return statements for upstream `test2`, `test5`, and `test6`, whose bodies contain only bytecode comments. The Rust output recompiles. The original and rebuilt methods agree across 39 observed results on ordinary, missing, and empty files. |
| `core/Default/JAVA_8/pkg/TestLambdaParamTypes` | The upstream implicit lambda parameters in `f2b`, `g`, and `h` infer `Object`, so `length()` fails to compile. The Rust output keeps the `Function<String, Object>` target where the original bootstrap requires a String argument. |
| `core/Default/JAVA_17/pkg/TestDuplicateAssignmentInSwitchExpr` | The upstream output redeclares `num` inside the initializer of the outer `num`. Java 17 rejects the duplicate local. The Rust output keeps distinct names and recompiles with the original tested dispatch and assignments. |
| `core/Default/JAVA_16/pkg/TestConstructorSwitchExpression2` | Java 16 rejects the upstream `this(null)` inside a switch arm. The Rust output preserves delegation as a constructor invocation, and the rebuilt fixture calls the original `this(String)` constructor for each sampled selector. |
| `core/Default/JAVA_16/pkg/TestConstructorSwitchExpression3` | Java 16 rejects the upstream enum constants without arguments and their explicit construction in a static block. The Rust output keeps the arguments with the constant declarations. Recompilation reproduces the original executable instructions. |
| `core/Default/JAVA_8/pkg/TestLocalClassesSwitch` | In `test2`, Java 8 rejects the repeated `LocalClass` declarations in the same switch scope. The Rust output scopes each declaration to its arm. The original and rebuilt classes agree across 19 observed output rows. |
| `core/Default/JAVA_8/pkg/TestClashName` | An `int` local named `SharedName2` shadows the unqualified type name in the upstream `SharedName2.f` expression. The Rust output uses `pkg.SharedName2.f` and recompiles to the original field access and subsequent instructions. |
| `core/Lambda to Anonymous Class/JAVA_8/pkg/TestLambdaToAnonymousClass` and `core/Lambda to Anonymous Class/JAVA_8/pkg/TestLambdaToAnonymousClass2` | Java 8 rejects the upstream SAM overrides because they omit return types. The Rust output keeps the declared `BiConsumer<List<String>, Integer>` target and the erased overrides. The recompiled code preserves the printing and stream call descriptors, the tested traversal order, and the tested exception types. |
| `core/Java Runtime/JAVA_8/pkg/TestAnonymousClass` | The upstream reference moves field declarations ahead of methods that allocate earlier anonymous classes. JDK 8 assigns different binary names on recompilation. The Rust output preserves the tested reflective binary names and enclosing members, along with field initialization and iterator behavior. |
| `core/Java Runtime/JAVA_8/pkg/TestNoGenericDiamonds` | Java 8 cannot infer `Inner<>` from the upstream invocation. The declared `I<String>` argument does not satisfy the constructor's `I<? extends I<T>>` parameter. The raw construction in the Rust output recompiles. |
| `core/Default/JAVA_17_PREVIEW/pkg/TestSwitchPatternMatching{2,5,15,18,Constructor1,Return2}` | JDK 17 with preview enabled rejects the upstream `when` guard syntax. The Rust output uses guarded patterns with `&&` and recompiles with the original JDK. The sampled null, pattern, and guard outcomes agree. |
| `core/Default/JAVA_17_PREVIEW/pkg/TestSwitchPatternMatching17` | The upstream reference contains an invalid source invocation of `SwitchBootstraps.typeSwitch`. The Rust output recompiles on JDK 17 and preserves the tested dispatch and side effects. |
| `core/Default/JAVA_17_PREVIEW/pkg/TestSwitchPatternMatching22` | JDK 17 rejects both upstream goldens because of fall-through from a pattern label. The Rust output restores the branch boundary and agrees with the tested exception and cleanup paths. |
| `core/Default/JAVA_21/pkg/TestSwitchOnEnumJ21` | The upstream `testComplexPattern` contains a bytecode listing in comments and recompiles to an empty method. The Rust output preserves the original dispatch, including the six output lines lost by the recompiled reference. |
| `core/Default/KOTLIN/pkg/TestSuspendLambdaKt` | The upstream output uses a class declared inside a static block from a field initializer. The Rust output uses a static member with the original binary name and reproduces the suspension closure's tested execution. Java reflection reports the recompiled class as a member class. |
| `core/Entire Classpath/KOTLIN/pkg/TestNamedSuspendFun2Kt` | The upstream source accesses continuation spill fields through `Continuation` and omits the synthetic `result` field used on resumption. The Rust output uses the typed frame and preserves the tested initial, resume, and cleanup paths. The original suspension target returns immediately. The Rust output retains its suspension-marker branch, verified against the bytecode. Java reflection reports the recompiled frame as a static member and `result` as a regular field. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestFuncRef` | The upstream `StringsKt.repeat` is unresolved in Kotlin source. The Rust output uses the `repeat` extension, which recompiles to the original `kotlin/text/StringsKt.repeat` and preserves the erased `Function1.invoke` target. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestReflection` | Kotlin rejects the upstream raw `KFunction` and `Function1` types and the `this.getClass()::class` expression. The Rust output keeps the callable's type and uses `this::class`. Recompilation preserves `Object.getClass`, `Reflection.getOrCreateKotlinClass`, the erased callable invocation, and the original `println` overload. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestTopLevelKt` | Kotlin rejects the upstream `final` modifier on top-level properties. The Rust output preserves the facade's `setTopLevelVar(I)V` signature and initializer order. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestTrySynchronized` | The upstream source includes an uninitialized monitor, invalid `@Throws` syntax, and a null assigned to the nonnullable stream type. The Rust output recompiles with the original executable instructions, exception tables, monitor exits, and null check before `close`. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestSynchronized` | Kotlin 2.0 recompiles the upstream printing expression to `PrintStream.println(String)`. The original and Rust roundtrip call `println(Object)`. The roundtrip also matches monitor release after an injected exception or error. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestSealedHierarchy` | Recompiling the upstream source changes the nested class order observed through `KClass.nestedClasses` from `[TestObject, TestClass]` to `[TestClass, TestObject]`. The Rust output preserves the observed original order. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestForRange` and `TestIfRange` | Kotlin 2.0 rejects the upstream JVM facade calls in both fixtures and the raw `Iterable` in `TestIfRange`. The Rust output recompiles and agrees across 1,316 observed output lines. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestNonInlineLambda` | Kotlin 2.0 rejects the upstream raw `ObjectRef`, undefined `$y`, and `Unit.INSTANCE`. The Rust output recovers a scoped mutable String. The recompiled helper opcodes and the tested null and wrong-type exception diagnostics agree with the original. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestSmartCasts` | Kotlin 2.0 rejects the upstream raw `Pair` and the cast to `java.lang.String` in a Kotlin String context. The Rust output uses the proven `Pair` smart cast and shares one member invocation across the two subtype tests. The recompiled `testWhen` instructions and 148 observed output lines agree with the fixture. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestAnyType` | Kotlin 2.0 rejects the upstream `length()` call on the String property. The Rust output uses the property and recompiles to the original 15 instructions. The print overload and an injected exception agree with the original. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestContracts` | Kotlin 2.0 rejects the upstream contract declarations and raw iteration types. The Rust output preserves the short-circuit expressions, type checks, and inline `sumOf`. Recompilation reproduces all 99 instructions in the six fixture methods, and 91 observed runtime lines agree. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestTryLoopReturnFinally` and `kotlin/Entire Classpath/KOTLIN/pkg/TestTryLoopSimpleFinally` | Kotlin rejects the upstream uninitialized property declarations. The Rust output preserves the initialization and recompiles with the original executable instructions and exception tables. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestTryLoop` | Kotlin rejects the upstream uninitialized property and the `Files.exists` call that passes an array without a spread. The Rust output preserves the empty `LinkOption` array and the retry loop's executable instructions and exception table. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestTryLoopNoCatch` | The upstream string length, index range, and `@Throws` expressions fail to compile. The Rust output recompiles with the original executable instructions, including `checkNotNull` and the exception table. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestTryVar` | Kotlin rejects the upstream `java.lang.Throwable` catch and the `.intValue()` arithmetic spelling. The Rust output recompiles with the original local initialization, operand evaluation, boxing, and exception tables. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestTrySplit` | Kotlin rejects the upstream `getMessage()` calls, `break label27`, and Java `Throwable` spelling. The Rust output preserves both labelled `run` exits and the exception dispatch. The recompiled instruction and handler offsets agree after rebasing two omitted `nop` instructions. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestTryCatchExpressions` and `kotlin/Entire Classpath/KOTLIN/pkg/TestTryFinallyExpressions` | Kotlin 2.0 rejects several generated bodies in the upstream reference, including `getMessage()` and JVM-only `StringsKt.repeat` calls. The Rust output restores typed try results and recompiles with the original Kotlin and JVM target. The original and rebuilt execution logs agree across ordinary calls and injected failures. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestTryReturn` | Kotlin 2.0 rejects the upstream boxed Boolean return, the `RuntimeException` cause cast, and the Java label syntax. The Rust output preserves platform null checks, exception wrapping, and exits through nested `finally` blocks. The 3,762 calls to the fixture's 14 deterministic methods produced identical result and exception traces. Separate runs of the random loop agreed on overload selection, exception handling, and cleanup transfers. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestDestructors` | Kotlin 2.0 rejects the upstream raw `List`, `Unit.INSTANCE`, inaccessible `KotlinNothingValueException`, and static spelling of extension components. The Rust output recompiles and agrees on callback order, overloads, and exceptions across 984 calls. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestCompileTimeErrors` | The upstream source omits the original suppressions for multiple bounds and the incompatible property override, and exposes default constructor arguments for `NotImplementedError`. The Rust output recompiles with the original diagnostics suppressed. Its nested bounds, anonymous binary name, primitive and boxed bridge dispatch, and tested runtime behavior agree. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestSmartCasts` | Kotlin 2.0 rejects the upstream `java.lang.String` return cast, raw `Pair` tests and accessor calls, and `charAt` spelling. The Rust output uses Kotlin types and expressions, retains the `DefaultImpls` ABI and original print overloads, and recompiles on the original toolchain. The original and rebuilt classes agree across 420 sampled calls after normalizing JVM-generated identity hashes. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestKotlinTypes` | Kotlin 2.0 rejects the upstream `Unit.INSTANCE` expression. The Rust output uses a typed Kotlin lambda and recompiles with matching JVM method signatures, instructions, and lambda bootstrap arguments. The sampled print, return, and exception behavior agrees. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestAnonymousEverything` | Kotlin 2.0 rejects the upstream Java metadata array syntax and local class declarations using `extends` and `implements`. The Rust output recompiles to the original eight binary class names. The tested reflection signatures, bridge calls, exceptions, and serialized lambda bytes agree. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestParams` | Kotlin 2.0 rejects the upstream exposed default-argument helper. Its receiver-first printing calls also select `PrintStream.println(String)` when rebuilt in isolation. The Rust output restores the defaults and preserves the original `PrintStream.println(Object)` calls. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestInfixFun`, `TestFunVarargs`, and `TestTailrecFunctions` | Kotlin 2.0 rejects the upstream synthetic helper calls and `JvmStatic` placement, unspread varargs and array `length`, and assignments to immutable parameters, respectively. The Rust sources recompile with matching tested signatures and runtime behavior. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestConvertedK2JOps` | The upstream source uses unresolved JVM facade names for Kotlin collection functions and an incompatible Java `String` initializer. The Rust output recompiles to the original collection initializers, accessor calls, and printing descriptor. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestAnnotations` | Kotlin rejects the upstream explicit repeatable annotation container and `[@...]` uses. The Rust output preserves runtime annotation values and ordering, and Kotlin regenerates the original container. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestEnumClass` | The upstream enum entries expose compiler-generated default argument masks and marker arguments. The Rust output restores the source defaults and recompiles to the original executable instructions and descriptors. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestVars` | Recompiling the upstream source selects `PrintStream.println(String)` in `testVar` and `testVal`, and `PrintStream.println(Object)` in `testPhi`. The Rust output preserves the original `Object`, `Object`, and `int` descriptors. The difference is observable when a replacement `PrintStream` overrides those methods. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestWhenBoolean` | The reference resolves a print to `PrintStream.println(String)`. The fixture and Rust rebuild use `println(Object)` and propagate an injected exception from that override. Kotlin 2.0 reproduces all 91 instructions and offsets in the Rust rebuild. |
| `kotlin/Entire Classpath/KOTLIN/pkg/TestKt`, `TestStringInterpolation`, and `kotlin/Entire Classpath/KOTLIN_OLD/pkg/TestClassicStringInterpolation` | The upstream printing expressions recompile to `PrintStream.println(String)`. The Rust output recompiles to the original `PrintStream.println(Object)` in all three cases. |
| `kotlin/Multifile Facade/KOTLIN/pkg/TestMultifile__TestMultifileA` and `kotlin/Multifile Facade/KOTLIN/pkg/TestMultifile__TestMultifileB` | The upstream printing calls recompile to `PrintStream.println(String)`. The Rust output recompiles to the original `PrintStream.println(Object)` in both file parts. |
| `core/Default/SCALA/pkg/TestCompanionObject` and `scala/Entire Classpath/SCALA/pkg/TestCompanionObject` | The original bridge invokes the default method nonvirtually. The upstream call dispatches to overrides when recompiled. The Rust output returns the verified default value for a nonnull receiver and preserves the null-receiver exception and diagnostic. |
| `scala/Entire Classpath/SCALA/pkg/TestDefaultParams`, `TestImplicits`, and `TestAssocTypes` | Java rejects the upstream `import scala.Predef.;` and bare `.MODULE$` syntax. The Rust output uses the Scala module's Java binary name. The explicit `IntShuffler.shuffle(Object)` bridge preserves its descriptor and tested dispatch. Java recompilation changes its bridge and synthetic reflection flags. |

Scala `EnumLike` contains static forwarders named `hashCode()` and `toString()`
that Java rejects because those signatures are instance methods of `Object`.
`AddMonoid` and `MulMonoid` each have both `id()I` and `id()Ljava/lang/Object;`.
Java source cannot declare both methods in one class. These declarations still
need a representation that preserves their JVM ABI.

Anonymous class ordering uses a complete sequence of attached anonymous classes
and preserves the declaration order of fields and the execution order of static
initializers. Independently terminal switch arms can also preserve their
anonymous allocation order. A partial sequence, conflicting order, or repeated
allocation spread across member fragments can still change binary names on
recompilation.
Recompilation checks preserve the runtime annotations on ordinary and qualified
allocations, the anonymous supertype, and allocations in a lambda helper.
Generic constructor annotations also use proven type arguments from field,
local, and method signatures. In an erased return or local context, an
unbounded no-argument construction can use `Object` to retain direct
type-argument annotation paths. More complex paths still need a source type.

### Inputs rejected by the JVM

These original inputs remain visible in the strict unsupported count. Loading
them with `java -Xverify:all` produced the following failures.

| Original fixture | JVM failure |
| --- | --- |
| `core/Default/JASM/pkg/TestSelfIterableLoop` | `VerifyError` at the `ifeq` in `testMethod`. The branch target at offset 38 lacks a stack-map frame. Recomputing frames in a scratch copy also exposes a `NoClassDefFoundError` for the unchanged `Ljava/lang/Iterable` operand. |
| `core/Default/JASM/pkg/TestInheritanceChainCycle` | `ClassCircularityError`. The class file names itself as its superclass. |
| `core/Default/JASM/pkg/TestCondy` | `VerifyError` in `testGetStaticFinal`. Its `areturn` has an `Integer` on the stack and the method declares `Class`. |
| `core/Complex Condys/JASM/pkg/TestComplexCondy` | `VerifyError` in `<clinit>`. Execution can fall through the end of the method body. |

### Kotlin companion input

The upstream `TestVarReplace` registration supplies `TestVarReplaceKt.class`.
The private `Constants` object from the same Kotlin file supplies six fields in
`Constants.class`. Two Kotlin 2.0 compilations with different `LN2` initializers
produced byte-identical facades and different results for `asinh(1e100)`. The
isolated case remains in the strict unsupported count. Kotlin 2.0 also rejects
the reference output's access to the file-private object and its JVM-only
`INSTANCE` spelling.

With both class files supplied as source inputs, the Rust CLI emits one
`TestVarReplace.kt`. Directory and archive inputs retain the verified companion
when `--only=pkg/TestVarReplace` selects the facade. `--add-external` continues
to supply classpath metadata. Kotlin 2.0 recompilation reproduces all 79
`asinh` instructions and offsets, the companion initializer and accessors,
and both classes' declaration signatures. All 4,156 sampled inputs produced
identical IEEE 754 result bits.
