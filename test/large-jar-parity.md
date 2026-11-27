# Large Java JAR parity

On November 27, 2026, seven of eight Maven Central artifacts completed with default settings in both the Rust CLI and the official Vineflower 1.12.0 Java CLI. Of 9,599 emitted Java files across those seven artifacts, 9,592 matched byte for byte (99.93%). All 344 resources matched. File and directory paths also matched. Rust also finished Elasticsearch with default settings and recovered `InternalEngine.closeNoLock`. The upstream default run timed out, so the full Elasticsearch output is excluded from the parity percentage.

## Default directory output

| Input | Entries ending in `.class` | Of which multi-release | Identical / emitted Java files | Differing Java files | Identical resources |
| --- | ---: | ---: | ---: | ---: | ---: |
| Apache Lucene Core 9.12.1 | 2,514 | 38 | 1,086 / 1,086 | 0 | 9 |
| H2 Database 2.3.232 | 1,055 | 1 | 776 / 777 | 1 | 5 |
| Eclipse Java Compiler (ECJ) 3.39.0 | 797 | 0 | 549 / 550 | 1 | 102 |
| Apache Calcite Core 1.38.0 | 4,343 | 0 | 1,668 / 1,672 | 4 | 11 |
| Apache Kafka Clients 3.9.0 | 3,842 | 0 | 1,808 / 1,808 | 0 | 192 |
| Apache Hadoop Common 3.4.1 | 2,625 | 0 | 1,197 / 1,198 | 1 | 16 |
| Bouncy Castle Provider 1.79 | 5,579 | 1,157 | 2,508 / 2,508 | 0 | 9 |
| Elasticsearch Server 8.17.0 | 8,563 | 0 | Rust emitted 4,082. Upstream timed out. | — | — |

The class counts include nested classes and entries under `META-INF/versions/`. Both CLIs use the base classes for these inputs by default. Nested classes commonly share one source file with their enclosing class. The counts above describe the emitted sources. The comparison also scanned sources for class, method and lambda decompilation failure comments.

## What differed

| Artifact | Source file | Difference |
| --- | --- | --- |
| H2 | `org/h2/mvstore/MVStore.java` | Rust adds `(M)` to the return of `openMap`. |
| ECJ | `org/eclipse/jdt/internal/compiler/apt/model/ElementImpl.java` | Rust adds `(A)` around the conditional return in `getAnnotation`. |
| Calcite | `org/apache/calcite/sql/SqlCallBinding.java` | Rust adds one `(T)` to a recursive return in `valueAs`. |
| Calcite | `org/apache/calcite/sql2rel/SqlToRelConverter.java` | Rust adds `(R)` to three recursive returns in `convertSortExpression`. |
| Calcite | `org/apache/calcite/rel/rules/DateRangeRules.java` | Rust omits the unreferenced `label117:` on a switch after correcting assertion control flow. |
| Hadoop | `org/apache/hadoop/crypto/key/kms/KMSClientProvider.java` | Rust adds `(T)` to the retry return in `call`. |
| Calcite | `org/apache/calcite/adapter/jdbc/JdbcUtils.java` | Both fail to recover `value(int)` in `ObjectArrayRowBuilder1` and `ObjectArrayRowBuilder2`. Their diagnostic comments differ. The fallback bytecode listings match. |

`javap` shows the relevant calls returning directly in the input bytecode. Recompiling each version of ECJ's `ElementImpl.java` against its original JAR with JDK 25.0.2, `-proc:none -g:none`, produced byte-identical class files. Both versions of H2's `MVStore.java` failed to recompile at the same two other lines. The comparison did not recompile the eight projects. Across the seven completed default comparisons, `DateRangeRules.java` was the only file whose output changed from the published Rust `v0.1.2` binary.

Calcite's two methods switch on an element of an inherited `int[]` field. Both implementations fail when the enum-switch recognizer looks for the field declaration in the subclass. Repeating the comparison on the `JdbcUtils` class family with `calcite-linq4j:1.38.0` supplied as an external library reproduced both failures. These were the only failure markers in the seven completed default comparisons.

## Elasticsearch

Before the fix, both default runs timed out after 600 seconds while rendering source. In Rust, a diagnostic build traced the stall to `CompositeSyntheticFieldLoader.storedFieldLoaders()` while writing an anonymous-class constructor. Generic scope lookup mistook an interface method reference with the same name and descriptor for an enclosing lambda body. It then kept selecting the method reference as its own enclosing scope. A thread dump of the unmodified upstream CLI showed its remaining active worker in the corresponding generic-context loop in `ClassWriter.writeMethod`.

Rust now follows the enclosing lambda's implementation when recovering the scope of a local or anonymous class. Once there, it uses the parent recorded during lambda discovery. On the full original JAR, the fixed release build finished in 3.89 seconds in one default run and emitted 4,082 Java files and 26 resources. The emitted `CompositeSyntheticFieldLoader.java` retained its generic return type and compiled with JDK 25.0.2 using `javac --release 21 -proc:none`, the input JAR, Lucene Core 9.12.0, Elasticsearch Core 8.17.0 and Elasticsearch X-Content 8.17.0.

At that stage, all 4,081 other source files and 26 resources matched the pre-fix Rust output on identical split inputs. Both CLIs still emitted a bytecode listing for `InternalEngine.closeNoLock(String, CountDownLatch)`.

### Recovering `InternalEngine.closeNoLock`

Recovering an `assert` followed by a surviving branch moved the enclosing conditional's exit edge onto the assertion itself. In this method that edge bypassed all cleanup. A later rewrite then removed the empty destination block when it inverted the outer conditional. Rust now keeps the exit on the entire assertion-and-branch sequence. It also checks for other incoming edges before removing an empty branch.

On the full Elasticsearch 8.17.0 JAR, only `InternalEngine.java` changed from the build with the generic-scope fix. All 4,082 generated sources were free of decompilation failure markers. We extracted the generated method and the corresponding method from Elasticsearch's published sources, compiled each against the same instrumented dependencies, and compared their behavior. The cleanup order, escaping exception, closed flag and latch count matched for all 84 calls across 21 scenarios, with assertions enabled and disabled, on both the first and second call. The scenarios included reader and translog failures, rollback errors and exceptions during cleanup. To run the standalone Java regression with a JDK, use `cargo test --locked --test driver guarded_nested_finally_preserves_cleanup_and_exception_paths -- --ignored`.

| Supplementary comparison | Identical / emitted Java files | Identical resources | Difference |
| --- | ---: | ---: | --- |
| Full original JAR with `--decompile-generics=0` on both CLIs | 4,081 / 4,082 | 26 / 26 | Rust recovers `InternalEngine.closeNoLock`. Upstream emits bytecode. |
| Default options on the other 8,557 class entries, with the six `CompositeSyntheticFieldLoader` family entries supplied as an external JAR | 4,080 / 4,081 | 26 / 26 | Same method |

Disabling generic signatures changes the source output and was used only in the supplementary comparison.

## Inputs and reproduction

The host was an Apple M4 Pro with 14 cores, macOS and JDK 25.0.2. The pre-fix Rust binary was built with `cargo build --release --locked --bin vineflower-rs` from `c7a8134` plus the graph reuse, variable-version snapshots and expression traversal changes described in the [performance measurements](README.md#direct-graph-reuse-and-variable-version-snapshots). Its local SHA-256 was `8a2ec387ce9d3f136d50fdf919690b7df05a2bc2a662fa9ce8944327339504d9`. With the generic-scope fix the binary had SHA-256 `496ea8424dcfd38296ce208d11fb994001574d52710f015ad068a5cd1a841a46`. After both fixes the binary had SHA-256 `17ee9f3e631a53c977afb30a92acf85e9fd6f65e5ce927d0bb5b5cfb049fb21c`.

The reference came from [Vineflower 1.12.0 on Maven Central](https://repo.maven.apache.org/maven2/org/vineflower/vineflower/1.12.0/vineflower-1.12.0.jar), SHA-256 `1dfcfe974395734fa467ce620661c7623d05ba83670de0529b1fbd63ff548b9d`. Each input was checked against its published Maven Central checksum. The default runs passed only the input JAR and a fresh output directory, with no extra libraries, an unset `CLASSPATH`, the default thread settings and the same JDK. Decompiler logs were captured separately. Source and resource comparisons used relative paths and raw bytes without normalization.

| Maven Central artifact | Input SHA-256 |
| --- | --- |
| [org.apache.lucene:lucene-core:9.12.1](https://repo.maven.apache.org/maven2/org/apache/lucene/lucene-core/9.12.1/lucene-core-9.12.1.jar) | `8d812e9fa6dbd816808205e6cb4d7ab43a747e379c8cb31a0d6dc91050b3f97a` |
| [com.h2database:h2:2.3.232](https://repo.maven.apache.org/maven2/com/h2database/h2/2.3.232/h2-2.3.232.jar) | `8dae62d22db8982c3dcb3826edb9c727c5d302063a67eef7d63d82de401f07d3` |
| [org.eclipse.jdt:ecj:3.39.0](https://repo.maven.apache.org/maven2/org/eclipse/jdt/ecj/3.39.0/ecj-3.39.0.jar) | `01f5a92ac19bb2b3bf85e295a68f2c73c264369109158b566ce9b490af982948` |
| [org.apache.calcite:calcite-core:1.38.0](https://repo.maven.apache.org/maven2/org/apache/calcite/calcite-core/1.38.0/calcite-core-1.38.0.jar) | `b55427c5e98fdc59e4722062d1414b18db3bc08998a00f42959751200ff09624` |
| [org.apache.kafka:kafka-clients:3.9.0](https://repo.maven.apache.org/maven2/org/apache/kafka/kafka-clients/3.9.0/kafka-clients-3.9.0.jar) | `15c1e137f2c2c94398e27abc4060a03b6bde10bf9fac15e8f70c02320b202f18` |
| [org.apache.hadoop:hadoop-common:3.4.1](https://repo.maven.apache.org/maven2/org/apache/hadoop/hadoop-common/3.4.1/hadoop-common-3.4.1.jar) | `85ab34eb0efc42651290991473341fc77491de2e0cfa7f2d02d20c57abed3aeb` |
| [org.bouncycastle:bcprov-jdk18on:1.79](https://repo.maven.apache.org/maven2/org/bouncycastle/bcprov-jdk18on/1.79/bcprov-jdk18on-1.79.jar) | `0d81ecc3124536b539bce9aa3fe9621b7f84c9cee371b635a5b31c78b79ab1da` |
| [org.elasticsearch:elasticsearch:8.17.0](https://repo.maven.apache.org/maven2/org/elasticsearch/elasticsearch/8.17.0/elasticsearch-8.17.0.jar) | `7fa7ca14deac6aa95f0be25792b15841d353937029828b6f4c8d24751cd6769f` |

To repeat one comparison, set `JAVA_HOME` to the JDK and `input` and `upstream` to the downloaded JAR paths, then run these commands from the Rust repository.

```sh
work=$(mktemp -d)
mkdir "$work/java" "$work/rust"
"$JAVA_HOME/bin/java" -jar "$upstream" "$input" "$work/java" >"$work/java.log" 2>&1
target/release/vineflower-rs "$input" "$work/rust" >"$work/rust.log" 2>&1
diff -qr "$work/java" "$work/rust"
```
