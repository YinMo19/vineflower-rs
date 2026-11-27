# Usage and Development Guide

`vineflower-rs` decompiles JVM bytecode to Java or Kotlin source. The command-line tool and Rust library accept individual class files, directories, JARs, and ZIP archives. The reference implementation is Vineflower 1.12.0 at commit `b8273988af850e8cfb234ca08d129058502b032f`. Output comparisons use the same input classes, dependencies, options, and plugins on both implementations. They cover source text, line mappings, and CLI behavior. [Upstream revision](https://github.com/Vineflower/vineflower/tree/b8273988af850e8cfb234ca08d129058502b032f)

## Build and decompile a class

Run these commands from the repository root with a stable Rust toolchain that supports the 2024 edition. The project has been tested with Rust 1.95.0. The examples below reuse `vf` and the temporary directory `work` in the same shell.

```sh
cargo build --release --locked
vf="$PWD/target/release/vineflower-rs"
work=$(mktemp -d)
"$vf" test/smoke/java16/TestRecordSimple.class "$work/record"
cat "$work/record/TestRecordSimple.java"
```

The standalone class produces a file directly under the destination. Its package declaration stays in the source.

```java
package pkg;

public record TestRecordSimple(int x, int y) {
}
```

The same CLI detects Kotlin metadata. With a single input and no destination, it prints a filename header followed by the source. Normal logs also go to stdout. Use `--log-level=ERROR` for a quieter preview, or supply a destination to get source files you can open in an editor.

```sh
"$vf" --log-level=ERROR test/smoke/kt/TestParams.class
"$vf" -h
"$vf" --help
"$vf" --version
"$vf" --list-plugins
```

Use `-h` for a short option summary, `--help` for the full help from clap, and `--version` to see which build is on your PATH.

The plugin list contains VariableRenaming, Kotlin, and IdeaNotNull. The Kotlin plugin uses metadata to match declarations and types to their JVM members. IdeaNotNull can recognize checks inserted by IntelliJ IDEA for annotated parameters and return values. [CLI](src/bin/vineflower-rs.rs) · [Kotlin implementation](src/kotlin/mod.rs) · [IdeaNotNull pass](src/decompiler/idea_not_null.rs)

## Shell completions

Install `vineflower-rs` on your PATH first. If you built it locally, run `export PATH="$PWD/target/release:$PATH"` from the repository root in Bash or Zsh. The `completions` subcommand writes a script for the selected shell to standard output.

| Shell | Enable completion |
| --- | --- |
| Bash | Run `eval "$(vineflower-rs completions bash)"`. Add that line to `~/.bashrc` for future interactive sessions. |
| Zsh | After `autoload -Uz compinit && compinit`, run `source <(vineflower-rs completions zsh)`. Put the source line after completion initialization in `~/.zshrc`. |
| Fish | Run `mkdir -p ~/.config/fish/completions`, then `vineflower-rs completions fish > ~/.config/fish/completions/vineflower-rs.fish`. Fish loads the file on demand. If you use a custom XDG configuration directory, use the `completions` directory under `$__fish_config_dir`. |
| PowerShell | Run `vineflower-rs completions powershell \| Out-String \| Invoke-Expression`. Add that line to your PowerShell profile (`$PROFILE`) to register it at startup. |
| Elvish | Run `eval (vineflower-rs completions elvish \| slurp)` in an interactive shell. Add that line to your Elvish `rc.elv` for future sessions (usually `~/.config/elvish/rc.elv` on Unix). |

To check, type `vineflower-rs --thread-cou` and press **Tab**. The shell should offer or insert `--thread-count`. In Fish you can also run `complete -C 'vineflower-rs --thread-cou'`. Regenerate saved scripts after upgrading the CLI.

## Archives, resources, and dependencies

To expand an existing JAR, run `"$vf" app.jar out/`. To try this with a bundled fixture, use the JDK's `jar` tool to give the class its package path and add a resource. The same archive can then be written to a source directory or to a ZIP.

```sh
mkdir -p "$work/input/pkg"
cp test/smoke/java16/TestRecordSimple.class "$work/input/pkg/"
printf 'sample resource\n' > "$work/input/example.txt"
jar cf "$work/sample.jar" -C "$work/input" .
"$vf" --folder "$work/sample.jar" "$work/sources"
cat "$work/sources/pkg/TestRecordSimple.java"
cmp "$work/input/example.txt" "$work/sources/example.txt"
"$vf" --file "$work/sample.jar" "$work/sources.zip"
jar tf "$work/sources.zip"
```

| Output | Invocation | Result |
| --- | --- | --- |
| Console preview | `"$vf" input.jar` | Prints each source with its entry name. Resources are omitted. |
| Directory | `"$vf" --folder input.jar out/` | Expands source and resources under `out/`, preserving package paths in the archive. |
| Source archive | `"$vf" --file input.jar sources.zip` | Writes a ZIP. Use one archive or directory input per invocation because each input unit recreates the destination archive. |
| Separate archives | `"$vf" --legacy-saving a.jar b.jar out/` | Places the decompiled archives in `out/a.jar` and `out/b.jar`, keeping the input filenames. |

Choose at most one explicit save mode. With multiple positional paths, the last path is the destination and the preceding paths are inputs. Select classes with an internal-name prefix such as `--only=com/example/`. The trailing slash prevents a match on `com/example2`. The filter applies to classes. Directory and archive saves still copy resources. [Argument parser](src/bin/vineflower-rs.rs) · [Output modes and resource copying](src/engine/driver/saver.rs)

Register dependencies separately from classes you want to decompile. Here the dependency supplies type information while the caller produces a source file. To supply several libraries, use `--add-external=lib/a.jar,lib/b.jar`.

```sh
"$vf" --thread-count=4 --add-external=test/smoke/java8/TestLibrary.class \
  --only=pkg/ test/smoke/java8/TestLibraryIsOnClasspath.class "$work/caller"
cat "$work/caller/TestLibraryIsOnClasspath.java"
```

Options can appear before or after input paths. Options with a required value accept a space or an equals sign. For example, `"$vf" input.jar --thread-count 4 --log-level=ERROR out/` writes sources to `out/`. Set a boolean with `--ascii-strings`, `--no-ascii-strings`, or an explicit value such as `--ascii-strings=0`. The positional paths keep their order. The upstream spellings `-thr=4`, `-e=lib/a.jar`, and `-only=pkg/` are also accepted. Use `--` before a filename that starts with a dash, as in `"$vf" -- --input.jar out/`.

A configuration file expands in place with `--config PATH` or the legacy `-cfg PATH`. Put each argument, including each separate option value, on its own line. Paths containing spaces fit on one line without shell quotes.

```sh
printf '%s\n' '--thread-count=1' '--log-level=ERROR' '--only=pkg/' \
  "$work/sample.jar" "$work/config-out" > "$work/args.txt"
"$vf" --config "$work/args.txt"
cmp "$work/sources/pkg/TestRecordSimple.java" "$work/config-out/pkg/TestRecordSimple.java"
```

The native process reads type information directly from a JDK. The default `--include-runtime=1` checks a valid `JAVA_HOME`, then the Java launcher on `PATH`, then the system JDK locator on macOS. To pin a particular standard library, use `--include-runtime=/path/to/jdk` with the default `--include-classpath=0`. Enabling `--include-classpath=1` registers class files and JARs listed in `CLASSPATH` and selects the host runtime. [Runtime discovery](src/engine/driver/runtime.rs) · [Option defaults](src/engine/options.rs)

## Embed the Rust library

If the application and this repository are sibling directories, run `cargo add --path ../vineflower-rs` in the application. The package name is `vineflower-rs` and its Rust import name is `vineflower_rs`. This example `src/main.rs` takes an input, an output directory, and an optional dependency.

```rust
use std::{env, io};
use vineflower_rs::engine::{
    Options,
    driver::{Decompiler, Output},
};

fn main() -> io::Result<()> {
    let mut args = env::args_os().skip(1);
    let usage = || io::Error::new(io::ErrorKind::InvalidInput, "usage: app INPUT OUT [LIB]");
    let input = args.next().ok_or_else(usage)?;
    let output = args.next().ok_or_else(usage)?;
    let mut options = Options::default();
    options.decompile_kotlin = true;
    options.idea_notnull = true;

    let mut decompiler = Decompiler::new(options)?;
    if let Some(library) = args.next() {
        decompiler.add_library(library)?;
    }
    decompiler.add_source(input)?;
    decompiler.save(Output::Folder(output.into()))
}
```

From the application directory, run `cargo run -- "$work/sample.jar" "$work/library-out"`. The example explicitly enables the Kotlin and IDEA plugins to match the CLI defaults. Call `add_source` and `add_library` repeatedly to register inputs that share classpath lookups and nested-class discovery. [Public driver API](src/engine/driver/mod.rs)

For an editor or analysis tool, set `options.bytecode_source_mapping = true` before constructing the decompiler, then replace the final `save` call with the following code.

```rust
for unit in decompiler.decompile()? {
    println!("{} -> {}", unit.qualified_name, unit.entry_name);
    if let Some(mapping) = &unit.mapping {
        for pair in mapping.chunks_exact(2) {
            println!("original line {} -> generated line {}", pair[0], pair[1]);
        }
    }
    println!("{}", unit.source);
}
Ok(())
```

`decompile()` returns a `Vec<DecompiledClass>` with one entry per emitted root class. Each entry carries its JVM internal name (`qualified_name`), output path (`entry_name`), source string, and optional mapping. Each pair of integers maps a line in the original source to a line in the generated source, both one-based. Use `save()` when the result needs to include resources. Both methods consume the session. For class bytes already in memory, the driver tests demonstrate `MemorySource`, `add_source_context`, a read-only library, and mapping retrieval. [Memory input](src/engine/driver/memory.rs) · [Driver examples](test/driver.rs)

## Follow a class through the implementation

For a change inside one method, start at the method processor to see when its passes run. For missing imports, enclosing instances, or field initializers, start at root-class preparation and class writing. [Method processor](src/engine/method_processor.rs) · [Class processor](src/engine/class_processor.rs) · [Architecture notes](ARCHITECTURE.md)

| Stage | What happens | Source |
| --- | --- | --- |
| Read classes and libraries | Parse constant pools, fields, methods, and attributes. Register classpath entries and build the root and nested class relationships. Member renaming uses the class and interface hierarchies. | [Class format](src/structs/mod.rs) · [Types](src/types/mod.rs) · [Renaming](src/renamer/mod.rs) |
| Construct the control-flow graph | Decode instructions and exception tables, split methods into basic blocks, connect edges, and clean up the graph. | [Instructions](src/code/mod.rs) · [Control-flow graph](src/code/cfg/mod.rs) |
| Recover statements and expressions | Recognize loops, conditionals, switches, catches, and finally blocks. Simulate the operand stack to lift bytecode instructions into expressions. | [Statement decomposition](src/decompiler/decompose/mod.rs) · [Finally recovery](src/decompiler/finally/mod.rs) · [Expressions](src/decompiler/exps/mod.rs) |
| Analyze data flow and rewrite methods | Track definitions and uses through the direct graph, simplify stack variables, recover higher-level constructs such as switch expressions and try-with-resources, and place local declarations. | [Direct graph](src/decompiler/flow/mod.rs) · [SSA and SSAU](src/decompiler/sforms/mod.rs) · [Variables](src/decompiler/vars/mod.rs) |
| Recover and write a compilation unit | Combine methods and nested classes to recover captures, field initializers, and imports. Kotlin uses metadata and additional method passes to reconstruct declarations and bodies. | [Java writer](src/engine/class_writer/mod.rs) · [Kotlin metadata](src/kotlin/metadata/mod.rs) · [Kotlin passes](src/kotlin/passes/mod.rs) · [Kotlin writer](src/kotlin/writer/mod.rs) |
| Save results | Finalize text and mappings, emit classes in input order, and handle resources according to the output mode. | [Text buffer](src/util/text_buffer.rs) · [Driver](src/engine/driver/mod.rs) |

Graph nodes have stable handles in the intermediate representation. These let a developer follow a statement or a shared expression through a rewrite and compare it with the corresponding Java stage. For Kotlin metadata changes, the repository also contains a generator and its pinned schema inputs. [IR storage](src/decompiler/ir.rs) · [Kotlin metadata binding generation](tools/kotlin-schema/README.md)

### Parallel processing

The default worker count comes from the logical processors available to the process. `--thread-count=N` or `-thr=N` supplies a positive worker budget, `1` selects sequential processing, and zero or a negative value restores automatic selection. For a single input unit with independent Java roots, the driver groups roots that share nested constructor state, local or anonymous class references, or enum switch maps. It estimates the cost of each group from method bytecode sizes and uses Rayon to prepare and write groups in parallel. The driver emits results in the original order. This path is enabled by default. [Group scheduling](src/engine/driver/class_groups/mod.rs) · [Dependency checks](src/engine/driver/class_groups/dependencies.rs)

Workers share parsed classes and the classpath. Each group has its own method graphs, class wrappers, and import scopes. Multiple input units, mixed Kotlin input, explicit references to synthetic lambda names, and some dynamic-constant expansions use a shared class tree. On that path workers can still prepare methods ahead of time. The coordinator checks any class lookups that may have changed before publishing prepared methods and rendering in order. When investigating a discrepancy that depends on parallelism, repeat the same invocation with `-thr=1` and keep input and dependency order fixed. [Shared preparation](src/engine/driver/prepare.rs) · [Method graph ownership](ARCHITECTURE.md)

## Run tests and investigate output differences

The default suite uses bundled bytecode and reference outputs. Run it from the repository root, or choose a target that covers the code you changed.

```sh
cargo test --locked
cargo test --locked --test control_flow --test structured_flow
cargo test --locked --test driver
cargo test --locked --test kotlin_body
cargo test --locked --test upstream_parity
```

`test/smoke` contains precompiled inputs, `test/upstream` holds the original reference files, and `test/registrations.tsv` records individual cases and their options. The driver tests cover library and CLI behavior, resources, output order, dependencies, and mappings. The flow targets can compare intermediate graphs. [Smoke classes](test/smoke) · [Upstream fixtures](test/upstream) · [Case registrations](test/registrations.tsv) · [Test documentation](test/README.md)

**Compare intermediate stages with Java.** Prepare a checkout of the pinned upstream revision, JDK 17 or later, and the toolchains for its fixture groups. These commands assume the checkout is at `../vineflower`. They build the distribution with its plugins and compile the core, Kotlin, and variable-renaming fixtures.

```sh
export VINEFLOWER_UPSTREAM="$(cd ../vineflower && pwd)"
(cd "$VINEFLOWER_UPSTREAM" && ./gradlew :allJar :testDataClasses :kotlin:testDataClasses :variable-renaming:testDataClasses)
export VINEFLOWER_RS_CLASS_ROOT="$VINEFLOWER_UPSTREAM"
cargo test --locked --test class_nodes --test control_flow --test structured_flow --test driver \
  -- --include-ignored --nocapture
```

**Run the full upstream parity suite.** The 697 active cases comprise 688 single-class registrations, two bulk cases, six CLI cases, and one lazy-library case. The test guide lists the JDKs used by each fixture group (8, 9, 11, 16, 17, 21, and 25), environment variables, and required precompiled inputs for other languages. The Scala plugin needs a separate fixture build because the pinned default Gradle settings omit that subproject. The Entire Classpath registrations need upstream runtime libraries on `CLASSPATH`, including Kotlin 2.0.0.

```sh
cargo test --locked --test upstream_parity full_parity -- --ignored --nocapture
# Run the CLI cases only.
VINEFLOWER_RS_PARITY_FILTER=cli/ cargo test --locked --test upstream_parity full_parity -- --ignored --nocapture
```

In the recorded full run, 694 of 697 cases matched the stored reference outputs. The three Scala cases were `TestCaseClasses`, `TestObject`, and `TestCompanionObject`. Given the same input and options, the pinned Java CLI and the Rust CLI agreed with each other on all three and differed from the stored Scala outputs. [Full-suite setup and comparison rules](test/README.md#end-to-end-source-and-cli-suite)

**Investigate a mismatch.** Use identical class files, siblings and inner classes, dependency order, options, and reference JDK. Compare output directories with `diff -qr`, locate the affected method, then look for the earliest difference in its control-flow graph, statement tree, expressions, or variable versions. To check recompilation or execution, compile the generated sources with the matching compiler and dependencies, then run the original entry point or tests. The distinction matters in the recorded five-library comparison on JDK 17. Of 1,024 generated Java files, 1,023 matched byte for byte. The remaining Guava file differed in how U+FDFF was escaped. Recompiling all 36 generated ASM files produced the same 28 compiler errors in both implementations. [Independent library checks](test/README.md#independent-java-libraries)

## Benchmark results and reproduction

These measurements used a 14-core Apple M4 Pro and JDK 25.0.2. The Rust release executable and the pinned Java 1.12.0 CLI each received only the input JAR and a fresh output directory. Each ran in a new process with default logging redirected to files, default mappings and worker count, and the default JVM heap. Each implementation ran once to warm the filesystem. Three timed pairs followed in Rust/Java, Java/Rust, Rust/Java order. The reported medians include startup and resource copying.

| Input | Java files | Other files | Rust | Java Vineflower | Speedup |
| --- | ---: | ---: | ---: | ---: | ---: |
| Minecraft 26.3 full client | 7,301 | 21,495 | 7.75 s | 15.91 s | 2.05× |
| Guava 33.3.1-jre | 627 | 11 | 0.724 s | 3.266 s | 4.51× |
| Gson 2.11.0 | 83 | 4 | 0.161 s | 0.889 s | 5.54× |

Relative paths and file bytes matched across both implementations on all three inputs. The Minecraft client SHA-256 was `4508d006323f24fa02876310c192d739af56516eb259000ac50f0909a68c9a2d`. Separate native runs took 13.43 s with four workers and 37.24 s with one. In an instrumented default run, copying resources and preparing directories took 1.55 s, processing Java class groups took 5.25 s, and writing the final Java files took 0.51 s. [Individual runs and timing breakdown](test/README.md#default-cli-and-rayon-class-groups)

To compare outputs on your machine, start with the sample archive built above and then point `input` at the JAR you want to measure. Set `JAVA_HOME` to the selected JDK and use the upstream distribution built above. This script compares each directory with the Java warm-up output after timing the process. It retains the outputs and logs, so allow enough space for eight expanded copies.

```sh
input="$work/sample.jar"
oracle="$VINEFLOWER_UPSTREAM/build/libs/vineflower-1.12.0+local.jar"
python3 - "$vf" "$JAVA_HOME/bin/java" "$oracle" "$input" "$work" <<'PY'
from pathlib import Path
from statistics import median
from subprocess import STDOUT, run
from tempfile import mkdtemp
from time import perf_counter
import sys

native, java, oracle, source, work = sys.argv[1:]
root = Path(mkdtemp(prefix="bench-", dir=work))
commands = {"rust": [native], "java": [java, "-jar", oracle]}
times = {"rust": [], "java": []}
orders = [("rust", "java"), ("rust", "java"), ("java", "rust"), ("rust", "java")]
for index, order in enumerate(orders):
    for name in order:
        output = root / f"{index}-{name}"
        output.mkdir()
        with output.with_suffix(".log").open("wb") as log:
            start = perf_counter()
            run([*commands[name], source, output], stdout=log, stderr=STDOUT, check=True)
            elapsed = perf_counter() - start
        if index:
            times[name].append(elapsed)
    run(["diff", "-qr", root / "0-java", root / f"{index}-rust"], check=True)
    run(["diff", "-qr", root / "0-java", root / f"{index}-java"], check=True)
for name, measurements in times.items():
    print(f"{name}: {median(measurements):.3f} s")
print(f"logs and outputs: {root}")
PY
```

## Licenses

The [project README](README.md) collects the copyright notices and links to the license texts for the port, its upstream test fixtures, and the bundled `jimage-rs` library.
