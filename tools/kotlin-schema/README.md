# Generate the Kotlin JVM metadata bindings

Vineflower 1.12.0 uses the Kotlin 2.2.20 metadata library, with package
relocation and removal of unused Java APIs. The Rust parser uses Prost
bindings generated from these JetBrains sources at tag `v2.2.20`.

- [Core metadata schema](https://github.com/JetBrains/kotlin/blob/v2.2.20/core/metadata/src/metadata.proto)
- [JVM metadata schema](https://github.com/JetBrains/kotlin/blob/v2.2.20/core/metadata.jvm/src/jvm_metadata.proto)
- [Imported descriptor options](https://github.com/JetBrains/kotlin/blob/v2.2.20/core/metadata/src/ext_options.proto)

From the root of this repository, use a Kotlin checkout at that tag and
a Protocol Buffers installation that includes the standard `.proto` files.

```sh
kotlin_schema_root=/absolute/path/to/kotlin
kotlin_schema_descriptor="$(mktemp)"
protoc -I "$kotlin_schema_root" --include_imports \
  --descriptor_set_out="$kotlin_schema_descriptor" \
  core/metadata/src/metadata.proto core/metadata.jvm/src/jvm_metadata.proto
cargo run --locked --manifest-path tools/kotlin-schema/Cargo.toml -- "$kotlin_schema_descriptor"
rm "$kotlin_schema_descriptor"
```

If the standard protobuf includes have a separate installation path,
pass it to `protoc` with another `-I`.

The generator flattens JVM extensions onto the host messages at their
original field numbers. `Property.jvm_flags` distinguishes the extension
from the core flags field. The legacy type annotations use the same
field numbers as the annotation fields in Vineflower's optimized jar.
String-table literals retain the raw bytes stored by the Java runtime.
Vineflower 1.12.0’s bundled JAR tries to decode these bytes with a charset
named `Code`. The resolver reproduces the resulting failure.

Prost generates `proto.rs` and `jvm_proto.rs`. The generator presents
proto2 required fields to Prost as optional, preserving the distinction
between an absent field and its default value. It generates
`wire_checks.rs` separately from the original field descriptors to
validate required fields recursively and apply proto2 enum defaults.

Normal Cargo builds compile the checked-in Rust files. Only regeneration
uses the separate tool, a schema checkout, `protoc` and `rustfmt`.
