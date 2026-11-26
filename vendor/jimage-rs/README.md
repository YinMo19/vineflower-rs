# jimage-rs 0.0.5

This directory contains the library from [jimage-rs 0.0.5], published under
the MIT license at [commit 3204dcdc11ea7a0701bfb64cbe3befbb34cb5c4c].
The manifest omits the CLI and upstream test dependencies.

The native changes keep the existing mmap and resource index. They bound
index sections and resource ranges, read Modified UTF-8 resource names,
and decode the ZIP and compact constant-pool layers used by jlink. The
constant-pool decoder was implemented in Rust from the observed OpenJDK
wire format. It rebuilds class bytes from the image's string table.

[jimage-rs 0.0.5]: https://crates.io/crates/jimage-rs/0.0.5
[commit 3204dcdc11ea7a0701bfb64cbe3befbb34cb5c4c]: https://github.com/hextriclosan/rusty-jvm/tree/3204dcdc11ea7a0701bfb64cbe3befbb34cb5c4c/jimage-rs
