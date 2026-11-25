//! A Rust port of the Vineflower Java decompiler (upstream 1.12.0).
//!
//! The port follows upstream's algorithms, iteration orders and method-local
//! counters. The current Java method entry reaches the initial statement
//! graph via [`engine::method_processor::initial_statement_graph`].
//!
//! # Where things are
//!
//! | upstream package | module |
//! | --- | --- |
//! | `code`, `code.cfg`, `code.interpreter`, `modules.code` | [`code`] |
//! | `struct`, `struct.attr`, `struct.consts` | [`structs`] |
//! | `struct.gen`, `struct.gen.generics` | [`types`] |
//! | `modules.decompiler` and its subpackages, `struct.match` | [`decompiler`] |
//! | `modules.renamer` | [`renamer`] |
//! | `main`, `main.rels`, `main.collectors`, `main.extern`, `api` | [`engine`] |
//! | `util`, `util.collections`, `util.token` | [`util`] |
//!
//! A class `FooBarHelper` is the file `foo_bar_helper.rs`; small classes that
//! belong together share a file. A static method `Foo.doIt(a)` is the function
//! `foo::do_it(cx, a)`; fields and constants keep their names in Rust case;
//! overloads share a base name and differ by a suffix.
//!
//! # How upstream's idioms are expressed
//!
//! - **Ambient state.** What upstream reads from the thread-local
//!   `DecompilerContext` is passed as `cx: &mut Cx` ([`engine::Cx`]), always
//!   the first parameter.
//! - **Object identity.** Statements, edges, expressions, expression lists
//!   and basic blocks live in arenas inside `cx`; a `Copy` handle stands for
//!   the Java reference, so comparing handles is `==` on references and a
//!   change through one alias is seen through all. The ids upstream assigns
//!   from its counters are fields of the nodes, not the handles.
//! - **Class hierarchies** are enums of the subclasses' data; a virtual
//!   method is a function that matches on the kind and calls the subclass's
//!   function of the same name in that subclass's module.
//! - **Collections.** A `HashMap`/`HashSet` whose iteration order can reach
//!   the output uses [`util::jhash`] for JDK value-key bucket order. The
//!   module documents tree-bin limits. Linked and identity-keyed maps that
//!   require stable iteration use `indexmap`, sorted keys use `BTreeMap`,
//!   and lookup-only maps can use `rustc_hash`.
//! - **Exceptions.** A Java exception that ends the decompilation of a
//!   method is a panic, caught where upstream catches it; `IOException`s of
//!   class loading are `io::Result`s; a parser that upstream lets throw on
//!   malformed input returns `Option`.
//! - **Strings.** Names and descriptors are shared `ArcStr`s. Generated text
//!   is kept in UTF-16 ([`util::text_buffer`]) and [`util::java_str`] has
//!   the `String` operations whose results differ from Rust's.
//! - **Shared mutable descriptors.** Generic signatures that upstream
//!   corrects in place are [`types::SharedSignature`] cells.

pub mod code;
pub mod decompiler;
pub mod engine;
pub mod renamer;
pub mod structs;
pub mod types;
pub mod util;
