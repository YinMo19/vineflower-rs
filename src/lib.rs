//! Native JVM class-file reader and Java source decompiler.

pub mod bytecode;
pub mod cfg;
pub mod classfile;
pub mod classpath;
mod context;
pub mod descriptor;
mod emit;
pub mod frontend;
mod hierarchy;
mod idea_notnull;
pub mod javadoc;
pub mod kotlin;
pub mod legacy;
mod lift;
pub mod naming;
mod options;
mod source_text;
mod structure;

pub use context::{ClassGroup, ClassGroupBuilder};
pub use emit::{DecompileError, MethodMap, Source, SourceMap, decompile, decompile_group};
pub use javadoc::{Javadoc, JavadocProvider, JavadocStyle, JavadocTarget};
pub use options::{OptionError, Options};
