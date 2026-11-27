//! Upstream's `code` package: the bytecode instruction model, and the decoder
//! that builds it from a method's `Code` attribute.

pub mod bytecode_parser;
pub mod bytecode_version;
pub mod cfg;
pub mod code_constants;
pub mod dead_code_helper;
pub mod exception_deobfuscator;
pub mod exception_table;
pub mod instruction;
pub mod instruction_sequence;
pub mod interpreter;
pub mod method_properties;

pub use bytecode_version::BytecodeVersion;
pub use exception_table::{ExceptionHandler, ExceptionTable};
pub use instruction::{Instruction, InstructionKind, JumpInstruction, SwitchInstruction};
pub use instruction_sequence::{FullInstructionSequence, InstructionSequence};
pub use method_properties::MethodProperties;
