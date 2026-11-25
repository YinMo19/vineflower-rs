// SPDX-License-Identifier: Apache-2.0

//! Upstream's `modules.decompiler` packages: the statement and expression IR
//! and the passes that turn a control-flow graph into structured source.

pub(crate) mod assertions;
pub(crate) mod concat;
pub mod decompose;
pub(crate) mod exits;
pub mod expr_processor;
pub mod exps;
pub mod finally;
pub mod flow;
pub(crate) mod increments;
pub(crate) mod inline_blocks;
pub(crate) mod intersection;
pub mod ir;
pub(crate) mod labels;
pub(crate) mod loops;
pub(crate) mod patterns;
pub(crate) mod post_process;
pub(crate) mod resources;
pub(crate) mod secondary;
pub mod sforms;
pub mod stack;
pub mod stats;
pub(crate) mod switches;
pub mod vars;
