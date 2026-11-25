// SPDX-License-Identifier: Apache-2.0

//! Upstream's `modules.decompiler` packages: the statement and expression IR
//! and the passes that turn a control-flow graph into structured source.

pub mod decompose;
pub mod expr_processor;
pub mod exps;
pub mod finally;
pub mod flow;
pub(crate) mod increments;
pub mod ir;
pub mod sforms;
pub mod stack;
pub mod stats;
pub mod vars;
