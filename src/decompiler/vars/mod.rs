// SPDX-License-Identifier: Apache-2.0

//! Upstream's `modules.decompiler.vars` package: variable versions, types,
//! names and definitions.

pub(crate) mod definitions;
mod inference;
pub(crate) mod naming;
pub mod processor;
pub mod var_version_pair;
pub mod version_graph;
pub mod versions;
