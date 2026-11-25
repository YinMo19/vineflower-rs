// SPDX-License-Identifier: Apache-2.0

//! Upstream's `code.cfg` package: basic blocks and the control-flow graph.

pub mod basic_block;
pub mod control_flow_graph;
pub mod exception_range_cfg;
mod jsr;

pub use control_flow_graph::ControlFlowGraph;
pub use exception_range_cfg::ExceptionRangeCFG;
