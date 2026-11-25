// SPDX-License-Identifier: Apache-2.0

//! Upstream's `main` packages: the decompilation session, its ambient
//! context and the class-level processors.

pub mod bytecode_mapping_tracer;
pub mod class_nodes;
pub mod class_processor;
pub mod class_wrapper;
pub mod context;
pub mod context_source;
pub mod counter_container;
pub mod import_collector;
pub mod method_processor;
pub mod nested;
pub mod options;

pub use context::Cx;
pub use options::Options;
