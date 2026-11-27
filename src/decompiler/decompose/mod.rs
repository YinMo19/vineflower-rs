//! Dominance and decomposition of method control flow.

pub mod dom_helper;
pub mod extended_postdominance;
pub mod finish;
pub mod generic_dominator_engine;
pub mod if_helper;
mod irreducible;
mod regions;
pub mod statement_order;
