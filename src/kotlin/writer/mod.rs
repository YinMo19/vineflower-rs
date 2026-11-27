//! Kotlin compilation-unit and declaration writing.

pub mod annotations;
mod class;
mod declaration;
pub mod fallback;
mod header;
mod lambda;
mod method_body;
pub mod modifiers;

pub use class::write_class;
pub use header::write_header;
pub(crate) use lambda::{allocation_expression, field_expression};
pub(crate) use method_body::{dump_error, write_code, write_method_body};
