// SPDX-License-Identifier: Apache-2.0

//! Upstream's `struct` packages: the loaded class model and the context
//! classes are looked up in.

pub mod attr;
pub mod consts;
pub mod context_unit;
pub mod struct_class;
pub mod struct_context;
pub mod struct_field;
pub mod struct_member;
pub mod struct_method;

pub use struct_class::StructClass;
pub use struct_context::StructContext;
pub use struct_field::{StructField, StructRecordComponent};
pub use struct_member::{Attributes, StructMember};
pub use struct_method::StructMethod;

pub mod single_file_context_source;
