// Copyright 2000-2017 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

//! Java identifier rules and Vineflower naming policies.

mod identifiers;
mod members;
mod variables;

pub use identifiers::{IdentifierKind, MemberRenamer, is_valid_identifier, is_valid_local_identifier};
pub use members::MemberRenames;
pub use variables::{VariableBinding, VariableNamer, VariableRenamer};
