// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `modules.decompiler.vars.VarVersionPair`: a variable index with its SSA version.

use std::fmt;

use crate::util::jhash::JavaHash;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct VarVersionPair {
    pub var: i32,
    pub version: i32,
}

impl VarVersionPair {
    pub fn new(var: i32, version: i32) -> Self {
        Self { var, version }
    }

    pub fn is(&self, var: i32, version: i32) -> bool {
        self.var == var && self.version == version
    }
}

impl JavaHash for VarVersionPair {
    fn java_hash(&self) -> i32 {
        self.var.wrapping_mul(31).wrapping_add(self.version)
    }
}

impl fmt::Display for VarVersionPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({},{})", self.var, self.version)
    }
}
