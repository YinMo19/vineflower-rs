// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `main.collectors.ImportCollector`.

use super::Cx;

#[derive(Default)]
pub struct ImportCollector {}

/// `getShortName(fullName)`.
pub fn get_short_name(_cx: &mut Cx, _full_name: &str) -> String {
    todo!("ImportCollector.getShortName")
}
