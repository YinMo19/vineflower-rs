// Copyright 2000-2021 JetBrains s.r.o. Use of this source code is governed by the Apache 2.0 license that can be found in the LICENSE file.

use std::rc::Rc;

use crate::descriptor::MethodDescriptor;

use super::super::expr::{Expr, Source};
use super::Locals;

impl Locals<'_> {
    pub(in crate::lift) fn capture_slot(&self, value: &Expr) -> Option<(u16, bool)> {
        let Source::Local(index) = value.source else {
            return None;
        };
        if value.order.is_none() || value.observable {
            return None;
        }
        let local = self.slots.get(usize::from(index))?.as_ref()?;
        if value.text != local.name || local.ty != value.ty {
            return None;
        }
        Some((index, self.parameter_names.contains(&local.name)))
    }

    pub(in crate::lift) fn bind_lambda_scope(
        &mut self,
        outer: &Self,
        captures: &[&str],
        descriptor: &MethodDescriptor,
        is_static: bool,
    ) {
        let mut names = self.names.borrow_mut();
        // Lambda parameters and locals are lexical children of the caller,
        // even though their bytecode was lifted from a separate method.
        let mut slot = usize::from(!is_static);
        let outer = outer.names.borrow();
        names.used.clone_from(&outer.used);
        if let (Some(child), Some(parent)) = (names.namer.as_mut(), outer.namer.as_ref()) {
            child.inherit(parent);
        }
        let parameters = Rc::make_mut(&mut self.parameter_names);
        for (ordinal, (parameter, ty)) in parameters
            .iter_mut()
            .zip(&descriptor.parameters)
            .enumerate()
        {
            let local = self.slots[slot].as_mut().expect("bound lambda parameter");
            let name = if let Some(capture) = captures.get(ordinal) {
                (*capture).into()
            } else {
                names.fresh(parameter)
            };
            parameter.clone_from(&name);
            local.name = name;
            slot += usize::from(ty.slots());
        }
    }

    pub(in crate::lift) fn lambda_parameter(&self, index: usize) -> String {
        self.names.borrow_mut().fresh(&format!("param{index}"))
    }
}
