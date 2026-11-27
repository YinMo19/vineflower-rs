//! Checking and merging substitutions against declared generic bounds.

use rustc_hash::{FxHashMap, FxHashSet};

use super::{assign_bounds, instance_of};
use crate::engine::Cx;
use crate::structs::StructClass;
use crate::types::{CodeType, GenericMethodDescriptor, GenericsMap, NamedGenerics, VarType};

pub(super) struct Mappings {
    pub named: NamedGenerics,
    pub bounds: NamedGenerics,
    pub values: GenericsMap,
}

impl Mappings {
    pub(super) fn new(
        cx: &Cx,
        declaring: &StructClass,
        method: Option<&GenericMethodDescriptor>,
        named: NamedGenerics,
        values: GenericsMap,
    ) -> Self {
        let mut bounds = NamedGenerics::new();
        if let Some(method) = method {
            assign_bounds(
                &mut bounds,
                &method.type_parameters,
                &method.type_parameter_bounds,
                true,
            );
        }
        if let Some(signature) = declaring.signature() {
            assign_bounds(
                &mut bounds,
                &signature.fparameters,
                &signature.fbounds,
                true,
            );
        }

        let mut parent = cx
            .class_nodes
            .get(&declaring.qualified_name)
            .and_then(|node| node.parent);
        while let Some(id) = parent {
            let node = &cx.class_nodes[id];
            if let Some(signature) = node.class.signature() {
                assign_bounds(
                    &mut bounds,
                    &signature.fparameters,
                    &signature.fbounds,
                    true,
                );
            }
            parent = node.parent;
        }

        Self {
            named,
            bounds,
            values,
        }
    }

    pub(super) fn process(&mut self, cx: &Cx, from: VarType, to: Option<VarType>) -> bool {
        if to.as_ref().is_some_and(|ty| {
            *ty == VarType::VARTYPE_NULL
                || (ty.ty == CodeType::Genvar && !self.named.contains_key(ty))
        }) {
            return false;
        }
        if !self.values.contains_key(&from) {
            self.put(cx, from, to);
            return true;
        }
        let (Some(to), Some(current)) = (to, self.values.get(&from).and_then(Option::as_ref))
        else {
            return false;
        };
        if to == *current || self.named.contains_key(current) {
            return false;
        }
        if current.ty != CodeType::Genvar
            && to.ty == CodeType::Genvar
            && let Some(bound) = self.named.get(&to).and_then(|bounds| bounds.first())
            && *bound != VarType::VARTYPE_OBJECT
            && instance_of(cx, bound, current)
        {
            return false;
        }
        if to.is_generic()
            && current.is_generic()
            && VarType::is_assignable(cx, &to, current, &self.named)
        {
            self.put(cx, from, Some(to));
            return true;
        }
        false
    }

    pub(super) fn put(&mut self, cx: &Cx, from: VarType, to: Option<VarType>) {
        if self.in_bounds(cx, &from, to.as_ref()) {
            self.values.insert(from, to);
        }
    }

    pub(super) fn in_bounds(&mut self, cx: &Cx, from: &VarType, to: Option<&VarType>) -> bool {
        self.verify_bounds(cx, from, to, &mut FxHashSet::default())
    }

    fn verify_bounds(
        &mut self,
        cx: &Cx,
        from: &VarType,
        to: Option<&VarType>,
        visited: &mut FxHashSet<(VarType, VarType)>,
    ) -> bool {
        let Some(bounds) = self.bounds.get(from).cloned() else {
            return false;
        };
        let Some(to) = to else { return true };
        let candidates = if to.ty == CodeType::Genvar {
            let Some(bounds) = self.named.get(to) else {
                return true;
            };
            bounds.clone()
        } else {
            vec![to.clone()]
        };
        for bound in &bounds {
            if !candidates
                .iter()
                .any(|candidate| self.verify_bound(cx, from, to, candidate, bound, visited))
            {
                return false;
            }
        }
        true
    }

    fn known_bound(&self, ty: &VarType) -> Option<&VarType> {
        self.values
            .get(ty)
            .and_then(Option::as_ref)
            .or_else(|| self.named.get(ty).and_then(|bounds| bounds.first()))
    }

    fn verify_bound(
        &mut self,
        cx: &Cx,
        from: &VarType,
        to: &VarType,
        candidate: &VarType,
        bound: &VarType,
        visited: &mut FxHashSet<(VarType, VarType)>,
    ) -> bool {
        let mut bound = bound.clone();
        if bound.ty == CodeType::Genvar {
            if self
                .known_bound(&bound)
                .is_some_and(|mapped| *mapped != bound)
            {
                let mut seen = FxHashMap::default();
                while let Some(next) = self.known_bound(&bound) {
                    if *next == bound || seen.get(&bound) == Some(next) {
                        break;
                    }
                    seen.insert(bound, next.clone());
                    bound = next.clone();
                }
                if bound.ty != CodeType::Genvar {
                    return instance_of(cx, candidate, &bound);
                }
            }
            if visited.insert((bound.clone(), candidate.clone())) {
                return self.verify_bounds(cx, &bound, Some(candidate), visited);
            }
        }

        if (candidate.ty as u32) < CodeType::Object as u32 {
            return bound == VarType::VARTYPE_OBJECT || bound == *candidate;
        }
        if candidate.ty != CodeType::Genvar && !instance_of(cx, candidate, &bound) {
            return false;
        }

        if bound.is_generic() && !bound.arguments().is_empty() {
            let view = if candidate.value == bound.value {
                candidate.clone()
            } else {
                VarType::get_generic_super_type(cx, candidate, &bound)
            };
            if !view.is_generic() || view.arguments().len() != bound.arguments().len() {
                return false;
            }
            let mut additional = GenericsMap::new();
            for (bound_argument, candidate_argument) in
                bound.arguments().iter().zip(view.arguments())
            {
                let Some(bound_argument) = bound_argument else {
                    continue;
                };
                if Some(bound_argument) == candidate_argument.as_ref() {
                    continue;
                }
                // T extends Comparable<T>.
                if from == bound_argument && Some(to) == candidate_argument.as_ref() {
                    continue;
                }
                // T extends Comparable<S>, where S has its own bound.
                if self.bounds.contains_key(bound_argument)
                    && visited.insert((bound.clone(), candidate.clone()))
                    && self.verify_bounds(cx, bound_argument, candidate_argument.as_ref(), visited)
                {
                    additional.insert(bound_argument.clone(), candidate_argument.clone());
                    continue;
                }
                return false;
            }
            for (key, value) in additional.iter() {
                self.process(cx, key.clone(), value.clone());
            }
        }
        true
    }
}
