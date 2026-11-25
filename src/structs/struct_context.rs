// Copyright 2000-2021 JetBrains s.r.o. and the Vineflower contributors.
// SPDX-License-Identifier: Apache-2.0

//! `struct.StructContext`: every class the decompiler knows about — the
//! classes to decompile, loaded up front, and the library classes, loaded
//! when something first asks for them.
//!
//! Saving the decompiled classes (`saveContext`) is the driver's part and
//! lives with it.

use std::sync::{Arc, Mutex, RwLock};

use arcstr::ArcStr;
use rustc_hash::FxHashMap;

use super::context_unit::ContextUnit;
use super::struct_class::StructClass;
use crate::engine::Options;
use crate::engine::context_source::ContextSource;
use crate::renamer::pool_interceptor::PoolInterceptor;
use crate::types::generic_main;
use crate::util::java_str;

pub struct StructContext {
    options: Arc<Options>,
    interceptor: Option<Arc<PoolInterceptor>>,
    units: Vec<Arc<ContextUnit>>,
    lazy_units: Vec<Arc<ContextUnit>>,
    /// Every class asked for so far; `None` for a name no unit has.
    classes: RwLock<FxHashMap<ArcStr, Option<Arc<StructClass>>>>,
    /// original -> corrected
    badly_placed_classes: Mutex<FxHashMap<ArcStr, ArcStr>>,
    units_by_class_name: RwLock<FxHashMap<ArcStr, Arc<ContextUnit>>>,
    abstract_names: FxHashMap<String, Vec<String>>,
}

impl StructContext {
    pub fn new(options: Arc<Options>, interceptor: Option<Arc<PoolInterceptor>>) -> Self {
        Self {
            options,
            interceptor,
            units: Vec::new(),
            lazy_units: Vec::new(),
            classes: RwLock::default(),
            badly_placed_classes: Mutex::default(),
            units_by_class_name: RwLock::default(),
            abstract_names: FxHashMap::default(),
        }
    }

    pub(crate) fn options(&self) -> &Arc<Options> {
        &self.options
    }

    pub(crate) fn pool_interceptor(&self) -> Option<&Arc<PoolInterceptor>> {
        self.interceptor.as_ref()
    }

    pub fn get_class(&self, name: &str) -> Option<Arc<StructClass>> {
        let cached = self.classes.read().unwrap().get(name).cloned();
        let ret = match cached {
            Some(class) => class,
            None => {
                let loaded = self.load_class(name);
                self.classes
                    .write()
                    .unwrap()
                    .entry(name.into())
                    .or_insert(loaded)
                    .clone()
            }
        }?;

        // Correct the class location
        let corrected_name = self.badly_placed_classes.lock().unwrap().remove(name);
        if let Some(corrected_name) = corrected_name {
            let mut classes = self.classes.write().unwrap();
            classes.insert(corrected_name, Some(Arc::clone(&ret)));
            classes.remove(name);
        }

        Some(ret)
    }

    /// Loads a class from the context unit known to have it, or else from
    /// the first lazy unit that has it.
    fn load_class(&self, key: &str) -> Option<Arc<StructClass>> {
        let unit_for_class = self.units_by_class_name.read().unwrap().get(key).cloned();
        unit_for_class
            .iter()
            .chain(&self.lazy_units)
            .find_map(|unit| self.try_load_class(unit, key))
    }

    fn try_load_class(&self, unit_for_class: &Arc<ContextUnit>, key: &str) -> Option<Arc<StructClass>> {
        log::info!("Loading Class: {key} from {}", unit_for_class.get_name());
        match unit_for_class.try_load_class(key, &self.options, self.interceptor.clone()) {
            Ok(clazz) => {
                let clazz = Arc::new(clazz?);
                if key != clazz.qualified_name {
                    // also place the class in the right key if it's wrong
                    self.units_by_class_name
                        .write()
                        .unwrap()
                        .insert(clazz.qualified_name.clone(), Arc::clone(unit_for_class));
                    self.badly_placed_classes
                        .lock()
                        .unwrap()
                        .insert(key.into(), clazz.qualified_name.clone());
                }
                Some(clazz)
            }
            Err(error) => {
                log::error!(
                    "Failed to read class {key} from {}: {error}",
                    unit_for_class.get_name()
                );
                None
            }
        }
    }

    pub fn has_class(&self, name: &str) -> bool {
        if self.units_by_class_name.read().unwrap().contains_key(name) {
            return true;
        }

        self.lazy_units.iter().any(|unit| {
            unit.has_class(name).unwrap_or_else(|error| {
                log::error!(
                    "Failed to check if class {name} exists in {}: {error}",
                    unit.get_name()
                );
                false
            })
        })
    }

    pub fn get_own_classes(&self) -> Vec<Arc<StructClass>> {
        self.units
            .iter()
            .filter(|unit| unit.own)
            .flat_map(|unit| &unit.class_entries)
            .map(|name| {
                self.get_class(name)
                    .unwrap_or_else(|| panic!("Could not find class {name}"))
            })
            .collect()
    }

    /// Reads every class again, for instance to see the names an
    /// interceptor now gives them.
    pub fn reload_context(&mut self, interceptor: Option<Arc<PoolInterceptor>>) {
        self.interceptor = interceptor;
        self.classes.get_mut().unwrap().clear();
        self.units_by_class_name.get_mut().unwrap().clear();
        self.abstract_names.clear();

        let units = std::mem::take(&mut self.units);
        self.lazy_units.clear();

        for unit in units.iter().filter(|unit| unit.root) {
            self.add_unit(Arc::clone(&unit.source), unit.own, true);
        }
    }

    /// `addSpace(source, isOwn)`.
    pub fn add_space(&mut self, source: Arc<dyn ContextSource>, is_own: bool) {
        self.add_unit(source, is_own, true);
    }

    fn add_unit(&mut self, source: Arc<dyn ContextSource>, is_own: bool, is_root: bool) {
        let unit = Arc::new(ContextUnit::new(source, is_own, is_root, &self.options));
        self.units.push(Arc::clone(&unit));
        if unit.is_lazy() {
            self.lazy_units.push(Arc::clone(&unit));
        }
        self.init_unit(&unit);
    }

    fn init_unit(&mut self, unit: &Arc<ContextUnit>) {
        for metadata in &unit.abstract_metadata {
            self.load_abstract_metadata(metadata);
        }

        log::info!("Scanning classes from {}", unit.get_name());
        let is_own = unit.own;
        for clazz in &unit.class_entries {
            let units_by_class_name = self.units_by_class_name.get_mut().unwrap();
            if let Some(existing) = units_by_class_name.get(clazz.as_str())
                && (!is_own || existing.own)
            {
                continue;
            }
            units_by_class_name.insert(clazz.as_str().into(), Arc::clone(unit));

            log::trace!("    {clazz}");
            if is_own {
                // pre-load classes
                self.get_class(clazz);
            }
        }

        for child in &unit.child_contexts {
            self.add_unit(Arc::clone(child), is_own, false);
        }
    }

    /// Whether `valclass` is, extends or implements `refclass`.
    pub fn instance_of(&self, valclass: &str, refclass: &str) -> bool {
        if valclass == refclass {
            return true;
        }

        let cl = self.get_class(valclass);
        // Don't know what we are? We must at least be an object.
        let has_super_class = cl.as_ref().is_some_and(|cl| cl.super_class.is_some());
        if !has_super_class && refclass == "java/lang/Object" {
            return true;
        }

        let Some(cl) = cl else {
            return false;
        };

        if let Some(super_class) = &cl.super_class
            && self.instance_of(super_class.get_string(), refclass)
        {
            return true;
        }

        cl.interfaces.iter().any(|&iface| {
            let iface = cl.pool.get_primitive_constant(iface).unwrap();
            self.instance_of(iface.get_string(), refclass)
        })
    }

    /// JOIN both classes on the lattice. Find a common ancestor.
    pub fn find_common_ancestor(&self, class_a: &str, class_b: &str) -> Option<Arc<StructClass>> {
        let a = self.get_class(class_a)?;
        self.get_class(class_b)?;

        if self.instance_of(class_b, class_a) {
            return Some(a);
        }

        // Iterate through the superclasses and interfaces to find any that can be assigned.
        // Don't return if the returned class is Object, otherwise we may miss out on other
        // opportunities to do better. The returned type is essentially arbitrary; extended
        // superclasses are preferred before interfaces.
        let super_class = a.super_class.iter().map(|super_class| super_class.get_string().clone());
        let interfaces = a.interfaces.iter().map(|&iface| {
            let iface = a.pool.get_primitive_constant(iface).unwrap();
            iface.get_string().clone()
        });
        super_class
            .chain(interfaces)
            .filter_map(|supertype| self.find_common_ancestor(&supertype, class_b))
            .find(|cl| cl.qualified_name != "java/lang/Object")
    }

    pub fn load_abstract_metadata(&mut self, string: &str) {
        for line in java_str::split(string, "\n") {
            let pts = java_str::split(line, " ");
            //class method desc [args...]
            if pts.len() < 4 {
                continue;
            }

            let desc = generic_main::parse_method_signature(pts[2]).unwrap();
            let mut params = Vec::new();
            for (x, param) in pts[3..].iter().enumerate() {
                for _ in 0..desc.parameter_types[x].stack_size {
                    params.push((*param).to_owned());
                }
            }

            self.abstract_names
                .insert(format!("{} {} {}", pts[0], pts[1], pts[2]), params);
        }
    }

    pub fn rename_abstract_parameter<'a>(
        &'a self,
        class_name: &str,
        method_name: &str,
        descriptor: &str,
        index: i32,
        default: &'a str,
    ) -> &'a str {
        self.abstract_names
            .get(&format!("{class_name} {method_name} {descriptor}"))
            .and_then(|params| params.get(index as usize))
            .map_or(default, String::as_str)
    }

    pub fn get_units(&self) -> &[Arc<ContextUnit>] {
        &self.units
    }
}
