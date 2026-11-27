//! The class facts used while lifting allocations and simplifying stack vars.
//! Worker graphs carry the names they consulted back to wrapper publication.

use std::{
    mem,
    panic::resume_unwind,
    ptr,
    sync::{Arc, Mutex},
};

use super::{
    ArcStr, ClassKind, ClassNode, ClassNodes, FxHashMap, LambdaInformation, StructClass, VarType,
};
use crate::structs::{StructContext, struct_context::ClasspathObservations};

#[derive(Clone, Copy)]
pub(crate) struct AllocationClass<'a> {
    pub class: &'a StructClass,
    pub kind: ClassKind,
    pub anonymous_type: Option<&'a VarType>,
    pub lambda: Option<&'a LambdaInformation>,
}

impl<'a> From<&'a ClassNode> for AllocationClass<'a> {
    fn from(node: &'a ClassNode) -> Self {
        Self {
            class: &node.class,
            kind: node.kind,
            anonymous_type: node.anonymous_type.as_ref(),
            lambda: node.lambda.as_ref(),
        }
    }
}

pub(super) struct Definition {
    pub class: Arc<StructClass>,
    pub kind: ClassKind,
    pub anonymous_type: Option<VarType>,
    pub lambda: Option<LambdaInformation>,
}

impl Definition {
    fn view(&self) -> AllocationClass<'_> {
        AllocationClass {
            class: &self.class,
            kind: self.kind,
            anonymous_type: self.anonymous_type.as_ref(),
            lambda: self.lambda.as_ref(),
        }
    }

    fn matches(&self, node: &ClassNode) -> bool {
        ptr::eq(self.class.as_ref(), node.class.as_ref())
            && self.kind == node.kind
            && self.anonymous_type == node.anonymous_type
            && self.lambda == node.lambda
    }
}

pub(super) type Definitions = FxHashMap<ArcStr, Arc<Definition>>;

/// Shared by the root workers. A later input unit can reuse this snapshot:
/// publication checks each answer against the live name table.
#[derive(Clone)]
pub(in crate::engine) struct ClassSnapshot(Arc<Definitions>);

impl ClassSnapshot {
    pub(in crate::engine) fn new(nodes: &ClassNodes) -> Self {
        Self(Arc::new(
            nodes
                .iter()
                .map(|(name, node)| {
                    (
                        name.clone(),
                        Arc::new(Definition {
                            class: Arc::clone(&node.class),
                            kind: node.kind,
                            anonymous_type: node.anonymous_type.clone(),
                            lambda: node.lambda.clone(),
                        }),
                    )
                })
                .collect(),
        ))
    }
}

pub(super) struct WorkerClasses {
    published: ClassSnapshot,
    lambdas: Definitions,
    allocations: Mutex<ObservedAllocations>,
    classpath: Mutex<ClasspathObservations>,
}

type ObservedAllocations = FxHashMap<ArcStr, Option<Arc<Definition>>>;

pub(in crate::engine) struct ClassObservations {
    allocations: ObservedAllocations,
    classpath: ClasspathObservations,
}

impl ClassObservations {
    // Methods keep allocation flags and types, never a provisional class-node
    // ID. Two nodes with the same facts give the same answer. A recorded miss
    // matters too: another root may since have published a lambda of that name.
    pub(in crate::engine) fn valid_for(&self, nodes: &ClassNodes, context: &StructContext) -> bool {
        self.allocations
            .iter()
            .all(|(name, observed)| match (observed, nodes.get(name)) {
                (Some(observed), Some(node)) => observed.matches(node),
                (None, None) => true,
                _ => false,
            })
            && self.classpath.valid_for(context)
    }
}

pub(in crate::engine) struct NeedsClassSession;

impl NeedsClassSession {
    pub(in crate::engine) fn defer() -> ! {
        resume_unwind(Box::new(Self))
    }
}

impl ClassNodes {
    pub(in crate::engine) fn for_preparation(
        published: ClassSnapshot,
        lambdas: &super::LambdaScan,
        classes: &[Arc<StructClass>],
    ) -> Self {
        Self {
            preparing: Some(Box::new(WorkerClasses {
                published,
                lambdas: lambdas.definitions(classes),
                allocations: Mutex::default(),
                classpath: Mutex::default(),
            })),
            ..Self::default()
        }
    }

    pub(crate) fn allocation_class(&self, name: &str) -> Option<AllocationClass<'_>> {
        let Some(worker) = &self.preparing else {
            return self.get(name).map(AllocationClass::from);
        };
        let definition = worker
            .lambdas
            .get(name)
            .or_else(|| worker.published.0.get(name));
        let mut observed = worker.allocations.lock().unwrap();
        if !observed.contains_key(name) {
            observed.insert(name.into(), definition.cloned());
        }
        definition.map(|definition| definition.view())
    }

    pub(in crate::engine) fn take_observations(&mut self) -> ClassObservations {
        let worker = self.preparing.as_mut().expect("worker class snapshot");
        ClassObservations {
            allocations: mem::take(worker.allocations.get_mut().unwrap()),
            classpath: mem::take(worker.classpath.get_mut().unwrap()),
        }
    }

    pub(in crate::engine) fn classpath_observations(
        &self,
    ) -> Option<&Mutex<ClasspathObservations>> {
        self.preparing.as_ref().map(|worker| &worker.classpath)
    }

    /// Lazy loading, imports and wrapper queries use the ordered class session.
    pub(crate) fn require_class_session(&self) {
        if self.preparing.is_some() {
            NeedsClassSession::defer();
        }
    }
}
