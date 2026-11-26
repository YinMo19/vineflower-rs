// SPDX-License-Identifier: Apache-2.0

//! ContextUnit preparation. Workers own the initial method graphs until the
//! coordinator reaches the corresponding root in publication order.

use std::sync::{Arc, mpsc};
use std::thread;
use std::{cell::OnceCell, io};

use super::{ClassSession, Cx, PendingClass, ReclaimSchedule};
use crate::decompiler::ir::Ir;
use crate::engine::class_nodes::{ClassNodes, ClassSnapshot, LambdaScan};
use crate::engine::class_processor::{process_class_with_lambda_scan, worker_classes};
use crate::engine::class_wrapper::catch_method_failure;
use crate::engine::method_processor::PreparedMethods;
use crate::structs::{StructClass, StructContext};

#[derive(Default)]
struct PreparedRoot {
    lambdas: LambdaScan,
    methods: Option<(Ir, PreparedMethods)>,
}

struct RootWork {
    classes: Vec<Arc<StructClass>>,
    kotlin: bool,
    methods: Option<(Ir, ClassSnapshot)>,
}

impl RootWork {
    fn snapshot(cx: &mut Cx, root: &PendingClass, definitions: &OnceCell<ClassSnapshot>) -> Self {
        let classes = worker_classes(&cx.class_nodes, root.node);
        // A timed method stays inside one deadline from decode through its
        // final pass. Lambda discovery is outside that deadline in Java.
        let methods =
            (!classes.is_empty() && cx.options.method_time_limit().is_none()).then(|| {
                let definitions = definitions.get_or_init(|| ClassSnapshot::new(&cx.class_nodes));
                (cx.ir.fork(), definitions.clone())
            });
        Self {
            classes,
            kotlin: root.kotlin,
            methods,
        }
    }

    fn prepare(self, context: &Arc<StructContext>) -> PreparedRoot {
        let lambdas = LambdaScan::for_classes(&self.classes);
        let methods = self.methods.map(|(ir, definitions)| {
            let mut worker = Cx::new(Arc::clone(context));
            worker.ir = ir;
            worker.class_nodes = ClassNodes::for_preparation(definitions, &lambdas, &self.classes);
            PreparedMethods::prepare(worker, self.classes, self.kotlin)
        });
        PreparedRoot { lambdas, methods }
    }
}

pub(super) fn unit(
    cx: &mut Cx,
    roots: &mut [PendingClass],
    reclaim: &mut ReclaimSchedule,
    parent: &ClassSession,
    definitions: &OnceCell<ClassSnapshot>,
) -> io::Result<()> {
    let count = cx.options.worker_count();
    // ContextUnit constructs its ForkJoinPool even for small input units.
    if count > 0x7fff {
        return Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            "thread-count exceeds the ForkJoinPool limit of 32767",
        ));
    }
    let count = count.min(roots.len());
    if count <= 1 {
        for i in 0..roots.len() {
            publish(cx, &mut roots[i], PreparedRoot::default())?;
            reclaim.after_root(cx, &roots[..=i], parent);
        }
        return Ok(());
    }

    thread::scope(|scope| {
        // One configured thread publishes wrappers and finishes methods. Each
        // other thread may prepare one root ahead, bounding unpublished IR.
        let mut workers = Vec::with_capacity(count - 1);
        for (i, root) in roots.iter().take(count - 1).enumerate() {
            let context = Arc::clone(&cx.struct_context);
            let (jobs, inputs) = mpsc::channel::<RootWork>();
            let (results, ready) = mpsc::sync_channel(0);
            thread::Builder::new()
                .name(format!("Vineflower-DecompilerThread-{i}"))
                .spawn_scoped(scope, move || {
                    for work in inputs {
                        if results.send(work.prepare(&context)).is_err() {
                            break;
                        }
                    }
                })?;
            jobs.send(RootWork::snapshot(cx, root, definitions))
                .unwrap();
            workers.push((jobs, ready));
        }
        for i in 0..roots.len() {
            let (jobs, ready) = &workers[i % workers.len()];
            let prepared = ready.recv().expect("root preparation worker stopped");
            if let Some(next) = roots.get(i + workers.len()) {
                jobs.send(RootWork::snapshot(cx, next, definitions))
                    .unwrap();
            }
            publish(cx, &mut roots[i], prepared)?;
            reclaim.after_root(cx, &roots[..=i], parent);
        }
        Ok(())
    })
}

fn publish(cx: &mut Cx, root: &mut PendingClass, prepared: PreparedRoot) -> io::Result<()> {
    let start = cx.ir.allocated_bytes();
    if let Some((ir, methods)) = prepared.methods {
        cx.ir.adopt(ir);
        cx.prepared_methods = Some(Box::new(methods));
    }
    log::info!("Preprocessing class {}", root.class.qualified_name);
    let processed =
        catch_method_failure(|| process_class_with_lambda_scan(cx, root.node, prepared.lambdas));
    // A rejected lambda or failed class can leave unconsumed method graphs.
    // Release them before tracing handles from the published wrappers.
    cx.prepared_methods = None;
    root.session = Some(cx.take_class_session());
    root.prepared_bytes = cx.ir.allocated_bytes() - start;
    if let Err(error) = processed {
        if error.kind() == io::ErrorKind::Interrupted {
            return Err(error);
        }
        log::error!(
            "Class {} couldn't be fully decompiled: {error}",
            root.class.qualified_name
        );
        root.error = Some(error);
    }
    Ok(())
}
