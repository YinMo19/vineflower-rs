// SPDX-License-Identifier: Apache-2.0

//! Cooperative deadlines for code-to-source method processing.

use std::cell::Cell;
use std::io;
use std::panic::resume_unwind;
use std::time::{Duration, Instant};

thread_local! {
    // Both language pipelines have infallible helper passes over the same IR.
    // A thread-local deadline lets those passes unwind to the existing method
    // boundary without putting timer state on each graph or moving the worker.
    static DEADLINE: Cell<Option<Instant>> = const { Cell::new(None) };
}

#[derive(Debug, thiserror::Error)]
#[error("Processing time limit exceeded")]
pub(super) struct MethodTimeout;

struct DeadlineScope(Option<Instant>);

impl Drop for DeadlineScope {
    fn drop(&mut self) {
        DEADLINE.set(self.0);
    }
}

pub(super) fn run<T>(seconds: i32, process: impl FnOnce() -> io::Result<T>) -> io::Result<T> {
    let deadline = Instant::now() + Duration::from_secs(seconds.max(0) as u64);
    let _scope = DeadlineScope(DEADLINE.replace(Some(deadline)));
    checkpoint();
    let result = process();
    if !matches!(&result, Err(error) if error.kind() == io::ErrorKind::Interrupted) {
        checkpoint();
    }
    result
}

#[inline]
pub(crate) fn checkpoint() {
    if DEADLINE
        .get()
        .is_some_and(|deadline| Instant::now() >= deadline)
    {
        expire();
    }
}

#[cold]
fn expire() -> ! {
    // This is an expected method error. Skip the process-wide panic hook.
    resume_unwind(Box::new(MethodTimeout))
}
