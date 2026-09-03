use std::any::Any;
use std::fmt;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::thread;

/// Bounded deterministic scheduler for independent compiler queries.
///
/// Work may finish in any order, but results are always returned in input order.
/// Changing the worker count therefore changes cost only, never artifact bytes.
const AUTO_WORKERS_SENTINEL: usize = 0;
const SEQUENTIAL_WORKERS: usize = 1;
const MIN_PARALLEL_INPUTS: usize = 2;
const MEBIBYTE: usize = 1024 * 1024;
// Workers run the same lowering recursions the main thread does, so they carry
// the same 8 MiB budget; the platform default for a spawned thread is a
// quarter of that, and a deep program then overflows only when the scheduler
// happens to run it off the main thread.
const WORKER_STACK: usize = 8 * MEBIBYTE;

#[derive(Debug)]
pub(super) struct QueryWorkerFailure {
    message: String,
}

impl QueryWorkerFailure {
    fn from_panic(payload: &(dyn Any + Send)) -> Self {
        let message = payload
            .downcast_ref::<String>()
            .cloned()
            .or_else(|| {
                payload
                    .downcast_ref::<&'static str>()
                    .map(ToString::to_string)
            })
            .unwrap_or_else(|| "non-string panic payload".to_string());
        Self { message }
    }
}

impl fmt::Display for QueryWorkerFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "compiler query worker panicked: {}", self.message)
    }
}

impl std::error::Error for QueryWorkerFailure {}

pub(super) struct QueryScheduler {
    threads: usize,
}

impl QueryScheduler {
    pub(super) const fn new(threads: usize) -> Self {
        Self {
            threads: if threads == AUTO_WORKERS_SENTINEL {
                SEQUENTIAL_WORKERS
            } else {
                threads
            },
        }
    }

    pub(super) fn map_ordered<T, R, F>(
        &self,
        inputs: &[T],
        f: F,
    ) -> Result<Vec<R>, QueryWorkerFailure>
    where
        T: Sync,
        R: Send,
        F: Fn(&T) -> R + Sync,
    {
        if self.threads == SEQUENTIAL_WORKERS || inputs.len() < MIN_PARALLEL_INPUTS {
            return catch_unwind(AssertUnwindSafe(|| inputs.iter().map(&f).collect()))
                .map_err(|payload| QueryWorkerFailure::from_panic(payload.as_ref()));
        }
        let workers = self.threads.min(inputs.len());
        let chunk_size = inputs.len().div_ceil(workers);
        thread::scope(|scope| {
            let handles = inputs
                .chunks(chunk_size)
                .map(|chunk| {
                    let f = &f;
                    thread::Builder::new()
                        .stack_size(WORKER_STACK)
                        .spawn_scoped(scope, move || chunk.iter().map(f).collect::<Vec<_>>())
                        .expect("spawn compiler query worker")
                })
                .collect::<Vec<_>>();
            let mut output = Vec::with_capacity(inputs.len());
            let mut first_failure = None;
            for handle in handles {
                match handle.join() {
                    Ok(chunk) if first_failure.is_none() => output.extend(chunk),
                    Err(payload) if first_failure.is_none() => {
                        first_failure = Some(QueryWorkerFailure::from_panic(payload.as_ref()));
                    }
                    Ok(_) | Err(_) => {}
                }
            }
            first_failure.map_or_else(|| Ok(output), Err)
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{QueryScheduler, SEQUENTIAL_WORKERS};
    use crate::error::Error;

    #[test]
    fn worker_count_cannot_reorder_results() {
        const CASES: u64 = 257;
        const WORKERS: usize = 8;
        let inputs = (0_u64..CASES).collect::<Vec<_>>();
        let sequential = QueryScheduler::new(SEQUENTIAL_WORKERS)
            .map_ordered(&inputs, |n| n.wrapping_mul(*n))
            .expect("sequential query schedule");
        let parallel = QueryScheduler::new(WORKERS)
            .map_ordered(&inputs, |n| n.wrapping_mul(*n))
            .expect("parallel query schedule");
        assert_eq!(parallel, sequential);
    }

    #[test]
    fn worker_panics_return_the_first_input_order_failure() {
        const INPUTS: usize = 8;
        const PARALLEL_WORKERS: usize = 4;
        const FIRST_PANIC: usize = 1;
        const LATER_PANIC: usize = 2;
        let inputs = (0..INPUTS).collect::<Vec<_>>();

        for workers in [SEQUENTIAL_WORKERS, PARALLEL_WORKERS] {
            let failure = QueryScheduler::new(workers)
                .map_ordered(&inputs, |input| match *input {
                    FIRST_PANIC => panic!("first input-order failure"),
                    LATER_PANIC => panic!("later input-order failure"),
                    value => value,
                })
                .expect_err("worker panic must cross the scheduler as an error");
            assert!(matches!(
                Error::from(failure),
                Error::InternalInvariant(message)
                    if message == "compiler query worker panicked: first input-order failure"
            ));
        }
    }
}
