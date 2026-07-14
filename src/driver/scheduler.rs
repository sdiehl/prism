/// Bounded deterministic scheduler for independent compiler queries.
///
/// Work may finish in any order, but results are always returned in input order.
/// Changing the worker count therefore changes cost only, never artifact bytes.
const AUTO_WORKERS_SENTINEL: usize = 0;
const SEQUENTIAL_WORKERS: usize = 1;
const MIN_PARALLEL_INPUTS: usize = 2;

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

    pub(super) fn map_ordered<T, R, F>(&self, inputs: &[T], f: F) -> Vec<R>
    where
        T: Sync,
        R: Send,
        F: Fn(&T) -> R + Sync,
    {
        if self.threads == SEQUENTIAL_WORKERS || inputs.len() < MIN_PARALLEL_INPUTS {
            return inputs.iter().map(&f).collect();
        }
        let workers = self.threads.min(inputs.len());
        let chunk_size = inputs.len().div_ceil(workers);
        std::thread::scope(|scope| {
            let handles = inputs
                .chunks(chunk_size)
                .map(|chunk| {
                    let f = &f;
                    scope.spawn(move || chunk.iter().map(f).collect::<Vec<_>>())
                })
                .collect::<Vec<_>>();
            handles
                .into_iter()
                .flat_map(|handle| handle.join().expect("compiler query worker panicked"))
                .collect()
        })
    }
}

#[cfg(test)]
mod tests {
    use super::{QueryScheduler, SEQUENTIAL_WORKERS};

    #[test]
    fn worker_count_cannot_reorder_results() {
        const CASES: u64 = 257;
        const WORKERS: usize = 8;
        let inputs = (0_u64..CASES).collect::<Vec<_>>();
        let sequential =
            QueryScheduler::new(SEQUENTIAL_WORKERS).map_ordered(&inputs, |n| n.wrapping_mul(*n));
        let parallel = QueryScheduler::new(WORKERS).map_ordered(&inputs, |n| n.wrapping_mul(*n));
        assert_eq!(parallel, sequential);
    }
}
