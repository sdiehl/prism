//! Strongly-connected components of a directed graph in index-adjacency form.
//!
//! Shared by dependency-ordered type inference (`types::effects::dep_sccs`) and
//! the content-hash cycle boundary (`core::hash`), which used to carry their own
//! Tarjan copies, one of them recursive.

/// Iterative Tarjan over an index graph.
///
/// `adj[v]` lists `v`'s successors, which must be in increasing order for a
/// deterministic walk. Returns the strongly-connected components callee-first
/// (each component after the ones it depends on), each component's members in
/// increasing index order. The explicit work stack avoids overflowing the native
/// stack on a deep call chain (a deep prelude dependency, say).
#[must_use]
pub(crate) fn tarjan_scc(adj: &[Vec<usize>]) -> Vec<Vec<usize>> {
    const UNVISITED: u32 = u32::MAX;
    let n = adj.len();
    let mut index = vec![UNVISITED; n];
    let mut lowlink = vec![0u32; n];
    let mut on_stack = vec![false; n];
    let mut comp_stack: Vec<usize> = Vec::new();
    let mut next_index: u32 = 0;
    let mut sccs: Vec<Vec<usize>> = Vec::new();
    for start in 0..n {
        if index[start] != UNVISITED {
            continue;
        }
        index[start] = next_index;
        lowlink[start] = next_index;
        next_index += 1;
        comp_stack.push(start);
        on_stack[start] = true;
        let mut work: Vec<(usize, usize)> = vec![(start, 0)];
        while let Some(&mut (v, ref mut i)) = work.last_mut() {
            if let Some(&w) = adj[v].get(*i) {
                *i += 1;
                if index[w] == UNVISITED {
                    index[w] = next_index;
                    lowlink[w] = next_index;
                    next_index += 1;
                    comp_stack.push(w);
                    on_stack[w] = true;
                    work.push((w, 0));
                } else if on_stack[w] {
                    lowlink[v] = lowlink[v].min(index[w]);
                }
            } else {
                if lowlink[v] == index[v] {
                    let mut comp = Vec::new();
                    loop {
                        let u = comp_stack.pop().expect("Tarjan stack underflow");
                        on_stack[u] = false;
                        comp.push(u);
                        if u == v {
                            break;
                        }
                    }
                    comp.sort_unstable();
                    sccs.push(comp);
                }
                let low_v = lowlink[v];
                work.pop();
                if let Some(&(parent, _)) = work.last() {
                    lowlink[parent] = lowlink[parent].min(low_v);
                }
            }
        }
    }
    sccs
}
