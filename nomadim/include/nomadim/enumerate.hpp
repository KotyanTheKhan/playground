#ifndef NOMADIM_ENUMERATE_HPP
#define NOMADIM_ENUMERATE_HPP

#include "nomadim/process_graph.hpp"
#include <vector>

namespace nomadim {

struct EnumerateResult {
    int count = 0;                            // # non-isomorphic dim-2 synced executions
    int isomorphic_hits = 0;                  // # collapsed by isomorphism
    std::vector<ProcessGraph> results;        // the representatives
};

// True if, in g's transitive closure, every process' last vertex is reachable
// from every process' start (fully synchronized execution).
bool is_full_synchronized(const ProcessGraph& g);

// Enumerate non-isomorphic, fully-synchronized, dimension-2 executions of
// n_procs processes using up to max_sync syncs, with `threads` worker threads
// (>= 1; 1 = single-threaded). The .count is independent of `threads`.
EnumerateResult enumerate(int n_procs, int max_sync, unsigned threads);

} // namespace nomadim

#endif // NOMADIM_ENUMERATE_HPP
