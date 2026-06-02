#ifndef NOMADIM_POSET_HPP
#define NOMADIM_POSET_HPP

#include "nomadim/types.hpp"

namespace nomadim {

class ProcessGraph; // fwd decl

// A general poset given by its cover/adjacency relation. edges[u] lists the
// vertices directly above u; the reachability closure is the partial order.
struct Poset {
    int n_vertices = 0;
    adjacency_list edges;

    // Throws std::invalid_argument if n_vertices < 0, edges.size() != n_vertices,
    // any endpoint is out of range, or the relation contains a cycle.
    void validate() const;

    // Build a Poset from a process-graph DAG (verbatim adjacency).
    static Poset from(const ProcessGraph& g);
};

} // namespace nomadim

#endif // NOMADIM_POSET_HPP
