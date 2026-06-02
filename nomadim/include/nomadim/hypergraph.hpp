#ifndef NOMADIM_HYPERGRAPH_HPP
#define NOMADIM_HYPERGRAPH_HPP

#include "nomadim/types.hpp"
#include "nomadim/order_relation.hpp"
#include <vector>

namespace nomadim {

// Resource caps for the (worst-case exponential) dimension/realizer routines.
// Exceeding any cap makes the analysis routines throw std::runtime_error.
struct Caps {
    int max_vertices = 16;
    int max_critical_pairs = 64;
    int max_results = 1000;   // colorings / realizers / hyperedges
};

// Reverse every critical pair in `idxs` on top of `base` (reversing (x,y) adds
// y<x). Returns true iff the result stays acyclic; if so, `out` holds the closed
// order (a witness from which a linear extension can be read off).
bool reverse_set(const StrictRel& base, const std::vector<critical_pair>& cps,
                 const std::vector<int>& idxs, StrictRel& out);

// Convenience: just the reversibility verdict.
bool is_reversible(const StrictRel& base, const std::vector<critical_pair>& cps,
                   const std::vector<int>& idxs);

} // namespace nomadim

#endif // NOMADIM_HYPERGRAPH_HPP
