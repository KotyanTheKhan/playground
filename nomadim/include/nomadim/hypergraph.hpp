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

// Minimal non-reversible subsets of the critical pairs (alternating cycles):
// the edges of the dimension hypergraph. Each edge is a sorted list of indices
// into `cps`. Enumerated by increasing size; a set is an edge iff it is
// non-reversible but every proper subset is reversible. Throws
// std::runtime_error if cps.size() exceeds caps.max_critical_pairs, and stops
// after caps.max_results edges.
std::vector<std::vector<int>>
enumerate_hyperedges(const StrictRel& base, const std::vector<critical_pair>& cps,
                     const Caps& caps);

// Smallest k>=2 for which the critical pairs admit a proper coloring (each color
// class reversible). Precondition: cps non-empty (callers handle the chain case
// dim<=1 separately). Throws if cps exceed caps.max_critical_pairs.
int chromatic_number(const StrictRel& base, const std::vector<critical_pair>& cps,
                     const Caps& caps);

// True iff the critical pairs admit a proper k-coloring (i.e. dimension <= k).
// Early-exits on the first valid coloring, so it is far cheaper than
// chromatic_number when the answer is "yes" -- it does not first prove that
// fewer colors are impossible. Throws if cps exceed caps.max_critical_pairs.
bool colorable_with(const StrictRel& base, const std::vector<critical_pair>& cps,
                    int k, const Caps& caps);

// All distinct proper k-colorings using exactly k colors, each as a color-per-
// critical-pair vector, canonicalized (colors numbered by first appearance) so
// permutation-equivalent colorings are reported once. Capped at caps.max_results.
std::vector<std::vector<int>>
enumerate_min_colorings(const StrictRel& base, const std::vector<critical_pair>& cps,
                        int k, const Caps& caps);

} // namespace nomadim

#endif // NOMADIM_HYPERGRAPH_HPP
