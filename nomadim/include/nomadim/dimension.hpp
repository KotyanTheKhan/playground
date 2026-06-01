#ifndef NOMADIM_DIMENSION_HPP
#define NOMADIM_DIMENSION_HPP

#include "nomadim/types.hpp"
#include <vector>

namespace nomadim {

// True if the directed graph contains a cycle (DFS, recursion stack).
bool have_cycle(const adjacency_list& g);

// True if the undirected graph (given as symmetric adjacency) is 2-colorable.
bool is_bipartite(const adjacency_list& g);

// (x,y) is critical if forcing edge x->y collapses no OTHER incomparable pair.
// `matrix` is the n*n transitive-closure distance matrix (already Floyd'd).
bool check_if_critical(const int* matrix, int n, int x, int y);

// All critical pairs of the poset whose closure is `matrix` (n*n, modified in place).
std::vector<critical_pair> find_critical_pairs(int* matrix, int n);

// Build the incompatibility graph on critical pairs (two conflict if reversing
// both creates a cycle in `poset_graph`) and return whether it is bipartite.
bool check_critical_pairs_graph(const adjacency_list& poset_graph,
                                const std::vector<critical_pair>& critical_pairs);

// True iff the poset given by adjacency `g` has order dimension <= 2.
bool is_dim2(const adjacency_list& g);

} // namespace nomadim

#endif // NOMADIM_DIMENSION_HPP
