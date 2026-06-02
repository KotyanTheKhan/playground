#ifndef NOMADIM_DIMENSION_HPP
#define NOMADIM_DIMENSION_HPP

#include "nomadim/types.hpp"
#include "nomadim/hypergraph.hpp"
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

// One minimum proper coloring of the critical-pair hypergraph, plus the realizer
// (one linear extension per reversible color class) it induces.
struct Coloring {
    std::vector<std::vector<critical_pair>> classes;   // dimension reversible classes
    std::vector<std::vector<int>> realizer;            // dimension linear extensions
};

// Full analysis of a poset's order dimension.
struct DimensionResult {
    int dimension = 0;
    std::vector<critical_pair> critical_pairs;
    std::vector<std::vector<int>> hyperedges;          // indices into critical_pairs
    std::vector<Coloring> colorings;                   // minimum colorings (capped)
};

// Compute the dimension, critical pairs, hyperedges, and all minimum colorings
// (each with its induced realizer) of the poset given by adjacency `g`.
// Precondition: `g` is acyclic. Throws std::runtime_error if `g` exceeds the caps.
DimensionResult analyze_dimension(const adjacency_list& g, const Caps& caps = Caps{});

// Convenience: just the dimension number.
int dimension(const adjacency_list& g, const Caps& caps = Caps{});

} // namespace nomadim

#endif // NOMADIM_DIMENSION_HPP
