#ifndef NOMADIM_FLOYD_HPP
#define NOMADIM_FLOYD_HPP

#include "nomadim/types.hpp"
#include <vector>

namespace nomadim {

// Build an n*n distance matrix (row-major) from an adjacency list:
// 0 on the diagonal, 1 for each edge, INF otherwise.
std::vector<int> make_graph_matrix(const adjacency_list& g);

// Floyd-Warshall all-pairs shortest paths in place.
void floyd(int* matrix, int n);

// Relax only paths passing through vertex v (used by critical-pair test).
void floyd_advance_vertex(int* matrix, int n, int v);

} // namespace nomadim

#endif // NOMADIM_FLOYD_HPP
