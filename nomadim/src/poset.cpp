#include "nomadim/poset.hpp"
#include "nomadim/process_graph.hpp"
#include "nomadim/dimension.hpp"   // have_cycle
#include <stdexcept>
#include <string>

namespace nomadim {

void Poset::validate() const {
    if (n_vertices < 0)
        throw std::invalid_argument("n_vertices must be non-negative");
    if ((int)edges.size() != n_vertices)
        throw std::invalid_argument("edges.size() must equal n_vertices");
    for (int u = 0; u < n_vertices; ++u)
        for (int v : edges[u])
            if (v < 0 || v >= n_vertices)
                throw std::invalid_argument("edge endpoint out of range");
    if (have_cycle(edges))
        throw std::invalid_argument("poset cover relation must be acyclic");
}

Poset Poset::from(const ProcessGraph& g) {
    Poset p;
    p.n_vertices = (int)g.graph.size();
    p.edges = g.graph;
    return p;
}

} // namespace nomadim
