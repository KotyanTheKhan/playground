#include "cmd_check.hpp"
#include "nomadim/io.hpp"
#include "nomadim/process_graph.hpp"
#include "nomadim/dimension.hpp"
#include "nomadim/floyd.hpp"
#include <iostream>

namespace nomadim {

int cmd_check(const std::string& path) {
    Document d = load_file(path);
    adjacency_list adj;
    if (d.poset) {
        adj = d.poset->edges;
    } else {
        ProcessGraph g = ProcessGraph::build(*d.execution);
        adj = g.graph;
    }
    std::vector<int> m = make_graph_matrix(adj);
    int n = (int)adj.size();
    floyd(m.data(), n);
    auto cps = find_critical_pairs(m.data(), n);
    bool dim2 = check_critical_pairs_graph(adj, cps);

    std::cout << "Vertices: " << n << "\n";
    std::cout << "Critical pairs: " << cps.size() << "\n";
    for (size_t i = 0; i < cps.size(); ++i)
        std::cout << "  " << i << ": " << cps[i].x << " " << cps[i].y << "\n";
    std::cout << (dim2 ? "Dimension <= 2: YES" : "Dimension <= 2: NO") << "\n";
    return dim2 ? 0 : 2;
}

} // namespace nomadim
