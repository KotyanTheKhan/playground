#include "cmd_dimension.hpp"
#include "nomadim/io.hpp"
#include "nomadim/process_graph.hpp"
#include "nomadim/dimension.hpp"
#include "nomadim/realizer.hpp"
#include <iostream>

namespace nomadim {

namespace {
void print_realizer(const std::vector<std::vector<int>>& realizer) {
    for (size_t i = 0; i < realizer.size(); ++i) {
        std::cout << "    L" << (i + 1) << ": [";
        for (size_t j = 0; j < realizer[i].size(); ++j)
            std::cout << (j ? ", " : "") << realizer[i][j];
        std::cout << "]\n";
    }
}
} // namespace

int cmd_dimension(const std::string& path, bool show_realizers, bool show_all,
                  int max_vertices, const std::string& out_path, bool quick, int max_cpairs,
                  int le_k) {
    Document d = load_file(path);
    adjacency_list adj;
    if (d.poset) adj = d.poset->edges;
    else         adj = ProcessGraph::build(*d.execution).graph;

    Caps caps; caps.max_vertices = max_vertices; caps.max_critical_pairs = max_cpairs;

    if (le_k > 0) {
        // "Is dimension <= K?" -- cheap when yes (early-exit K-coloring).
        bool ok = dimension_at_most(adj, le_k, caps);
        std::cout << "Vertices: " << adj.size() << "\n";
        std::cout << "Dimension <= " << le_k << ": " << (ok ? "yes" : "no") << "\n";
        return ok ? 0 : 2;
    }

    if (quick) {
        // Fast path: dimension only, no hyperedge/coloring enumeration.
        DimensionResult dr = analyze_dimension(adj, caps, /*with_colorings=*/false);
        std::cout << "Vertices: " << adj.size() << "\n";
        std::cout << "Dimension: " << dr.dimension << "\n";
        return 0;
    }

    DimensionResult dr = analyze_dimension(adj, caps);

    std::cout << "Vertices: " << adj.size() << "\n";
    std::cout << "Critical pairs: " << dr.critical_pairs.size() << "\n";
    std::cout << "Hyperedges: " << dr.hyperedges.size() << "\n";
    std::cout << "Dimension: " << dr.dimension << "\n";

    if (show_all) {
        std::cout << "Minimum colorings: " << dr.colorings.size() << "\n";
        for (size_t c = 0; c < dr.colorings.size(); ++c) {
            std::cout << "  coloring " << c << ":\n";
            print_realizer(dr.colorings[c].realizer);
        }
    } else if (show_realizers && !dr.colorings.empty()) {
        std::cout << "Realizer:\n";
        print_realizer(dr.colorings.front().realizer);
    }

    if (!out_path.empty()) {
        Document outd;
        outd.poset = d.poset;
        outd.execution = d.execution;
        Meta meta = d.meta.value_or(Meta{});      // keep existing notes
        meta.dimension = dr.dimension;
        std::vector<std::vector<std::vector<int>>> rs;
        for (const auto& col : dr.colorings) rs.push_back(col.realizer);
        meta.realizers = std::move(rs);
        meta.source_hash = poset_hash(adj);
        outd.meta = std::move(meta);
        save_file(out_path, dump_document(outd));
    }
    return 0;
}

} // namespace nomadim
