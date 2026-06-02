#include "nomadim/dimension.hpp"
#include "nomadim/floyd.hpp"
#include "nomadim/hypergraph.hpp"
#include "nomadim/order_relation.hpp"
#include <functional>
#include <vector>
#include <cstring>
#include <stdexcept>

namespace nomadim {

bool have_cycle(const adjacency_list& g) {
    std::vector<bool> used(g.size(), false), cur_way(g.size(), false);
    std::function<bool(int)> dfs = [&](int v) -> bool {
        used[v] = true;
        cur_way[v] = true;
        for (int u : g[v]) {
            if (cur_way[u]) return true;
            if (!used[u] && dfs(u)) return true;
        }
        cur_way[v] = false;
        return false;
    };
    for (int i = 0; i < (int)g.size(); ++i)
        if (!used[i] && dfs(i)) return true;
    return false;
}

bool is_bipartite(const adjacency_list& g) {
    std::vector<int> label(g.size(), -1);
    std::function<bool(int,int)> dfs = [&](int v, int lbl) -> bool {
        label[v] = lbl;
        int nl = lbl == 0 ? 1 : 0;
        for (int u : g[v]) {
            if (label[u] != -1 && label[u] != nl) return false;
            if (label[u] == -1 && !dfs(u, nl)) return false;
        }
        return true;
    };
    for (int i = 0; i < (int)g.size(); ++i)
        if (label[i] == -1 && !dfs(i, 0)) return false;
    return true;
}

bool check_if_critical(const int* matrix, int n, int x, int y) {
    std::vector<int> nm(matrix, matrix + n * n);
    nm[x * n + y] = 1;
    floyd_advance_vertex(nm.data(), n, x);
    floyd_advance_vertex(nm.data(), n, y);
    for (int v = 0; v < n; ++v)
        for (int u = 0; u < n; ++u) {
            if (v == x && u == y) continue;
            if (matrix[v * n + u] == INF && nm[v * n + u] != INF) return false;
        }
    return true;
}

std::vector<critical_pair> find_critical_pairs(int* matrix, int n) {
    std::vector<critical_pair> cps;
    floyd(matrix, n);
    for (int v = 0; v < n; ++v)
        for (int u = 0; u < n; ++u)
            if (matrix[v * n + u] == INF && matrix[u * n + v] == INF)
                if (check_if_critical(matrix, n, v, u))
                    cps.push_back({v, u});
    return cps;
}

bool check_critical_pairs_graph(const adjacency_list& poset_graph,
                                const std::vector<critical_pair>& cps) {
    adjacency_list icg(cps.size());
    // Reuse a single working copy of the poset graph: add the two reversal
    // edges, test for a cycle, then pop them (reverse push order) to restore.
    // Avoids an O(V+E) deep copy for every one of the O(cps^2) pairs.
    adjacency_list lg = poset_graph;
    for (size_t i = 0; i < cps.size(); ++i)
        for (size_t j = i + 1; j < cps.size(); ++j) {
            lg[cps[i].y].push_back(cps[i].x);
            lg[cps[j].y].push_back(cps[j].x);
            bool cyc = have_cycle(lg);
            lg[cps[j].y].pop_back();
            lg[cps[i].y].pop_back();
            if (cyc) {
                icg[i].push_back((int)j);
                icg[j].push_back((int)i);
            }
        }
    return is_bipartite(icg);
}

bool is_dim2(const adjacency_list& g) {
    std::vector<int> matrix = make_graph_matrix(g);
    int n = (int)g.size();
    // find_critical_pairs closes the matrix itself, so no pre-floyd here.
    auto cps = find_critical_pairs(matrix.data(), n);
    return check_critical_pairs_graph(g, cps);
}

namespace {

// Build the realizer induced by a coloring: for each color class, reverse its
// pairs on top of the base order and read off a deterministic linear extension.
Coloring make_coloring(const StrictRel& base, const std::vector<critical_pair>& cps,
                       const std::vector<int>& colors, int k) {
    Coloring out;
    out.classes.assign(k, {});
    for (size_t i = 0; i < cps.size(); ++i) out.classes[colors[i]].push_back(cps[i]);
    for (int c = 0; c < k; ++c) {
        std::vector<int> idxs;
        for (size_t i = 0; i < cps.size(); ++i) if (colors[i] == c) idxs.push_back((int)i);
        StrictRel cls(base.n);
        reverse_set(base, cps, idxs, cls);     // valid coloring => always succeeds
        out.realizer.push_back(topo_order(cls));
    }
    return out;
}

} // namespace

DimensionResult analyze_dimension(const adjacency_list& g, const Caps& caps,
                                  bool with_colorings) {
    int n = (int)g.size();
    if (n > caps.max_vertices)
        throw std::runtime_error("poset too large: vertices (" + std::to_string(n) +
            ") exceed cap (" + std::to_string(caps.max_vertices) + ")");

    DimensionResult dr;
    std::vector<int> matrix = make_graph_matrix(g);
    dr.critical_pairs = find_critical_pairs(matrix.data(), n);   // closes matrix
    StrictRel base = base_order(g);

    if (dr.critical_pairs.empty()) {
        // No incomparable pairs -> a chain. dim 1 (or 0 for the empty poset).
        dr.dimension = (n == 0) ? 0 : 1;
        if (n > 0 && with_colorings) {
            Coloring c; c.realizer.push_back(topo_order(base));
            dr.colorings.push_back(std::move(c));
        }
        return dr;
    }

    if (!with_colorings) {
        // Fast path: dimension only, skip the costly hyperedge / coloring work.
        dr.dimension = chromatic_number(base, dr.critical_pairs, caps);
        return dr;
    }

    dr.hyperedges = enumerate_hyperedges(base, dr.critical_pairs, caps);
    dr.dimension = chromatic_number(base, dr.critical_pairs, caps);
    auto colorings = enumerate_min_colorings(base, dr.critical_pairs, dr.dimension, caps);
    for (const auto& colors : colorings)
        dr.colorings.push_back(make_coloring(base, dr.critical_pairs, colors, dr.dimension));
    return dr;
}

int dimension(const adjacency_list& g, const Caps& caps) {
    return analyze_dimension(g, caps, /*with_colorings=*/false).dimension;
}

bool dimension_at_most(const adjacency_list& g, int k, const Caps& caps) {
    int n = (int)g.size();
    if (n > caps.max_vertices)
        throw std::runtime_error("poset too large: vertices (" + std::to_string(n) +
            ") exceed cap (" + std::to_string(caps.max_vertices) + ")");
    std::vector<int> matrix = make_graph_matrix(g);
    std::vector<critical_pair> cps = find_critical_pairs(matrix.data(), n);
    if (cps.empty()) return k >= 1;        // chain: dimension <= 1
    StrictRel base = base_order(g);
    return colorable_with(base, cps, k, caps);
}

} // namespace nomadim
