#include "nomadim/dimension.hpp"
#include "nomadim/floyd.hpp"
#include <functional>
#include <vector>
#include <cstring>

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
    for (size_t i = 0; i < cps.size(); ++i)
        for (size_t j = i + 1; j < cps.size(); ++j) {
            adjacency_list lg = poset_graph;
            lg[cps[i].y].push_back(cps[i].x);
            lg[cps[j].y].push_back(cps[j].x);
            if (have_cycle(lg)) {
                icg[i].push_back((int)j);
                icg[j].push_back((int)i);
            }
        }
    return is_bipartite(icg);
}

bool is_dim2(const adjacency_list& g) {
    std::vector<int> matrix = make_graph_matrix(g);
    int n = (int)g.size();
    floyd(matrix.data(), n);
    auto cps = find_critical_pairs(matrix.data(), n);
    return check_critical_pairs_graph(g, cps);
}

} // namespace nomadim
