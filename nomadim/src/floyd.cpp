#include "nomadim/floyd.hpp"

namespace nomadim {

std::vector<int> make_graph_matrix(const adjacency_list& g) {
    int n = (int)g.size();
    std::vector<int> matrix(n * n, INF);
    for (int i = 0; i < n; ++i) matrix[i * n + i] = 0;
    for (int v = 0; v < n; ++v)
        for (int u : g[v]) matrix[v * n + u] = 1;
    return matrix;
}

void floyd(int* matrix, int n) {
    for (int k = 0; k < n; ++k)
        for (int i = 0; i < n; ++i) {
            int v = matrix[i * n + k];
            for (int j = 0; j < n; ++j) {
                int val = v + matrix[k * n + j];
                if (matrix[i * n + j] > val) matrix[i * n + j] = val;
            }
        }
}

void floyd_advance_vertex(int* matrix, int n, int v) {
    int k = v;
    for (int i = 0; i < n; ++i) {
        int vv = matrix[i * n + k];
        for (int j = 0; j < n; ++j) {
            int val = vv + matrix[k * n + j];
            if (matrix[i * n + j] > val) matrix[i * n + j] = val;
        }
    }
}

} // namespace nomadim
