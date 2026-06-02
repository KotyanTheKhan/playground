#ifndef NOMADIM_ORDER_RELATION_HPP
#define NOMADIM_ORDER_RELATION_HPP

#include "nomadim/types.hpp"
#include <vector>

namespace nomadim {

// Dense strict partial order on n elements: lt[a*n+b] == 1 means a < b.
struct StrictRel {
    int n;
    std::vector<char> lt;
    explicit StrictRel(int n_) : n(n_), lt((size_t)n_ * n_, 0) {}
    bool less(int a, int b) const { return lt[(size_t)a * n + b] != 0; }

    // Add a<b and re-close transitively. Returns false if this creates a cycle
    // (b<a already held, or the closure forces some element below itself).
    bool add_and_close(int a, int b) {
        if (less(a, b)) return true;
        if (less(b, a)) return false;
        lt[(size_t)a * n + b] = 1;
        bool changed = true;
        while (changed) {
            changed = false;
            for (int i = 0; i < n; ++i)
                for (int j = 0; j < n; ++j) {
                    if (!lt[(size_t)i * n + j]) continue;
                    for (int k = 0; k < n; ++k)
                        if (lt[(size_t)j * n + k] && !lt[(size_t)i * n + k]) {
                            if (i == k) return false;   // i < ... < i : cycle
                            lt[(size_t)i * n + k] = 1;
                            changed = true;
                        }
                }
        }
        return true;
    }
};

// Build the closed strict order of adjacency `g` (edge u->v means u < v).
inline StrictRel base_order(const adjacency_list& g) {
    StrictRel r((int)g.size());
    for (int u = 0; u < (int)g.size(); ++u)
        for (int v : g[u]) r.add_and_close(u, v);
    return r;
}

// Linearize a TOTAL strict order into a permutation, least element first.
// In a total order each element has a distinct number of elements below it.
inline std::vector<int> linearize(const StrictRel& r) {
    int n = r.n;
    std::vector<int> below(n, 0), order(n);
    for (int a = 0; a < n; ++a)
        for (int b = 0; b < n; ++b)
            if (r.less(a, b)) below[b]++;
    for (int e = 0; e < n; ++e) order[below[e]] = e;
    return order;
}

// Deterministic linear extension of the (possibly partial) order r: repeatedly
// emit the smallest-indexed not-yet-placed element with no unplaced predecessor.
inline std::vector<int> topo_order(const StrictRel& r) {
    int n = r.n;
    std::vector<char> placed(n, 0);
    std::vector<int> order;
    order.reserve(n);
    for (int step = 0; step < n; ++step)
        for (int c = 0; c < n; ++c) {
            if (placed[c]) continue;
            bool minimal = true;
            for (int d = 0; d < n; ++d)
                if (!placed[d] && d != c && r.less(d, c)) { minimal = false; break; }
            if (minimal) { placed[c] = 1; order.push_back(c); break; }
        }
    return order;
}

} // namespace nomadim

#endif // NOMADIM_ORDER_RELATION_HPP
