#include "nomadim/realizer.hpp"
#include <utility>
#include <vector>

namespace nomadim {
namespace {

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

// Linearize a total strict order into a permutation, least element first.
// In a total order each element has a distinct number of elements below it.
std::vector<int> linearize(const StrictRel& r) {
    int n = r.n;
    std::vector<int> below(n, 0), order(n);
    for (int a = 0; a < n; ++a)
        for (int b = 0; b < n; ++b)
            if (r.less(a, b)) below[b]++;
    for (int e = 0; e < n; ++e) order[below[e]] = e;
    return order;
}

struct Solver {
    std::vector<std::pair<int, int>> pairs;   // incomparable pairs (u < v by index)
    Realizer result;

    bool solve(int idx, StrictRel r1, StrictRel r2) {
        if (idx == (int)pairs.size()) {
            result.dim_le_2 = true;
            result.l1 = linearize(r1);
            result.l2 = linearize(r2);
            return true;
        }
        int u = pairs[idx].first, v = pairs[idx].second;
        // Branch A: u<v in L1, v<u in L2.
        {
            StrictRel a1 = r1, a2 = r2;
            if (a1.add_and_close(u, v) && a2.add_and_close(v, u) &&
                solve(idx + 1, std::move(a1), std::move(a2)))
                return true;
        }
        // Branch B: v<u in L1, u<v in L2.
        {
            StrictRel b1 = r1, b2 = r2;
            if (b1.add_and_close(v, u) && b2.add_and_close(u, v) &&
                solve(idx + 1, std::move(b1), std::move(b2)))
                return true;
        }
        return false;
    }
};

} // namespace

Realizer find_realizer(const adjacency_list& g) {
    int n = (int)g.size();
    StrictRel base(n);
    for (int u = 0; u < n; ++u)
        for (int v : g[u])
            base.add_and_close(u, v);   // seed direct edges, close to full order

    Solver s;
    for (int u = 0; u < n; ++u)
        for (int v = u + 1; v < n; ++v)
            if (!base.less(u, v) && !base.less(v, u))
                s.pairs.push_back({u, v});

    if (s.solve(0, base, base)) return s.result;
    return Realizer{false, {}, {}};
}

} // namespace nomadim
