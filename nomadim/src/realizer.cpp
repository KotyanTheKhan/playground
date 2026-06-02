#include "nomadim/realizer.hpp"
#include "nomadim/order_relation.hpp"
#include <utility>
#include <vector>

namespace nomadim {
namespace {

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
