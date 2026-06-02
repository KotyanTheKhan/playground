#include "nomadim/hypergraph.hpp"
#include <algorithm>
#include <functional>
#include <stdexcept>
#include <string>

namespace nomadim {

bool reverse_set(const StrictRel& base, const std::vector<critical_pair>& cps,
                 const std::vector<int>& idxs, StrictRel& out) {
    out = base;
    for (int i : idxs)
        if (!out.add_and_close(cps[i].y, cps[i].x))   // reverse (x,y) => y<x
            return false;
    return true;
}

bool is_reversible(const StrictRel& base, const std::vector<critical_pair>& cps,
                   const std::vector<int>& idxs) {
    StrictRel out(base.n);
    return reverse_set(base, cps, idxs, out);
}

namespace {

// Is every immediate (one-element-smaller) subset of `sub` reversible? Used to
// confirm minimality while enumerating by size.
bool all_proper_subsets_reversible(const StrictRel& base,
                                   const std::vector<critical_pair>& cps,
                                   const std::vector<int>& sub) {
    for (size_t drop = 0; drop < sub.size(); ++drop) {
        std::vector<int> s;
        s.reserve(sub.size() - 1);
        for (size_t i = 0; i < sub.size(); ++i)
            if (i != drop) s.push_back(sub[i]);
        if (!is_reversible(base, cps, s)) return false;  // a smaller edge exists
    }
    return true;
}

} // namespace

std::vector<std::vector<int>>
enumerate_hyperedges(const StrictRel& base, const std::vector<critical_pair>& cps,
                     const Caps& caps) {
    int m = (int)cps.size();
    if (m > caps.max_critical_pairs)
        throw std::runtime_error("hypergraph too large: critical pairs (" +
            std::to_string(m) + ") exceed cap (" +
            std::to_string(caps.max_critical_pairs) + ")");

    std::vector<std::vector<int>> edges;
    std::vector<int> sub;
    // Enumerate subsets by increasing size; record minimal non-reversible ones.
    // Singletons are always reversible, so the smallest possible edge is size 2.
    std::function<void(int, int)> rec = [&](int start, int remaining) {
        if ((int)edges.size() >= caps.max_results) return;
        if (remaining == 0) {
            if (!is_reversible(base, cps, sub) &&
                all_proper_subsets_reversible(base, cps, sub))
                edges.push_back(sub);
            return;
        }
        for (int i = start; i <= m - remaining; ++i) {
            sub.push_back(i);
            rec(i + 1, remaining - 1);
            sub.pop_back();
            if ((int)edges.size() >= caps.max_results) return;
        }
    };
    for (int size = 2; size <= m && (int)edges.size() < caps.max_results; ++size)
        rec(0, size);
    return edges;
}

} // namespace nomadim
