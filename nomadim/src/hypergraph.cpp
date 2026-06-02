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
    // Subset enumeration is worst-case exponential in m, so bound the number of
    // candidate sets evaluated (defence-in-depth: the dimension itself comes from
    // chromatic_number, not from this list). When the budget is spent we return
    // the edges found so far — for visualization a partial list is acceptable.
    long budget = (long)caps.max_results * 200;
    bool stop = false;
    // Enumerate subsets by increasing size; record minimal non-reversible ones.
    // Singletons are always reversible, so the smallest possible edge is size 2.
    std::function<void(int, int)> rec = [&](int start, int remaining) {
        if (stop || (int)edges.size() >= caps.max_results) return;
        if (remaining == 0) {
            if (--budget < 0) { stop = true; return; }
            if (!is_reversible(base, cps, sub) &&
                all_proper_subsets_reversible(base, cps, sub))
                edges.push_back(sub);
            return;
        }
        for (int i = start; i <= m - remaining; ++i) {
            sub.push_back(i);
            rec(i + 1, remaining - 1);
            sub.pop_back();
            if (stop || (int)edges.size() >= caps.max_results) return;
        }
    };
    for (int size = 2; size <= m && !stop && (int)edges.size() < caps.max_results; ++size)
        rec(0, size);
    return edges;
}

namespace {

// Backtracking proper coloring: colors[i] in [0,k). A partial assignment is
// valid iff every color class is reversible. With want_all=false the search
// stops at the first complete coloring (chromatic test); with want_all=true it
// collects every canonical coloring that uses exactly k colors.
struct Colorer {
    const StrictRel& base;
    const std::vector<critical_pair>& cps;
    int k, m, max_results;
    std::vector<int> colors;
    std::vector<std::vector<int>> all;
    bool want_all;

    bool class_reversible(int c, int upto) {
        std::vector<int> idxs;
        for (int j = 0; j <= upto; ++j) if (colors[j] == c) idxs.push_back(j);
        return is_reversible(base, cps, idxs);
    }

    // Returns true to signal the caller should stop searching.
    bool rec(int i, int used) {
        if (i == m) {
            if (!want_all) return true;                       // found one
            if (used == k) all.push_back(colors);
            return (int)all.size() >= max_results;
        }
        int limit = std::min(k, used + 1);                    // canonical labels
        for (int c = 0; c < limit; ++c) {
            colors[i] = c;
            if (class_reversible(c, i)) {
                // stop == "found one" (chromatic test) or "results full" (enum).
                if (rec(i + 1, c == used ? used + 1 : used)) return true;
            }
        }
        colors[i] = -1;
        return false;
    }
};

} // namespace

int chromatic_number(const StrictRel& base, const std::vector<critical_pair>& cps,
                     const Caps& caps) {
    int m = (int)cps.size();
    if (m > caps.max_critical_pairs)
        throw std::runtime_error("hypergraph too large: critical pairs (" +
            std::to_string(m) + ") exceed cap (" +
            std::to_string(caps.max_critical_pairs) + ")");
    for (int k = 2; k <= m; ++k) {
        Colorer col{base, cps, k, m, caps.max_results, std::vector<int>(m, -1), {}, false};
        if (col.rec(0, 0)) return k;
    }
    return m;   // every singleton its own color (unreachable for valid posets)
}

std::vector<std::vector<int>>
enumerate_min_colorings(const StrictRel& base, const std::vector<critical_pair>& cps,
                        int k, const Caps& caps) {
    int m = (int)cps.size();
    if (m > caps.max_critical_pairs)
        throw std::runtime_error("hypergraph too large: critical pairs (" +
            std::to_string(m) + ") exceed cap (" +
            std::to_string(caps.max_critical_pairs) + ")");
    Colorer col{base, cps, k, m, caps.max_results, std::vector<int>(m, -1), {}, true};
    col.rec(0, 0);
    return col.all;
}

} // namespace nomadim
