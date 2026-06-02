#include "nomadim/oracle.hpp"
#include "nomadim/order_relation.hpp"
#include <vector>
#include <functional>

namespace nomadim {
namespace {

// All linear extensions of the partial order `base`, as position vectors:
// pos[e] = rank of e. Backtracking over all topological orders.
std::vector<std::vector<int>> all_extensions(const StrictRel& base) {
    int n = base.n;
    std::vector<std::vector<int>> exts;
    std::vector<int> order;
    std::vector<char> placed(n, 0);
    std::function<void()> rec = [&]() {
        if ((int)order.size() == n) {
            std::vector<int> pos(n);
            for (int i = 0; i < n; ++i) pos[order[i]] = i;
            exts.push_back(std::move(pos));
            return;
        }
        for (int c = 0; c < n; ++c) {
            if (placed[c]) continue;
            bool minimal = true;
            for (int d = 0; d < n; ++d)
                if (!placed[d] && d != c && base.less(d, c)) { minimal = false; break; }
            if (!minimal) continue;
            placed[c] = 1; order.push_back(c);
            rec();
            order.pop_back(); placed[c] = 0;
        }
    };
    rec();
    return exts;
}

// Does the chosen subset of extensions intersect to exactly `base`?
bool realizes(const StrictRel& base, const std::vector<std::vector<int>>& exts,
              const std::vector<int>& chosen) {
    int n = base.n;
    for (int a = 0; a < n; ++a)
        for (int b = 0; b < n; ++b) {
            if (a == b) continue;
            bool in_all = true;
            for (int idx : chosen)
                if (!(exts[idx][a] < exts[idx][b])) { in_all = false; break; }
            if (in_all != base.less(a, b)) return false;
        }
    return true;
}

} // namespace

int oracle_dimension(const adjacency_list& g) {
    int n = (int)g.size();
    if (n <= 1) return n == 0 ? 0 : 1;
    StrictRel base = base_order(g);
    auto exts = all_extensions(base);
    int E = (int)exts.size();
    if (E == 1) return 1;   // total order
    // Smallest subset of extensions whose intersection is the order.
    for (int k = 1; k <= E; ++k) {
        std::vector<int> chosen(k);
        std::function<bool(int,int)> pick = [&](int start, int depth) -> bool {
            if (depth == k) return realizes(base, exts, chosen);
            for (int i = start; i <= E - (k - depth); ++i) {
                chosen[depth] = i;
                if (pick(i + 1, depth + 1)) return true;
            }
            return false;
        };
        if (pick(0, 0)) return k;
    }
    return E;
}

} // namespace nomadim
