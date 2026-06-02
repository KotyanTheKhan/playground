#include "nomadim/hypergraph.hpp"

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

} // namespace nomadim
