#include "nomadim/isomorphism.hpp"
#include <algorithm>
#include <numeric>

namespace nomadim {

bool is_isomorphic(const ProcessGraph& pgl, const ProcessGraph& pgr) {
    if (pgl.proc_num != pgr.proc_num) return false;
    if (pgl.graph.size() != pgr.graph.size()) return false;
    if (pgl.proc_verteces.size() != pgr.proc_verteces.size()) return false;
    if (pgl.labels.size() != pgr.labels.size()) return false;

    std::vector<int> perm(pgr.proc_num);
    std::iota(perm.begin(), perm.end(), 0);

    bool isomorphic = false;
    do {
        bool sizes_ok = true;
        for (size_t i = 0; i < pgl.proc_verteces.size() && sizes_ok; ++i)
            if (pgl.proc_verteces[i].size() != pgr.proc_verteces[perm[i]].size())
                sizes_ok = false;
        if (!sizes_ok) continue;

        bool labels_ok = true;
        for (int p = 0; p < (int)pgl.proc_verteces.size() && labels_ok; ++p) {
            for (size_t i = 0; i < pgl.proc_verteces[p].size() && labels_ok; ++i) {
                int vl = pgl.proc_verteces[p][i];
                int vr = pgr.proc_verteces[perm[p]][i];
                if (pgl.labels[vl].num != pgr.labels[vr].num) { labels_ok = false; break; }
                if (pgl.graph[vl].size() != pgr.graph[vr].size()) { labels_ok = false; break; }
                if (!pgl.graph[vl].empty()) {
                    int vls = pgl.graph[vl][0];
                    int vrs = pgr.graph[vr][0];
                    int vlas1 = pgl.graph[vls][0], vlas2 = pgl.graph[vls][1];
                    int vras1 = pgr.graph[vrs][0], vras2 = pgr.graph[vrs][1];
                    int vlo = (pgl.labels[vlas1].proc == p) ? vlas2 : vlas1;
                    int vro = (pgr.labels[vras1].proc == perm[p]) ? vras2 : vras1;
                    if (perm[pgl.labels[vlo].proc] != pgr.labels[vro].proc ||
                        pgl.labels[vlo].num != pgr.labels[vro].num) {
                        labels_ok = false; break;
                    }
                }
            }
        }
        if (!labels_ok) continue;
        isomorphic = true;
    } while (!isomorphic && std::next_permutation(perm.begin(), perm.end()));

    return isomorphic;
}

std::vector<ProcessGraph> generate_all_isomorphic(const ProcessGraph& pg) {
    std::vector<int> perm(pg.proc_num);
    std::iota(perm.begin(), perm.end(), 0);
    std::vector<ProcessGraph> ret;
    do {
        ProcessGraph npg;
        npg.init(pg.proc_num);
        for (auto const& s : pg.syncs)
            npg.sync(std::min(perm[s.first], perm[s.second]),
                     std::max(perm[s.first], perm[s.second]));
        ret.push_back(npg);
    } while (std::next_permutation(perm.begin(), perm.end()));
    return ret;
}

ProcessGraph::PEHash canonical_sync_name(const ProcessGraph& pg) {
    auto names = pg.proc_sync_name;
    std::sort(names.begin(), names.end());
    return names;
}

} // namespace nomadim
