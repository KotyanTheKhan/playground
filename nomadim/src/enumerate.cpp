#include "nomadim/enumerate.hpp"
#include "nomadim/floyd.hpp"
#include "nomadim/dimension.hpp"
#include "nomadim/isomorphism.hpp"

#include <boost/fiber/all.hpp>
#include <unordered_set>
#include <mutex>
#include <thread>
#include <atomic>
#include <vector>
#include <cstddef>

namespace nomadim {
namespace bf = boost::fibers;

bool is_full_synchronized(const ProcessGraph& g) {
    std::vector<int> m = make_graph_matrix(g.graph);
    int n = (int)g.graph.size();
    floyd(m.data(), n);
    for (int start = 0; start < g.proc_num; ++start)
        for (int last : g.proc_last_vertex)
            if (m[start * n + last] == INF) return false;
    return true;
}

namespace {

// Hash for the canonical per-process sync signature (the prune-cache key).
struct PEHashHash {
    size_t operator()(const ProcessGraph::PEHash& s) const noexcept {
        std::hash<std::string> h;
        size_t ret = 0;
        for (auto const& x : s)
            ret ^= h(x) + 0x9e3779b97f4a7c15ULL + (ret << 6) + (ret >> 2);
        return ret;
    }
};

// State shared across all worker threads / fibers of one enumerate() call.
// Guarded by std::mutex because fibers on different threads run on independent
// schedulers; the locked regions contain no fiber-suspension points, so they
// cannot interleave other fibers of the same thread.
struct EnumState {
    int max_sync = 0;
    std::unordered_set<ProcessGraph::PEHash, PEHashHash> cache;
    std::mutex cache_mut;
    std::mutex rp_mut;
    std::vector<ProcessGraph> results;
    std::atomic<int> count{0};
    std::atomic<int> iso_hits{0};
};

// Plain recursive search of one subtree: extend the execution by every sync
// pair, prune by the shared canonical sync-name cache, and on full
// synchronization test dimension-2 and dedup by isomorphism. Faithful to the
// upstream enumeration; the count is independent of how branches are
// distributed across fibers/threads (the cache+dedup are order-independent).
void search(EnumState& st, ProcessGraph g, int sync_num) {
    if (sync_num > st.max_sync) return;

    {
        std::lock_guard<std::mutex> lk(st.cache_mut);
        auto key = canonical_sync_name(g);
        if (st.cache.find(key) != st.cache.end()) return;
        st.cache.insert(std::move(key));
    }

    if (is_full_synchronized(g)) {
        if (is_dim2(g.graph)) {
            bool iso = false;
            {
                std::lock_guard<std::mutex> lk(st.rp_mut);
                for (auto const& p : st.results)
                    if (is_isomorphic(p, g)) { iso = true; break; }
                if (!iso) st.results.push_back(g);
            }
            if (iso) st.iso_hits.fetch_add(1);
            else     st.count.fetch_add(1);
        }
        return;
    }

    int proc_num = g.proc_num;
    for (int p1 = 0; p1 < proc_num; ++p1)
        for (int p2 = p1 + 1; p2 < proc_num; ++p2) {
            ProcessGraph ng = g;
            ng.sync(p1, p2);
            search(st, std::move(ng), sync_num + 1);
        }
}

} // namespace

// Multithreaded + multifibered: the first-level branches are partitioned across
// `threads` OS threads (multithreaded); within each thread every assigned
// branch runs as its own boost::fiber on that thread's default (round-robin)
// scheduler (multifibered). The default scheduler keeps no process-global
// state, so it is safe to spin threads up and down on every call (unlike the
// work-stealing scheduler, whose global registry corrupts across repeated
// short-lived threads).
EnumerateResult enumerate(int n_procs, int max_sync, unsigned threads) {
    if (threads < 1) threads = 1;

    EnumState st;
    st.max_sync = max_sync;

    ProcessGraph root;
    root.init(n_procs);

    std::vector<ProcessGraph> branches;
    if (!is_full_synchronized(root)) {
        for (int p1 = 0; p1 < n_procs; ++p1)
            for (int p2 = p1 + 1; p2 < n_procs; ++p2) {
                ProcessGraph child = root;
                child.sync(p1, p2);
                branches.push_back(std::move(child));
            }
    }

    if (branches.empty()) {
        // Degenerate (e.g. a single process): no branching needed.
        search(st, std::move(root), 0);
    } else {
        const unsigned tc = std::min<unsigned>(threads, (unsigned)branches.size());
        std::vector<std::thread> pool;
        pool.reserve(tc);
        for (unsigned t = 0; t < tc; ++t) {
            pool.emplace_back([&st, &branches, t, tc] {
                // 8 MiB fiber stacks: each fiber runs the recursive search plus
                // is_dim2 / have_cycle (recursive DFS).
                bf::fixedsize_stack salloc{ 8 * 1024 * 1024 };
                std::vector<bf::fiber> fibers;
                for (size_t i = t; i < branches.size(); i += tc) {
                    ProcessGraph g = branches[i];
                    fibers.emplace_back(
                        bf::launch::post,
                        std::allocator_arg, salloc,
                        [&st, g]() mutable { search(st, std::move(g), 1); });
                }
                for (auto& f : fibers) f.join();
            });
        }
        for (auto& th : pool) th.join();
    }

    EnumerateResult result;
    result.count = st.count.load();
    result.isomorphic_hits = st.iso_hits.load();
    result.results = std::move(st.results);
    return result;
}

} // namespace nomadim
