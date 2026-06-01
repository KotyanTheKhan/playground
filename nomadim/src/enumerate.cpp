#include "nomadim/enumerate.hpp"
#include "nomadim/floyd.hpp"
#include "nomadim/dimension.hpp"
#include "nomadim/isomorphism.hpp"

#include <unordered_set>
#include <map>
#include <array>
#include <deque>
#include <mutex>
#include <condition_variable>
#include <thread>
#include <atomic>
#include <vector>
#include <algorithm>
#include <cstddef>

namespace nomadim {

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

// Cheap isomorphism invariant for bucketing results: isomorphic process graphs
// share the same total vertex count and the same multiset of per-process event
// counts, so is_isomorphic only needs to compare within a bucket.
using IsoKey = std::vector<int>;
IsoKey iso_key(const ProcessGraph& g) {
    IsoKey key;
    key.reserve(g.proc_verteces.size() + 1);
    key.push_back((int)g.graph.size());
    for (auto const& pv : g.proc_verteces) key.push_back((int)pv.size());
    std::sort(key.begin() + 1, key.end());
    return key;
}

// The prune cache is sharded so the per-node hot path does not become a single
// lock convoy that serializes all worker threads onto one core.
constexpr size_t NSHARD = 64;
struct CacheShard {
    std::mutex mut;
    std::unordered_set<ProcessGraph::PEHash, PEHashHash> set;
};

struct EnumState {
    int max_sync = 0;
    int parallel_cutoff = 0;   // queue children of nodes shallower than this
    std::array<CacheShard, NSHARD> cache;
    std::mutex rp_mut;
    std::map<IsoKey, std::vector<ProcessGraph>> buckets;
    std::atomic<int> count{0};
    std::atomic<int> iso_hits{0};
};

// Insert g's canonical sync-name into the cache; return true if it was new
// (caller should process it), false if already seen (prune).
bool cache_insert(EnumState& st, const ProcessGraph& g) {
    auto key = canonical_sync_name(g);
    size_t h = PEHashHash{}(key);
    CacheShard& shard = st.cache[h % NSHARD];
    std::lock_guard<std::mutex> lk(shard.mut);
    if (shard.set.find(key) != shard.set.end()) return false;
    shard.set.insert(std::move(key));
    return true;
}

// A fully-synchronized node: test dimension-2 and dedup by isomorphism.
void handle_full_sync(EnumState& st, const ProcessGraph& g) {
    if (!is_dim2(g.graph)) return;
    IsoKey key = iso_key(g);
    bool iso = false;
    {
        std::lock_guard<std::mutex> lk(st.rp_mut);
        auto& bucket = st.buckets[key];
        for (auto const& p : bucket)
            if (is_isomorphic(p, g)) { iso = true; break; }
        if (!iso) bucket.push_back(g);
    }
    if (iso) st.iso_hits.fetch_add(1);
    else     st.count.fetch_add(1);
}

// Fine-grained work pool (std::thread). Tasks are subtree roots; workers pop
// tasks, process the node, and either queue (shallow) or inline-recurse (deep)
// the children. Duplicate nodes are pruned by the shared cache BEFORE being
// queued, so distinct subtrees spread across the worker threads. in_flight
// tracks outstanding tasks so the pool can detect quiescence and shut down.
struct Task { ProcessGraph g; int sync_num; };

struct Pool {
    std::deque<Task> q;
    std::mutex m;
    std::condition_variable cv;
    std::atomic<long> in_flight{0};
    bool done = false;

    void push(Task t) {
        in_flight.fetch_add(1);
        { std::lock_guard<std::mutex> lk(m); q.push_back(std::move(t)); }
        cv.notify_one();
    }

    bool pop(Task& t) {
        std::unique_lock<std::mutex> lk(m);
        cv.wait(lk, [&] { return !q.empty() || done; });
        if (q.empty()) return false;
        t = std::move(q.front());
        q.pop_front();
        return true;
    }

    void finish_one() {
        if (in_flight.fetch_sub(1) == 1) {
            { std::lock_guard<std::mutex> lk(m); done = true; }
            cv.notify_all();
        }
    }
};

// Process one already-cache-admitted node `g` at depth `sync_num`. Children
// (deduped) are queued while shallow, inlined once deep, to bound queue size.
void expand(EnumState& st, Pool& pool, const ProcessGraph& g, int sync_num) {
    if (is_full_synchronized(g)) { handle_full_sync(st, g); return; }
    if (sync_num >= st.max_sync) return;

    int proc_num = g.proc_num;
    for (int p1 = 0; p1 < proc_num; ++p1)
        for (int p2 = p1 + 1; p2 < proc_num; ++p2) {
            ProcessGraph ng = g;
            ng.sync(p1, p2);
            if (!cache_insert(st, ng)) continue;          // prune duplicates here
            if (sync_num < st.parallel_cutoff)
                pool.push({std::move(ng), sync_num + 1});  // parallelizable task
            else
                expand(st, pool, ng, sync_num + 1);        // inline (deep)
        }
}

} // namespace

EnumerateResult enumerate(int n_procs, int max_sync, unsigned threads) {
    if (threads < 1) threads = 1;

    EnumState st;
    st.max_sync = max_sync;
    // Queue children for the shallow levels (where, after symmetry dedup, enough
    // distinct subtrees exist to keep all threads busy); inline deeper levels.
    st.parallel_cutoff = std::min(max_sync, 5);

    Pool pool;

    ProcessGraph root;
    root.init(n_procs);
    cache_insert(st, root);
    pool.push({std::move(root), 0});

    std::vector<std::thread> workers;
    workers.reserve(threads);
    for (unsigned i = 0; i < threads; ++i)
        workers.emplace_back([&st, &pool] {
            Task t;
            while (pool.pop(t)) {
                expand(st, pool, t.g, t.sync_num);
                pool.finish_one();
            }
        });
    for (auto& w : workers) w.join();

    EnumerateResult result;
    result.count = st.count.load();
    result.isomorphic_hits = st.iso_hits.load();
    for (auto& kv : st.buckets)
        for (auto& g : kv.second)
            result.results.push_back(std::move(g));
    return result;
}

} // namespace nomadim
