#include "cmd_enumerate.hpp"
#include "nomadim/enumerate.hpp"
#include "nomadim/io.hpp"
#include "nomadim/execution.hpp"
#include "nomadim/dimension.hpp"
#include "nomadim/hypergraph.hpp"
#include <iostream>
#include <fstream>
#include <map>
#include <vector>
#include <thread>
#include <atomic>
#include <mutex>

namespace nomadim {

int cmd_enumerate(int n_procs, int max_sync, unsigned threads, const std::string& out_path,
                  bool all_dims, bool with_dim, int max_vertices, int max_cpairs) {
    EnumerateResult r = enumerate(n_procs, max_sync, threads, all_dims);
    std::cout << "Processes: " << n_procs << "  max syncs: " << max_sync
              << "  threads: " << threads << "\n";
    std::cout << "Non-isomorphic " << (all_dims ? "(all-dim)" : "dim-2")
              << " synced executions: " << r.count
              << "  (isomorphic hits: " << r.isomorphic_hits << ")\n";

    // Optionally compute each shape's order dimension (fast path: no coloring
    // enumeration), for a (sync-count, dimension) histogram and per-doc meta.
    // Parallelized across `threads` workers: the per-shape dimension computation
    // dominates at large shape counts.
    std::vector<int> dims;
    if (with_dim) {
        Caps caps; caps.max_vertices = max_vertices; caps.max_critical_pairs = max_cpairs;
        size_t n = r.results.size();
        dims.assign(n, 0);              // 0 = computed; -1 = uncomputable (cap hit)
        std::atomic<size_t> next{0};
        unsigned nw = threads < 1 ? 1 : threads;
        std::vector<std::thread> workers;
        for (unsigned w = 0; w < nw; ++w)
            workers.emplace_back([&] {
                size_t i;
                while ((i = next.fetch_add(1)) < n) {
                    // Exceptions must not escape a worker thread (std::terminate);
                    // a shape that exceeds the caps is marked uncomputable (-1).
                    try { dims[i] = dimension(r.results[i].graph, caps); }
                    catch (const std::exception&) { dims[i] = -1; }
                }
            });
        for (auto& t : workers) t.join();

        std::map<std::pair<int,int>, int> hist;   // (syncs, dim) -> count
        int max_dim = 0; size_t max_idx = 0; long uncomputable = 0;
        for (size_t i = 0; i < n; ++i) {
            if (dims[i] < 0) { uncomputable++; continue; }
            hist[{(int)r.results[i].syncs.size(), dims[i]}]++;
            if (dims[i] > max_dim) { max_dim = dims[i]; max_idx = i; }
        }
        std::cout << "Dimension histogram (syncs, dimension -> count):\n";
        for (auto const& kv : hist)
            std::cout << "  syncs=" << kv.first.first << " dim=" << kv.first.second
                      << " -> " << kv.second << "\n";
        if (uncomputable)
            std::cout << "  uncomputable (caps exceeded): " << uncomputable << "\n";
        std::cout << "Maximum dimension: " << max_dim
                  << (uncomputable ? " (among computable shapes)" : "") << "\n";
        if (max_dim > 0) {
            std::cout << "  example (syncs=" << r.results[max_idx].syncs.size() << "):";
            for (auto const& s : r.results[max_idx].syncs)
                std::cout << " (" << s.first << "," << s.second << ")";
            std::cout << "\n";
        }
    }

    if (!out_path.empty()) {
        std::ofstream o(out_path);
        if (!o) { std::cerr << "cannot open " << out_path << "\n"; return 1; }
        for (size_t i = 0; i < r.results.size(); ++i) {
            auto const& g = r.results[i];
            if (with_dim) {
                Document d;
                d.execution = Execution{g.proc_num, g.syncs};
                Meta m; m.dimension = dims[i];
                d.meta = std::move(m);
                o << dump_document(d) << "---\n";
            } else {
                Execution e{g.proc_num, g.syncs};
                o << dump_execution(e) << "---\n";
            }
        }
        std::cout << "Wrote " << r.results.size() << " executions to " << out_path << "\n";
    }
    return 0;
}

} // namespace nomadim
