#include "cmd_enumerate.hpp"
#include "nomadim/enumerate.hpp"
#include "nomadim/io.hpp"
#include "nomadim/execution.hpp"
#include <iostream>
#include <fstream>

namespace nomadim {

int cmd_enumerate(int n_procs, int max_sync, unsigned threads, const std::string& out_path) {
    EnumerateResult r = enumerate(n_procs, max_sync, threads);
    std::cout << "Processes: " << n_procs << "  max syncs: " << max_sync
              << "  threads: " << threads << "\n";
    std::cout << "Non-isomorphic dim-2 synced executions: " << r.count
              << "  (isomorphic hits: " << r.isomorphic_hits << ")\n";

    if (!out_path.empty()) {
        std::ofstream o(out_path);
        if (!o) { std::cerr << "cannot open " << out_path << "\n"; return 1; }
        for (auto const& g : r.results) {
            Execution e{g.proc_num, g.syncs};
            o << dump_execution(e) << "---\n";
        }
        std::cout << "Wrote " << r.results.size() << " executions to " << out_path << "\n";
    }
    return 0;
}

} // namespace nomadim
