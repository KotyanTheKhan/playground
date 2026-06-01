#ifndef NOMADIM_EXECUTION_HPP
#define NOMADIM_EXECUTION_HPP

#include <vector>
#include <utility>

namespace nomadim {

// A distributed execution: n_procs processes plus an ordered list of
// synchronization events, each a pair of distinct process indices.
struct Execution {
    int n_procs = 0;
    std::vector<std::pair<int,int>> syncs;

    // Throws std::invalid_argument if n_procs <= 0, any endpoint is out of
    // [0, n_procs), or any sync pairs a process with itself.
    void validate() const;
};

} // namespace nomadim

#endif // NOMADIM_EXECUTION_HPP
