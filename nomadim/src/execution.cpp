#include "nomadim/execution.hpp"
#include <stdexcept>
#include <string>

namespace nomadim {

void Execution::validate() const {
    if (n_procs <= 0)
        throw std::invalid_argument("n_procs must be positive, got " + std::to_string(n_procs));
    for (auto const& s : syncs) {
        if (s.first < 0 || s.first >= n_procs || s.second < 0 || s.second >= n_procs)
            throw std::invalid_argument("sync endpoint out of range [0, " + std::to_string(n_procs) + ")");
        if (s.first == s.second)
            throw std::invalid_argument("sync cannot pair a process with itself");
    }
}

} // namespace nomadim
