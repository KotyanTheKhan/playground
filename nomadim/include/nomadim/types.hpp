#ifndef NOMADIM_TYPES_HPP
#define NOMADIM_TYPES_HPP

#include <vector>
#include <utility>
#include <limits>

namespace nomadim {

using adjacency_list = std::vector<std::vector<int>>;

// Floyd "infinity": large enough that 2*INF does not overflow int.
inline constexpr int INF = std::numeric_limits<int>::max() / 3;

struct critical_pair {
    int x;
    int y;
};

// Returns the library version string. Defined in src/version.cpp.
const char* version();

} // namespace nomadim

#endif // NOMADIM_TYPES_HPP
