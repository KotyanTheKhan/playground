#ifndef NOMADIM_ORACLE_HPP
#define NOMADIM_ORACLE_HPP

// Test-only brute-force dimension oracle. Enumerates linear extensions of the
// poset and finds the smallest set whose intersection is exactly the order.
// Exponential; intended only for validating analyze_dimension on small posets.
// NOT linked into the library, CLI, or WASM.
#include "nomadim/types.hpp"

namespace nomadim {

int oracle_dimension(const adjacency_list& g);

} // namespace nomadim

#endif // NOMADIM_ORACLE_HPP
