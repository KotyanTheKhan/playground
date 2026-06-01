#ifndef NOMADIM_REALIZER_HPP
#define NOMADIM_REALIZER_HPP

#include "nomadim/types.hpp"
#include <vector>

namespace nomadim {

// A 2-realizer of a poset: two linear extensions whose intersection is exactly
// the partial order. When the poset has order dimension > 2, dim_le_2 is false
// and l1/l2 are empty.
struct Realizer {
    bool dim_le_2 = false;
    std::vector<int> l1;   // permutation of 0..n-1, least element first
    std::vector<int> l2;
};

// Find a 2-realizer of the poset whose order is the reachability closure of the
// adjacency list `g` (edge u->v means u < v). Precondition: `g` is acyclic
// (callers validate with Poset::validate first).
Realizer find_realizer(const adjacency_list& g);

} // namespace nomadim

#endif // NOMADIM_REALIZER_HPP
