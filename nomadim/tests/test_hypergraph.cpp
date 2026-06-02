#include <gtest/gtest.h>
#include "nomadim/hypergraph.hpp"
#include "nomadim/dimension.hpp"
#include "nomadim/floyd.hpp"
#include "nomadim/order_relation.hpp"
#include <vector>

using namespace nomadim;

namespace {
std::vector<critical_pair> cps_of(const adjacency_list& g) {
    std::vector<int> m = make_graph_matrix(g);
    return find_critical_pairs(m.data(), (int)g.size());
}
} // namespace

TEST(Hypergraph, SingletonAlwaysReversible) {
    adjacency_list a3(3);                 // 3-antichain
    auto cps = cps_of(a3);
    StrictRel base = base_order(a3);
    ASSERT_FALSE(cps.empty());
    EXPECT_TRUE(is_reversible(base, cps, {0}));
}

TEST(Hypergraph, OppositePairIsNotReversible) {
    // In a 3-antichain (a,b) and (b,a) are both critical and conflict.
    adjacency_list a3(3);
    auto cps = cps_of(a3);
    StrictRel base = base_order(a3);
    // Find indices of a mutually-reversed pair (x,y) and (y,x).
    int i = -1, j = -1;
    for (size_t p = 0; p < cps.size() && i < 0; ++p)
        for (size_t q = 0; q < cps.size(); ++q)
            if (cps[p].x == cps[q].y && cps[p].y == cps[q].x) { i = (int)p; j = (int)q; break; }
    ASSERT_GE(i, 0);
    EXPECT_TRUE(is_reversible(base, cps, {i}));
    EXPECT_FALSE(is_reversible(base, cps, {i, j}));
}
