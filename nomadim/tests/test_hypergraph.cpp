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

TEST(Hypergraph, AntichainHyperedges) {
    // 3-antichain (6 critical pairs): the minimal non-reversible sets are the
    // 3 mutually-reversed {(a,b),(b,a)} pairs (size 2) plus the 2 directed
    // 3-cycles e.g. {(0,1),(1,2),(2,0)} (size 3) = 5 edges total.
    adjacency_list a3(3);
    auto cps = cps_of(a3);
    StrictRel base = base_order(a3);
    auto edges = enumerate_hyperedges(base, cps, Caps{});
    EXPECT_EQ(edges.size(), 5u);
    int size2 = 0, size3 = 0;
    for (const auto& e : edges) {
        EXPECT_GE(e.size(), 2u);
        if (e.size() == 2) ++size2; else if (e.size() == 3) ++size3;
        // every edge is genuinely non-reversible
        EXPECT_FALSE(is_reversible(base, cps, e));
    }
    EXPECT_EQ(size2, 3);
    EXPECT_EQ(size3, 2);
}

TEST(Hypergraph, StandardExampleS3HasThreePairwiseHyperedges) {
    // S_3 has 3 critical pairs that pairwise conflict (reversing any two closes
    // a cycle through the base order) -> three size-2 hyperedges (a triangle).
    adjacency_list s3(6); s3[0] = {4,5}; s3[1] = {3,5}; s3[2] = {3,4};
    auto cps = cps_of(s3);
    ASSERT_EQ(cps.size(), 3u);
    StrictRel base = base_order(s3);
    auto edges = enumerate_hyperedges(base, cps, Caps{});
    ASSERT_EQ(edges.size(), 3u);
    for (const auto& e : edges) EXPECT_EQ(e.size(), 2u);
}
