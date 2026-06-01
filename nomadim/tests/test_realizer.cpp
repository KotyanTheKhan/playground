#include <gtest/gtest.h>
#include "nomadim/realizer.hpp"
#include "nomadim/dimension.hpp"
#include "nomadim/process_graph.hpp"
#include "nomadim/execution.hpp"
#include "nomadim/types.hpp"
#include <vector>

using namespace nomadim;

namespace {

// Strict reachability of g: base[a*n+b] == 1 iff a < b in the partial order.
std::vector<char> reach(const adjacency_list& g) {
    int n = (int)g.size();
    std::vector<char> r((size_t)n * n, 0);
    for (int u = 0; u < n; ++u)
        for (int v : g[u]) r[(size_t)u * n + v] = 1;
    for (int k = 0; k < n; ++k)
        for (int i = 0; i < n; ++i)
            for (int j = 0; j < n; ++j)
                if (r[(size_t)i * n + k] && r[(size_t)k * n + j])
                    r[(size_t)i * n + j] = 1;
    return r;
}

// pos[e] = index of element e in the linear order `order`.
std::vector<int> positions(const std::vector<int>& order) {
    std::vector<int> pos(order.size());
    for (int i = 0; i < (int)order.size(); ++i) pos[order[i]] = i;
    return pos;
}

// Assert r is a valid 2-realizer of g: l1/l2 are permutations, both are linear
// extensions of the partial order, and their intersection is exactly the order.
void expect_valid_realizer(const adjacency_list& g, const Realizer& r) {
    int n = (int)g.size();
    ASSERT_EQ((int)r.l1.size(), n);
    ASSERT_EQ((int)r.l2.size(), n);
    std::vector<char> seen1(n, 0), seen2(n, 0);
    for (int x : r.l1) { ASSERT_GE(x, 0); ASSERT_LT(x, n); ASSERT_FALSE(seen1[x]); seen1[x] = 1; }
    for (int x : r.l2) { ASSERT_GE(x, 0); ASSERT_LT(x, n); ASSERT_FALSE(seen2[x]); seen2[x] = 1; }
    auto base = reach(g);
    auto p1 = positions(r.l1), p2 = positions(r.l2);
    for (int a = 0; a < n; ++a)
        for (int b = 0; b < n; ++b) {
            if (a == b) continue;
            if (base[(size_t)a * n + b]) {
                EXPECT_LT(p1[a], p1[b]);   // both orders extend the partial order
                EXPECT_LT(p2[a], p2[b]);
            }
            bool in_both = (p1[a] < p1[b]) && (p2[a] < p2[b]);
            EXPECT_EQ(in_both, (bool)base[(size_t)a * n + b]);  // intersection == order
        }
}

} // namespace

// A 4-chain has dimension 1, so it has a 2-realizer (both extensions = 0<1<2<3).
TEST(Realizer, ChainHasRealizer) {
    adjacency_list chain = {{1}, {2}, {3}, {}};
    Realizer r = find_realizer(chain);
    EXPECT_TRUE(r.dim_le_2);
    expect_valid_realizer(chain, r);
}

// A 3-element antichain has dimension 2: one valid realizer is any order and its
// reverse, so the intersection is empty (all pairs incomparable).
TEST(Realizer, AntichainHasRealizer) {
    adjacency_list a3(3);   // no edges
    Realizer r = find_realizer(a3);
    EXPECT_TRUE(r.dim_le_2);
    expect_valid_realizer(a3, r);
}

// Degenerate sizes: the empty poset and a single element both trivially realize.
TEST(Realizer, EmptyAndSingleton) {
    Realizer r0 = find_realizer(adjacency_list{});
    EXPECT_TRUE(r0.dim_le_2);
    EXPECT_TRUE(r0.l1.empty());
    EXPECT_TRUE(r0.l2.empty());

    adjacency_list one(1);
    Realizer r1 = find_realizer(one);
    EXPECT_TRUE(r1.dim_le_2);
    expect_valid_realizer(one, r1);
}

// The standard example S_3 has order dimension 3 — no 2-realizer exists.
TEST(Realizer, StandardExampleS3HasNoRealizer) {
    adjacency_list s3(6);
    s3[0] = {4, 5}; s3[1] = {3, 5}; s3[2] = {3, 4};
    Realizer r = find_realizer(s3);
    EXPECT_FALSE(r.dim_le_2);
    EXPECT_TRUE(r.l1.empty());
    EXPECT_TRUE(r.l2.empty());
    EXPECT_EQ(r.dim_le_2, is_dim2(s3));   // agrees with the existing checker
}

// The canonical 4-process execution is NOT 2-dimensional (25 critical pairs).
TEST(Realizer, CanonicalExecutionHasNoRealizer) {
    ProcessGraph g = ProcessGraph::build(Execution{4, {{0,1},{1,2},{2,3},{0,2}}});
    Realizer r = find_realizer(g.graph);
    EXPECT_FALSE(r.dim_le_2);
    EXPECT_TRUE(r.l1.empty());
    EXPECT_TRUE(r.l2.empty());
    EXPECT_EQ(r.dim_le_2, is_dim2(g.graph));
}

// A single synchronization between two processes expands to a 2-dimensional poset.
TEST(Realizer, SingleSyncExecutionHasRealizer) {
    ProcessGraph g = ProcessGraph::build(Execution{2, {{0,1}}});
    Realizer r = find_realizer(g.graph);
    EXPECT_TRUE(r.dim_le_2);
    EXPECT_EQ(r.dim_le_2, is_dim2(g.graph));
    expect_valid_realizer(g.graph, r);
}

// The "N" poset (0<2, 1<2, 1<3) has dimension 2.
TEST(Realizer, NPosetHasRealizer) {
    adjacency_list n_poset = {{2}, {2, 3}, {}, {}};
    Realizer r = find_realizer(n_poset);
    EXPECT_TRUE(r.dim_le_2);
    EXPECT_EQ(r.dim_le_2, is_dim2(n_poset));
    expect_valid_realizer(n_poset, r);
}
