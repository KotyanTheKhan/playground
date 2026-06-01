#include <gtest/gtest.h>
#include "nomadim/dimension.hpp"
#include "nomadim/process_graph.hpp"
#include "nomadim/execution.hpp"
#include "nomadim/types.hpp"
#include "nomadim/floyd.hpp"

using namespace nomadim;

TEST(Dimension, HelpersDetectCycleAndBipartite) {
    adjacency_list cyc = {{1}, {2}, {0}};
    EXPECT_TRUE(have_cycle(cyc));
    adjacency_list dag = {{1}, {2}, {}};
    EXPECT_FALSE(have_cycle(dag));

    adjacency_list even = {{1}, {0, 2}, {1}}; // path: bipartite
    EXPECT_TRUE(is_bipartite(even));
    adjacency_list tri = {{1, 2}, {0, 2}, {0, 1}}; // triangle: not bipartite
    EXPECT_FALSE(is_bipartite(tri));
}

// A total order (chain) has dimension 1 and thus <= 2: no incomparable pairs,
// hence no critical pairs and an empty (bipartite) incompatibility graph.
TEST(Dimension, ChainIsDim2) {
    adjacency_list chain = {{1}, {2}, {3}, {}};
    EXPECT_TRUE(is_dim2(chain));
}

// A single synchronization between two processes expands to a 2-dimensional
// poset (verified against the upstream algorithm: 4 critical pairs, bipartite).
TEST(Dimension, SingleSyncExecutionIsDim2) {
    Execution e{2, {{0, 1}}};
    ProcessGraph g = ProcessGraph::build(e);
    EXPECT_TRUE(is_dim2(g.graph));
}

// Matches upstream `check_poset`: this hardcoded execution expands to a poset
// that is NOT 2-dimensional (25 critical pairs; incompatibility graph not
// bipartite).
TEST(Dimension, CanonicalExecutionIsNotDim2) {
    Execution e{4, {{0,1},{1,2},{2,3},{0,2}}};
    ProcessGraph g = ProcessGraph::build(e);
    EXPECT_FALSE(is_dim2(g.graph));
}

// The standard example S_3 has order dimension 3, hence not <= 2.
// Minimals 0,1,2 ; maximals 3,4,5 ; a_i < b_j for i != j.
TEST(Dimension, StandardExampleS3IsNotDim2) {
    adjacency_list s3(6);
    s3[0] = {4, 5};
    s3[1] = {3, 5};
    s3[2] = {3, 4};
    EXPECT_FALSE(is_dim2(s3));
}

TEST(Dimension, HaveCycleEdgeCases) {
    EXPECT_FALSE(have_cycle(adjacency_list{}));
    EXPECT_FALSE(have_cycle(adjacency_list{{}}));
    EXPECT_TRUE(have_cycle(adjacency_list{{0}}));
    EXPECT_TRUE(have_cycle(adjacency_list{{1},{0}}));
    EXPECT_FALSE(have_cycle(adjacency_list{{1},{2},{}}));
}

TEST(Dimension, IsBipartiteEdgeCases) {
    EXPECT_TRUE(is_bipartite(adjacency_list{}));
    EXPECT_TRUE(is_bipartite(adjacency_list{{}}));
    EXPECT_TRUE(is_bipartite(adjacency_list{{1,3},{0,2},{1,3},{0,2}}));
    EXPECT_FALSE(is_bipartite(adjacency_list{{1,2},{0,2},{0,1}}));
}

TEST(Dimension, CheckIfCriticalOnSmallPoset) {
    adjacency_list g = {{}, {2}, {}};
    std::vector<int> m = make_graph_matrix(g);
    floyd(m.data(), 3);
    EXPECT_FALSE(check_if_critical(m.data(), 3, 0, 1));
    EXPECT_TRUE(check_if_critical(m.data(), 3, 1, 0));
}

TEST(Dimension, FindCriticalPairsCounts) {
    {
        ProcessGraph g = ProcessGraph::build(Execution{4, {{0,1},{1,2},{2,3},{0,2}}});
        std::vector<int> m = make_graph_matrix(g.graph);
        EXPECT_EQ(find_critical_pairs(m.data(), (int)g.graph.size()).size(), 25u);
    }
    {
        adjacency_list s3(6); s3[0] = {4,5}; s3[1] = {3,5}; s3[2] = {3,4};
        std::vector<int> m = make_graph_matrix(s3);
        EXPECT_EQ(find_critical_pairs(m.data(), 6).size(), 3u);
    }
    {
        adjacency_list chain = {{1},{2},{3},{}};
        std::vector<int> m = make_graph_matrix(chain);
        EXPECT_EQ(find_critical_pairs(m.data(), 4).size(), 0u);
    }
    {
        adjacency_list a3(3);
        std::vector<int> m = make_graph_matrix(a3);
        EXPECT_EQ(find_critical_pairs(m.data(), 3).size(), 6u);
    }
}

TEST(Dimension, CheckCriticalPairsGraphBipartiteness) {
    adjacency_list a3(3);
    std::vector<int> m = make_graph_matrix(a3);
    auto cps = find_critical_pairs(m.data(), 3);
    EXPECT_TRUE(check_critical_pairs_graph(a3, cps));
    adjacency_list s3(6); s3[0] = {4,5}; s3[1] = {3,5}; s3[2] = {3,4};
    std::vector<int> ms = make_graph_matrix(s3);
    auto cps3 = find_critical_pairs(ms.data(), 6);
    EXPECT_FALSE(check_critical_pairs_graph(s3, cps3));
}
