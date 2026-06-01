#include <gtest/gtest.h>
#include "nomadim/dimension.hpp"
#include "nomadim/process_graph.hpp"
#include "nomadim/execution.hpp"
#include "nomadim/types.hpp"

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
