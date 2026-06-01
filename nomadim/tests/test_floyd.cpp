#include <gtest/gtest.h>
#include "nomadim/floyd.hpp"
#include "nomadim/types.hpp"
#include <vector>

using namespace nomadim;

TEST(Floyd, ComputesReachabilityDistances) {
    // chain 0 -> 1 -> 2
    adjacency_list g = {{1}, {2}, {}};
    std::vector<int> m = make_graph_matrix(g);
    floyd(m.data(), 3);
    EXPECT_EQ(m[0*3 + 2], 2);   // 0 reaches 2 in 2 steps
    EXPECT_EQ(m[2*3 + 0], INF); // 2 does not reach 0
    EXPECT_EQ(m[1*3 + 1], 0);
}

TEST(Floyd, MakeGraphMatrixLayout) {
    adjacency_list g = {{1}, {2}, {}};
    std::vector<int> m = make_graph_matrix(g);
    ASSERT_EQ(m.size(), 9u);
    EXPECT_EQ(m[0*3 + 0], 0);
    EXPECT_EQ(m[1*3 + 1], 0);
    EXPECT_EQ(m[0*3 + 1], 1);
    EXPECT_EQ(m[1*3 + 2], 1);
    EXPECT_EQ(m[0*3 + 2], INF);
    EXPECT_EQ(m[1*3 + 0], INF);
}

TEST(Floyd, DisconnectedStaysInf) {
    adjacency_list g = {{1}, {0}, {3}, {2}};
    std::vector<int> m = make_graph_matrix(g);
    floyd(m.data(), 4);
    EXPECT_EQ(m[0*4 + 1], 1);
    EXPECT_EQ(m[0*4 + 2], INF);
    EXPECT_EQ(m[2*4 + 0], INF);
}

TEST(Floyd, DiamondTakesShortestPath) {
    adjacency_list g = {{1, 2}, {3}, {3}, {}};
    std::vector<int> m = make_graph_matrix(g);
    floyd(m.data(), 4);
    EXPECT_EQ(m[0*4 + 3], 2);
    EXPECT_EQ(m[3*4 + 0], INF);
}

TEST(Floyd, SingleVertex) {
    adjacency_list g = {{}};
    std::vector<int> m = make_graph_matrix(g);
    floyd(m.data(), 1);
    EXPECT_EQ(m[0], 0);
}

TEST(Floyd, AdvanceVertexRelaxesOnlyThroughThatVertex) {
    adjacency_list g = {{1}, {2}, {}};
    std::vector<int> m = make_graph_matrix(g);
    EXPECT_EQ(m[0*3 + 2], INF);
    floyd_advance_vertex(m.data(), 3, 1);
    EXPECT_EQ(m[0*3 + 2], 2);
    adjacency_list g2 = {{1}, {2}, {3}, {}};
    std::vector<int> m2 = make_graph_matrix(g2);
    floyd_advance_vertex(m2.data(), 4, 1);
    EXPECT_EQ(m2[0*4 + 2], 2);
    EXPECT_EQ(m2[0*4 + 3], INF);
}
