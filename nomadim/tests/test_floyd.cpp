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
