#include <gtest/gtest.h>
#include "nomadim/order_relation.hpp"
#include <vector>

using namespace nomadim;

TEST(OrderRelation, AddAndCloseDetectsCycle) {
    StrictRel r(3);
    EXPECT_TRUE(r.add_and_close(0, 1));
    EXPECT_TRUE(r.add_and_close(1, 2));
    EXPECT_TRUE(r.less(0, 2));          // transitivity closed
    EXPECT_FALSE(r.add_and_close(2, 0)); // would create 0<...<0
}

TEST(OrderRelation, BaseOrderFromAdjacency) {
    adjacency_list g = {{1}, {2}, {}};   // 0<1<2
    StrictRel r = base_order(g);
    EXPECT_TRUE(r.less(0, 2));
    EXPECT_FALSE(r.less(2, 0));
}

TEST(OrderRelation, TopoOrderRespectsPartialOrderSmallestFirst) {
    // 0<2, 1<2 ; 0 and 1 incomparable -> smallest-first gives [0,1,2].
    StrictRel r(3);
    r.add_and_close(0, 2);
    r.add_and_close(1, 2);
    std::vector<int> ord = topo_order(r);
    EXPECT_EQ(ord, (std::vector<int>{0, 1, 2}));
}

TEST(OrderRelation, LinearizeTotalOrder) {
    StrictRel r(3);
    r.add_and_close(2, 0);
    r.add_and_close(0, 1);   // total: 2<0<1
    EXPECT_EQ(linearize(r), (std::vector<int>{2, 0, 1}));
}
