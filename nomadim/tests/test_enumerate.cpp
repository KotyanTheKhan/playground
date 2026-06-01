#include <gtest/gtest.h>
#include "nomadim/enumerate.hpp"

using namespace nomadim;

// Default tier: cheap golden counts (run on every invocation).
TEST(Enumerate, GoldenCountsDefaultTier) {
    EXPECT_EQ(enumerate(2, 8, 1).count, 1);
    EXPECT_EQ(enumerate(3, 3, 1).count, 2);
    EXPECT_EQ(enumerate(3, 4, 1).count, 6);
    EXPECT_EQ(enumerate(3, 5, 1).count, 12);
    EXPECT_EQ(enumerate(3, 6, 1).count, 20);
    EXPECT_EQ(enumerate(4, 5, 1).count, 10);
    EXPECT_EQ(enumerate(4, 6, 1).count, 102);
    EXPECT_EQ(enumerate(4, 7, 1).count, 634);
    EXPECT_EQ(enumerate(5, 7, 1).count, 40);
}

TEST(Enumerate, ThreadCountDoesNotChangeResult) {
    EXPECT_EQ(enumerate(4, 5, 1).count, enumerate(4, 5, 4).count);
}

#ifdef NOMADIM_SLOW_TESTS
TEST(EnumerateSlow, GoldenCountsSlowTier) {
    EXPECT_EQ(enumerate(4, 8, 4).count, 3058);
    EXPECT_EQ(enumerate(4, 9, 4).count, 12784);
    EXPECT_EQ(enumerate(5, 8, 4).count, 704);
    EXPECT_EQ(enumerate(6, 9, 4).count, 1036);
}
#endif
