#include <gtest/gtest.h>
#include "nomadim/enumerate.hpp"
#include <thread>
#include <algorithm>

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
// Heavier golden counts, gated behind -DNOMADIM_SLOW_TESTS=ON. Run with several
// threads. The even larger reference cases (4,9 -> 12784 and 6,9 -> 1036) are
// documented in the design/plan but not run here: their search trees are large
// enough to take minutes, which is impractical for an automated test.
TEST(EnumerateSlow, GoldenCountsSlowTier) {
    unsigned j = std::max(2u, std::thread::hardware_concurrency());
    EXPECT_EQ(enumerate(4, 8, j).count, 3058);
    EXPECT_EQ(enumerate(5, 8, j).count, 704);
}
#endif
