#include <gtest/gtest.h>
#include "nomadim/oracle.hpp"
#include "nomadim/dimension.hpp"
#include <vector>

using namespace nomadim;

TEST(Oracle, MatchesAnalyzeOnAllSmallDags) {
    for (int n = 1; n <= 4; ++n) {
        std::vector<std::pair<int,int>> slots;
        for (int i = 0; i < n; ++i)
            for (int j = 0; j < n; ++j)
                if (i != j) slots.push_back({i, j});
        int E = (int)slots.size();
        for (long mask = 0; mask < (1L << E); ++mask) {
            adjacency_list g(n);
            for (int b = 0; b < E; ++b)
                if (mask & (1L << b)) g[slots[b].first].push_back(slots[b].second);
            if (have_cycle(g)) continue;
            int oracle = oracle_dimension(g);
            int got = analyze_dimension(g, Caps{}).dimension;
            ASSERT_EQ(got, oracle) << "n=" << n << " mask=" << mask;
        }
    }
}

TEST(Oracle, S3DimensionIsThree) {
    adjacency_list s3(6); s3[0] = {4,5}; s3[1] = {3,5}; s3[2] = {3,4};
    EXPECT_EQ(oracle_dimension(s3), 3);
}
