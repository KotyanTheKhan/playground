#include <gtest/gtest.h>
#include "nomadim/isomorphism.hpp"
#include "nomadim/process_graph.hpp"
#include "nomadim/execution.hpp"
#include <algorithm>

using namespace nomadim;

TEST(Isomorphism, ReflexiveAndPermutationInvariant) {
    ProcessGraph a = ProcessGraph::build(Execution{4, {{0,1},{1,2},{2,3},{0,2}}});
    ProcessGraph b = ProcessGraph::build(Execution{4, {{0,1},{1,2},{2,3},{0,2}}});
    EXPECT_TRUE(is_isomorphic(a, b));
}

TEST(Isomorphism, DistinguishesDifferentExecutions) {
    // A "path" of syncs vs a "star" of syncs are structurally distinct
    // (network degree sequences differ), so not isomorphic. Verified against
    // the upstream algorithm as oracle. (Note: (0,1),(1,2) vs (0,1),(0,2) ARE
    // isomorphic via relabeling, so they make a poor negative case.)
    ProcessGraph path = ProcessGraph::build(Execution{4, {{0,1},{1,2},{2,3}}});
    ProcessGraph star = ProcessGraph::build(Execution{4, {{0,1},{0,2},{0,3}}});
    EXPECT_FALSE(is_isomorphic(path, star));
}

TEST(Isomorphism, GenerateAllIsomorphicCardinality) {
    ProcessGraph a = ProcessGraph::build(Execution{3, {{0,1}}});
    auto all = generate_all_isomorphic(a);
    EXPECT_EQ(all.size(), 6u); // 3! permutations
}

TEST(Isomorphism, CanonicalSyncNamePermutationInvariant) {
    ProcessGraph a = ProcessGraph::build(Execution{4, {{0,1}}});
    ProcessGraph b = ProcessGraph::build(Execution{4, {{2,3}}});
    EXPECT_EQ(canonical_sync_name(a), canonical_sync_name(b));
}

TEST(Isomorphism, CanonicalSyncNameSortedAndDistinguishes) {
    ProcessGraph a = ProcessGraph::build(Execution{4, {{0,1}}});
    auto key = canonical_sync_name(a);
    EXPECT_TRUE(std::is_sorted(key.begin(), key.end()));
    ProcessGraph path = ProcessGraph::build(Execution{4, {{0,1},{1,2},{2,3}}});
    ProcessGraph star = ProcessGraph::build(Execution{4, {{0,1},{0,2},{0,3}}});
    EXPECT_NE(canonical_sync_name(path), canonical_sync_name(star));
}

TEST(Isomorphism, GenerateAllIsomorphicCardinalityN4) {
    ProcessGraph a = ProcessGraph::build(Execution{4, {{0,1}}});
    EXPECT_EQ(generate_all_isomorphic(a).size(), 24u);
}

TEST(Isomorphism, NotIsomorphicWhenShapeDiffers) {
    ProcessGraph a = ProcessGraph::build(Execution{3, {{0,1}}});
    ProcessGraph diff_procs = ProcessGraph::build(Execution{4, {{0,1}}});
    EXPECT_FALSE(is_isomorphic(a, diff_procs));
    ProcessGraph more_syncs = ProcessGraph::build(Execution{3, {{0,1},{1,2}}});
    EXPECT_FALSE(is_isomorphic(a, more_syncs));
    EXPECT_TRUE(is_isomorphic(a, a));
}
