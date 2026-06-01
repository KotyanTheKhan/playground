#include <gtest/gtest.h>
#include "nomadim/io.hpp"
#include <stdexcept>

using namespace nomadim;

TEST(Io, ExecutionRoundTrip) {
    Execution e{4, {{0,1},{1,2},{2,3},{0,2}}};
    std::string text = dump_execution(e);
    Document d = parse_document(text);
    ASSERT_TRUE(d.execution.has_value());
    EXPECT_EQ(d.execution->n_procs, 4);
    EXPECT_EQ(d.execution->syncs, e.syncs);
}

TEST(Io, PosetRoundTrip) {
    Poset p{3, {{1,2},{2},{}}};
    std::string text = dump_poset(p);
    Document d = parse_document(text);
    ASSERT_TRUE(d.poset.has_value());
    EXPECT_EQ(d.poset->n_vertices, 3);
    EXPECT_EQ(d.poset->edges, p.edges);
}

TEST(Io, ParsesBothKeys) {
    Document d = parse_document(
        "execution:\n  n_procs: 2\n  syncs: [[0,1]]\n"
        "poset:\n  n_vertices: 2\n  edges: [[0,1]]\n");
    EXPECT_TRUE(d.execution.has_value());
    EXPECT_TRUE(d.poset.has_value());
}

TEST(Io, RejectsMalformedSyncPair) {
    EXPECT_THROW(parse_document("execution:\n  n_procs: 2\n  syncs: [[0,1,2]]\n"),
                 std::runtime_error);
}

TEST(Io, RejectsMalformedEdgePair) {
    EXPECT_THROW(parse_document("poset:\n  n_vertices: 2\n  edges: [[0]]\n"),
                 std::runtime_error);
}

TEST(Io, RejectsDocumentWithNeitherKey) {
    EXPECT_THROW(parse_document("foo: 1\n"), std::runtime_error);
}
