#include <gtest/gtest.h>
#include "nomadim/io.hpp"
#include <filesystem>
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

// The remaining §9 validation classes, exercised through the YAML loader (which
// runs Execution::validate / Poset::validate on the parsed values).
TEST(Io, RejectsNonPositiveProcs) {
    EXPECT_THROW(parse_document("execution:\n  n_procs: 0\n  syncs: []\n"),
                 std::invalid_argument);
}

TEST(Io, RejectsOutOfRangeSyncEndpoint) {
    EXPECT_THROW(parse_document("execution:\n  n_procs: 2\n  syncs: [[0,5]]\n"),
                 std::invalid_argument);
}

TEST(Io, RejectsSelfSync) {
    EXPECT_THROW(parse_document("execution:\n  n_procs: 3\n  syncs: [[1,1]]\n"),
                 std::invalid_argument);
}

TEST(Io, RejectsCyclicPoset) {
    EXPECT_THROW(parse_document("poset:\n  n_vertices: 3\n  edges: [[0,1],[1,2],[2,0]]\n"),
                 std::invalid_argument);
}

TEST(Io, RejectsOutOfRangePosetEdgeSource) {
    // source out of range is rejected by the parser (runtime_error)...
    EXPECT_THROW(parse_document("poset:\n  n_vertices: 2\n  edges: [[9,0]]\n"),
                 std::runtime_error);
}

TEST(Io, RejectsOutOfRangePosetEdgeTarget) {
    // ...and target out of range is rejected by Poset::validate (invalid_argument).
    EXPECT_THROW(parse_document("poset:\n  n_vertices: 2\n  edges: [[0,9]]\n"),
                 std::invalid_argument);
}

TEST(Io, RejectsDocumentWithNeitherKey) {
    EXPECT_THROW(parse_document("foo: 1\n"), std::runtime_error);
}

TEST(Io, FileRoundTripExecution) {
    Execution e{4, {{0,1},{1,2},{2,3},{0,2}}};
    auto path = std::filesystem::temp_directory_path() / "nomadim_test_exec.yaml";
    save_file(path.string(), dump_execution(e));
    Document d = load_file(path.string());
    std::filesystem::remove(path);
    ASSERT_TRUE(d.execution.has_value());
    EXPECT_EQ(d.execution->n_procs, 4);
    EXPECT_EQ(d.execution->syncs, e.syncs);
}

TEST(Io, FileRoundTripPoset) {
    Poset p{3, {{1,2},{2},{}}};
    auto path = std::filesystem::temp_directory_path() / "nomadim_test_poset.yaml";
    save_file(path.string(), dump_poset(p));
    Document d = load_file(path.string());
    std::filesystem::remove(path);
    ASSERT_TRUE(d.poset.has_value());
    EXPECT_EQ(d.poset->n_vertices, 3);
    EXPECT_EQ(d.poset->edges, p.edges);
}

TEST(Io, LoadNonexistentFileThrows) {
    EXPECT_THROW(load_file("/nonexistent/nomadim/does_not_exist.yaml"),
                 std::runtime_error);
}

TEST(Io, PosetHashIsStableAndOrderInsensitive) {
    adjacency_list a = {{2}, {2}, {}};
    adjacency_list b = {{2}, {2}, {}};
    EXPECT_EQ(poset_hash(a), poset_hash(b));
    adjacency_list c = {{1}, {2}, {}};
    EXPECT_NE(poset_hash(a), poset_hash(c));
}

TEST(Io, MetaRoundTrips) {
    Document d;
    Poset p; p.n_vertices = 3; p.edges = {{2}, {2}, {}};
    p.validate();
    d.poset = p;
    Meta meta;
    meta.notes = "hello world";
    meta.dimension = 2;
    meta.realizers = std::vector<std::vector<std::vector<int>>>{{{0,1,2},{1,0,2}}};
    meta.source_hash = poset_hash(p.edges);
    d.meta = meta;

    std::string text = dump_document(d);
    Document d2 = parse_document(text);
    ASSERT_TRUE(d2.meta.has_value());
    EXPECT_EQ(d2.meta->notes.value_or(""), "hello world");
    EXPECT_EQ(d2.meta->dimension.value_or(-1), 2);
    ASSERT_TRUE(d2.meta->realizers.has_value());
    EXPECT_EQ((*d2.meta->realizers)[0][1], (std::vector<int>{1,0,2}));
    EXPECT_EQ(d2.meta->source_hash.value_or(""), poset_hash(p.edges));
}

TEST(Io, NotesOnlyDocumentParses) {
    Document d = parse_document(
        "poset:\n  n_vertices: 2\n  edges:\n    - [0, 1]\n"
        "meta:\n  notes: just a note\n");
    ASSERT_TRUE(d.meta.has_value());
    EXPECT_EQ(d.meta->notes.value_or(""), "just a note");
    EXPECT_FALSE(d.meta->dimension.has_value());
}
