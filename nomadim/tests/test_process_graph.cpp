#include <gtest/gtest.h>
#include "nomadim/process_graph.hpp"
#include "nomadim/execution.hpp"

using nomadim::ProcessGraph;
using nomadim::Execution;

TEST(ProcessGraph, EmptyInitHasOneVertexPerProcess) {
    ProcessGraph g;
    g.init(4);
    EXPECT_EQ(g.proc_num, 4);
    EXPECT_EQ((int)g.graph.size(), 4);          // one initial vertex per process
    EXPECT_EQ(g.proc_last_vertex.size(), 4u);
}

TEST(ProcessGraph, SyncAddsThreeVertices) {
    ProcessGraph g;
    g.init(2);                                   // 2 vertices
    g.sync(0, 1);                                // +3 vertices (meet + 2 successors)
    EXPECT_EQ((int)g.graph.size(), 5);
    EXPECT_EQ(g.syncs.size(), 1u);
}

TEST(ProcessGraph, BuildsFromExecution) {
    Execution e{4, {{0,1},{1,2},{2,3},{0,2}}};
    ProcessGraph g = ProcessGraph::build(e);
    EXPECT_EQ(g.proc_num, 4);
    EXPECT_EQ(g.syncs.size(), 4u);
    // 4 initial + 3 per sync * 4 syncs = 16
    EXPECT_EQ((int)g.graph.size(), 16);
}
