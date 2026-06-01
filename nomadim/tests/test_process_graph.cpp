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

TEST(ProcessGraph, InitStateIsCorrect) {
    ProcessGraph g;
    g.init(2);
    ASSERT_EQ((int)g.graph.size(), 2);
    EXPECT_TRUE(g.graph[0].empty());
    EXPECT_TRUE(g.graph[1].empty());
    EXPECT_EQ(g.labels[0].proc, 0); EXPECT_EQ(g.labels[0].num, 0);
    EXPECT_EQ(g.labels[1].proc, 1); EXPECT_EQ(g.labels[1].num, 0);
    EXPECT_EQ(g.proc_last_vertex, (std::vector<int>{0, 1}));
    EXPECT_EQ(g.proc_verteces[0], (std::vector<int>{0}));
    EXPECT_EQ(g.proc_verteces[1], (std::vector<int>{1}));
    ASSERT_EQ(g.network.size(), 2u);
    EXPECT_TRUE(g.network[0].empty());
    ASSERT_EQ(g.proc_sync_name.size(), 2u);
    EXPECT_EQ(g.proc_sync_name[0], "");
}

TEST(ProcessGraph, SyncBuildsMeetStructure) {
    ProcessGraph g;
    g.init(2);
    g.sync(0, 1);
    ASSERT_EQ((int)g.graph.size(), 5);
    EXPECT_EQ(g.graph[0], (std::vector<int>{2}));
    EXPECT_EQ(g.graph[1], (std::vector<int>{2}));
    EXPECT_EQ(g.graph[2], (std::vector<int>{3, 4}));
    EXPECT_TRUE(g.graph[3].empty());
    EXPECT_TRUE(g.graph[4].empty());
    EXPECT_EQ(g.proc_last_vertex, (std::vector<int>{3, 4}));
    EXPECT_EQ(g.proc_verteces[0], (std::vector<int>{0, 3}));
    EXPECT_EQ(g.proc_verteces[1], (std::vector<int>{1, 4}));
    EXPECT_EQ(g.labels[2].proc, -1); EXPECT_EQ(g.labels[2].num, -1);
    EXPECT_EQ(g.labels[3].proc, 0);  EXPECT_EQ(g.labels[3].num, 1);
    EXPECT_EQ(g.labels[4].proc, 1);  EXPECT_EQ(g.labels[4].num, 1);
    EXPECT_EQ(g.network[0].count(1), 1u);
    EXPECT_EQ(g.network[1].count(0), 1u);
    EXPECT_EQ(g.proc_sync_name[0], "0");
    EXPECT_EQ(g.proc_sync_name[1], "0");
    ASSERT_EQ(g.syncs.size(), 1u);
    EXPECT_EQ(g.syncs[0], (std::make_pair(0, 1)));
}

TEST(ProcessGraph, BuildEqualsManualReplay) {
    Execution e{4, {{0,1},{1,2},{2,3},{0,2}}};
    ProcessGraph built = ProcessGraph::build(e);
    ProcessGraph manual;
    manual.init(4);
    for (auto const& s : e.syncs) manual.sync(s.first, s.second);
    EXPECT_EQ(built.graph, manual.graph);
    EXPECT_EQ(built.syncs, manual.syncs);
    EXPECT_EQ(built.proc_sync_name, manual.proc_sync_name);
}
