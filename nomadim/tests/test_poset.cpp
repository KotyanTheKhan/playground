#include <gtest/gtest.h>
#include "nomadim/poset.hpp"
#include "nomadim/process_graph.hpp"
#include "nomadim/execution.hpp"
#include "nomadim/dimension.hpp"
#include <stdexcept>

using namespace nomadim;

TEST(Poset, ValidatesBounds) {
    Poset p{3, {{1,2},{2},{}}};
    EXPECT_NO_THROW(p.validate());
    Poset bad{2, {{0,5}}};
    EXPECT_THROW(bad.validate(), std::invalid_argument);
}

TEST(Poset, RejectsCyclicEdges) {
    Poset cyc{3, {{1},{2},{0}}};
    EXPECT_THROW(cyc.validate(), std::invalid_argument);
}

TEST(Poset, FromProcessGraphMatchesGraph) {
    Execution e{4, {{0,1},{1,2},{2,3},{0,2}}};
    ProcessGraph g = ProcessGraph::build(e);
    Poset p = Poset::from(g);
    EXPECT_EQ(p.n_vertices, (int)g.graph.size());
    EXPECT_EQ(p.edges, g.graph);
}
