#include <gtest/gtest.h>
#include "nomadim/execution.hpp"
#include <stdexcept>

using nomadim::Execution;

TEST(Execution, ValidConstruction) {
    Execution e{4, {{0,1},{1,2},{2,3},{0,2}}};
    EXPECT_NO_THROW(e.validate());
    EXPECT_EQ(e.n_procs, 4);
    EXPECT_EQ(e.syncs.size(), 4u);
}

TEST(Execution, RejectsNonPositiveProcs) {
    Execution e{0, {}};
    EXPECT_THROW(e.validate(), std::invalid_argument);
}

TEST(Execution, RejectsOutOfRangeProc) {
    Execution e{2, {{0, 5}}};
    EXPECT_THROW(e.validate(), std::invalid_argument);
}

TEST(Execution, RejectsSelfSync) {
    Execution e{3, {{1, 1}}};
    EXPECT_THROW(e.validate(), std::invalid_argument);
}
