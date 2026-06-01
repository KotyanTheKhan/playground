#include <gtest/gtest.h>
#include "nomadim/types.hpp"
#include <string>

TEST(Smoke, VersionIsNonEmpty) {
    EXPECT_FALSE(std::string(nomadim::version()).empty());
}
