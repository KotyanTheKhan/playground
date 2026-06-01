cmake_minimum_required(VERSION 3.16)
project(nomadim LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release)
endif()

option(NOMADIM_SLOW_TESTS "Enable heavy golden-count enumeration tests" OFF)

include(FetchContent)

FetchContent_Declare(yaml-cpp
  GIT_REPOSITORY https://github.com/jbeder/yaml-cpp.git
  GIT_TAG 0.8.0)
set(YAML_CPP_BUILD_TESTS OFF CACHE BOOL "" FORCE)
FetchContent_MakeAvailable(yaml-cpp)

FetchContent_Declare(cli11
  GIT_REPOSITORY https://github.com/CLIUtils/CLI11.git
  GIT_TAG v2.4.2)
FetchContent_MakeAvailable(cli11)

FetchContent_Declare(googletest
  GIT_REPOSITORY https://github.com/google/googletest.git
  GIT_TAG v1.15.2)
set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
FetchContent_MakeAvailable(googletest)

find_package(Boost REQUIRED COMPONENTS fiber context)
find_package(Threads REQUIRED)

# ---- core library ----
add_library(nomadim_core
  src/version.cpp
  src/execution.cpp
  src/process_graph.cpp
  src/floyd.cpp
  src/dimension.cpp
  src/poset.cpp
  src/isomorphism.cpp
  src/enumerate.cpp
)
target_include_directories(nomadim_core PUBLIC include)
target_link_libraries(nomadim_core PUBLIC yaml-cpp Boost::fiber Boost::context Threads::Threads)

# ---- CLI (sources added in later tasks) ----
add_executable(nomadim app/main.cpp)
target_link_libraries(nomadim PRIVATE nomadim_core CLI11::CLI11)

# ---- tests ----
enable_testing()
include(GoogleTest)
add_executable(nomadim_tests tests/test_smoke.cpp tests/test_execution.cpp tests/test_process_graph.cpp tests/test_floyd.cpp tests/test_dimension.cpp tests/test_poset.cpp tests/test_isomorphism.cpp tests/test_enumerate.cpp)
target_link_libraries(nomadim_tests PRIVATE nomadim_core GTest::gtest_main)
if(NOMADIM_SLOW_TESTS)
  target_compile_definitions(nomadim_tests PRIVATE NOMADIM_SLOW_TESTS=1)
endif()
gtest_discover_tests(nomadim_tests)
