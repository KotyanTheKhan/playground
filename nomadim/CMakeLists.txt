cmake_minimum_required(VERSION 3.16)
project(nomadim LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release)
endif()

option(NOMADIM_SLOW_TESTS "Enable heavy golden-count enumeration tests" OFF)
option(NOMADIM_BENCH "Build performance benchmarks (fetches Google Benchmark)" OFF)
option(NOMADIM_WASM "Build the WebAssembly module via Emscripten (no CLI/tests/bench)" OFF)

include(FetchContent)

FetchContent_Declare(yaml-cpp
  GIT_REPOSITORY https://github.com/jbeder/yaml-cpp.git
  GIT_TAG 0.8.0)
set(YAML_CPP_BUILD_TESTS OFF CACHE BOOL "" FORCE)
FetchContent_MakeAvailable(yaml-cpp)

if(NOMADIM_WASM)
  # ---- WebAssembly module (Emscripten) ----
  # Reduced source set: omits enumerate.cpp/isomorphism.cpp (std::thread) and the
  # CLI/tests. Everything the editor bindings need, nothing that needs pthreads.
  add_executable(nomadim_wasm
    src/version.cpp
    src/execution.cpp
    src/process_graph.cpp
    src/floyd.cpp
    src/dimension.cpp
    src/poset.cpp
    src/realizer.cpp
    src/io.cpp
    src/wasm_bindings.cpp
  )
  target_include_directories(nomadim_wasm PRIVATE include)
  target_link_libraries(nomadim_wasm PRIVATE yaml-cpp)
  target_compile_options(nomadim_wasm PRIVATE -fexceptions)
  target_link_options(nomadim_wasm PRIVATE
    -fexceptions
    --bind
    "-sMODULARIZE=1"
    "-sEXPORT_NAME=createNomadim"
    "-sENVIRONMENT=web,worker,node"
    "-sALLOW_MEMORY_GROWTH=1"
  )
  set_target_properties(nomadim_wasm PROPERTIES OUTPUT_NAME nomadim)
else()
  # ---- native build: core library + CLI + tests + benchmarks ----
  FetchContent_Declare(cli11
    GIT_REPOSITORY https://github.com/CLIUtils/CLI11.git
    GIT_TAG v2.4.2)
  FetchContent_MakeAvailable(cli11)

  FetchContent_Declare(googletest
    GIT_REPOSITORY https://github.com/google/googletest.git
    GIT_TAG v1.15.2)
  set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
  FetchContent_MakeAvailable(googletest)

  find_package(Threads REQUIRED)

  add_library(nomadim_core
    src/version.cpp
    src/execution.cpp
    src/process_graph.cpp
    src/floyd.cpp
    src/dimension.cpp
    src/poset.cpp
    src/realizer.cpp
    src/isomorphism.cpp
    src/enumerate.cpp
    src/io.cpp
  )
  target_include_directories(nomadim_core PUBLIC include)
  target_link_libraries(nomadim_core PUBLIC yaml-cpp Threads::Threads)

  add_executable(nomadim app/main.cpp app/cmd_check.cpp app/cmd_enumerate.cpp app/cmd_convert.cpp)
  target_link_libraries(nomadim PRIVATE nomadim_core CLI11::CLI11)

  enable_testing()
  include(GoogleTest)
  add_executable(nomadim_tests tests/test_smoke.cpp tests/test_execution.cpp tests/test_process_graph.cpp tests/test_floyd.cpp tests/test_dimension.cpp tests/test_realizer.cpp tests/test_poset.cpp tests/test_isomorphism.cpp tests/test_enumerate.cpp tests/test_io.cpp tests/test_order_relation.cpp)
  target_link_libraries(nomadim_tests PRIVATE nomadim_core GTest::gtest_main)
  if(NOMADIM_SLOW_TESTS)
    target_compile_definitions(nomadim_tests PRIVATE NOMADIM_SLOW_TESTS=1)
  endif()
  gtest_discover_tests(nomadim_tests)

  add_test(NAME cli_check_dim2
    COMMAND nomadim check ${CMAKE_CURRENT_SOURCE_DIR}/data/exec_dim2.yaml)
  set_tests_properties(cli_check_dim2 PROPERTIES
    PASS_REGULAR_EXPRESSION "Dimension <= 2: YES")

  add_test(NAME cli_check_not_dim2
    COMMAND nomadim check ${CMAKE_CURRENT_SOURCE_DIR}/data/poset_s3.yaml)
  set_tests_properties(cli_check_not_dim2 PROPERTIES
    PASS_REGULAR_EXPRESSION "Dimension <= 2: NO")

  add_test(NAME cli_check_canonical_not_dim2
    COMMAND nomadim check ${CMAKE_CURRENT_SOURCE_DIR}/data/exec_4_canonical.yaml)
  set_tests_properties(cli_check_canonical_not_dim2 PROPERTIES
    PASS_REGULAR_EXPRESSION "Dimension <= 2: NO")

  add_test(NAME cli_enumerate_4_5
    COMMAND nomadim enumerate -n 4 -k 5 -j 1)
  set_tests_properties(cli_enumerate_4_5 PROPERTIES
    PASS_REGULAR_EXPRESSION "Non-isomorphic dim-2 synced executions: 10")

  # ---- benchmarks (opt-in: -DNOMADIM_BENCH=ON) ----
  if(NOMADIM_BENCH)
    FetchContent_Declare(benchmark
      GIT_REPOSITORY https://github.com/google/benchmark.git
      GIT_TAG v1.9.1)
    set(BENCHMARK_ENABLE_TESTING OFF CACHE BOOL "" FORCE)
    set(BENCHMARK_ENABLE_GTEST_TESTS OFF CACHE BOOL "" FORCE)
    FetchContent_MakeAvailable(benchmark)

    add_executable(nomadim_bench bench/bench_nomadim.cpp)
    target_link_libraries(nomadim_bench PRIVATE nomadim_core benchmark::benchmark)
  endif()

  # ---- compare.py regression-gate tests ----
  find_package(Python3 COMPONENTS Interpreter)
  if(Python3_Interpreter_FOUND)
    add_test(NAME compare_py
      COMMAND ${Python3_EXECUTABLE} -m unittest discover
              -s ${CMAKE_CURRENT_SOURCE_DIR}/tests -p "test_compare.py")
  endif()
endif()
