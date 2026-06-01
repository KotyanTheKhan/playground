# NomaDimension C++ Port Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Port the NomaDimension poset-dimension tooling into a new top-level `nomadim/` C++ project: a reusable `libnomadim` core plus a single `nomadim` CLI that reads/writes posets as YAML, checks whether a poset has dimension ≤ 2, and enumerates non-isomorphic dimension-2 executions parametrized by *N* processes.

**Architecture:** A focused static library of single-responsibility modules (execution model → event-structure DAG → Floyd transitive closure → critical-pair / bipartite dimension test → isomorphism → multithreaded+multifibered enumerator → YAML I/O), driven by a CLI11-based multi-command binary. Each algorithm is a faithful port of the upstream C++, cleaned into a `nomadim` namespace with headers under `include/nomadim/`. Tests use GoogleTest with golden regression counts from the original.

**Tech Stack:** C++17, CMake (≥3.16) with FetchContent (yaml-cpp, GoogleTest, CLI11) and `find_package(Boost REQUIRED COMPONENTS fiber context)`, Apple clang / GCC, CTest.

---

## Prerequisites (one-time, on the build machine)

This project is built with CMake, entirely separate from the repository's Coq/dune
build (the `.claude/scripts/timed-build.sh` wrapper does **not** apply here).

Boost's `fiber` and `context` libraries are **compiled** (not header-only) and
must be installed before the first build:

```bash
brew install boost cmake        # macOS
# or: sudo apt-get install libboost-fiber-dev libboost-context-dev cmake  # Debian/Ubuntu
```

yaml-cpp, GoogleTest, and CLI11 are fetched automatically by CMake; no manual
install needed.

---

## File Structure

```
nomadim/
  CMakeLists.txt                     # build: libnomadim, nomadim CLI, tests; FetchContent + Boost
  README.md                          # how to build/run/test
  .gitignore                         # build/ dir
  include/nomadim/
    types.hpp                        # shared aliases: adjacency_list, critical_pair, INF
    execution.hpp                    # Execution struct + validation
    process_graph.hpp                # ProcessGraph (event-structure DAG builder)
    floyd.hpp                        # transitive closure
    dimension.hpp                    # critical pairs + bipartite dim-2 test
    poset.hpp                        # general Poset + Poset::from(ProcessGraph)
    isomorphism.hpp                  # is_isomorphic, generate_all_isomorphic
    enumerate.hpp                    # EnumerateResult, enumerate(N,K,threads)
    io.hpp                           # YAML load/save (execution + poset documents)
  src/
    execution.cpp
    process_graph.cpp
    floyd.cpp
    dimension.cpp
    poset.cpp
    isomorphism.cpp
    enumerate.cpp
    io.cpp
  app/
    main.cpp                         # CLI11 wiring -> subcommands
    cmd_check.cpp / cmd_check.hpp
    cmd_enumerate.cpp / cmd_enumerate.hpp
    cmd_convert.cpp / cmd_convert.hpp
  tests/
    test_floyd.cpp
    test_dimension.cpp
    test_isomorphism.cpp
    test_io.cpp
    test_enumerate.cpp
  data/
    exec_4_canonical.yaml            # 0-1,1-2,2-3,0-2 (dim 2)
    poset_s3.yaml                    # standard example S_3 (dimension 3, NOT dim 2)
```

**Responsibility boundaries:** `types` holds only shared aliases; `process_graph`
knows nothing about dimension; `dimension` operates on a plain `adjacency_list`
(so it works for both executions and general posets); `io` is the only module that
touches YAML; `enumerate` is the only module that touches Boost. The CLI layer
(`app/`) contains no algorithm logic — it only parses args, calls the library, and
formats output.

---

## Task 0: Project skeleton, CMake, first green build

**Files:**
- Create: `nomadim/.gitignore`
- Create: `nomadim/CMakeLists.txt`
- Create: `nomadim/include/nomadim/types.hpp`
- Create: `nomadim/src/version.cpp`
- Create: `nomadim/tests/test_smoke.cpp`

- [ ] **Step 1: Create `.gitignore`**

```
build/
```

- [ ] **Step 2: Create shared types header** — `nomadim/include/nomadim/types.hpp`

```cpp
#ifndef NOMADIM_TYPES_HPP
#define NOMADIM_TYPES_HPP

#include <vector>
#include <utility>
#include <limits>

namespace nomadim {

using adjacency_list = std::vector<std::vector<int>>;

// Floyd "infinity": large enough that 2*INF does not overflow int.
inline constexpr int INF = std::numeric_limits<int>::max() / 3;

struct critical_pair {
    int x;
    int y;
};

// Returns the library version string. Defined in src/version.cpp.
const char* version();

} // namespace nomadim

#endif // NOMADIM_TYPES_HPP
```

- [ ] **Step 3: Create `nomadim/src/version.cpp`**

```cpp
#include "nomadim/types.hpp"

namespace nomadim {
const char* version() { return "0.1.0"; }
} // namespace nomadim
```

- [ ] **Step 4: Create `nomadim/CMakeLists.txt`**

```cmake
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
)
target_include_directories(nomadim_core PUBLIC include)
target_link_libraries(nomadim_core PUBLIC yaml-cpp Boost::fiber Boost::context Threads::Threads)

# ---- CLI (sources added in later tasks) ----
add_executable(nomadim app/main.cpp)
target_link_libraries(nomadim PRIVATE nomadim_core CLI11::CLI11)

# ---- tests ----
enable_testing()
include(GoogleTest)
add_executable(nomadim_tests tests/test_smoke.cpp)
target_link_libraries(nomadim_tests PRIVATE nomadim_core GTest::gtest_main)
if(NOMADIM_SLOW_TESTS)
  target_compile_definitions(nomadim_tests PRIVATE NOMADIM_SLOW_TESTS=1)
endif()
gtest_discover_tests(nomadim_tests)
```

Note: `app/main.cpp` is created in this task as a stub so the `nomadim` target
links; later tasks replace its body.

- [ ] **Step 5: Create stub `nomadim/app/main.cpp`**

```cpp
#include "nomadim/types.hpp"
#include <cstdio>

int main() {
    std::printf("nomadim %s\n", nomadim::version());
    return 0;
}
```

- [ ] **Step 6: Write the smoke test** — `nomadim/tests/test_smoke.cpp`

```cpp
#include <gtest/gtest.h>
#include "nomadim/types.hpp"
#include <string>

TEST(Smoke, VersionIsNonEmpty) {
    EXPECT_FALSE(std::string(nomadim::version()).empty());
}
```

- [ ] **Step 7: Configure and build**

Run:
```bash
cmake -S nomadim -B nomadim/build -DCMAKE_BUILD_TYPE=Release
cmake --build nomadim/build -j
```
Expected: configures (downloads yaml-cpp/CLI11/googletest), finds Boost, builds
`nomadim_core`, `nomadim`, `nomadim_tests` with no errors. If Boost is not found,
install it (see Prerequisites).

- [ ] **Step 8: Run tests**

Run: `ctest --test-dir nomadim/build --output-on-failure`
Expected: `Smoke.VersionIsNonEmpty` PASSES (100% tests passed).

- [ ] **Step 9: Commit**

```bash
git add nomadim/.gitignore nomadim/CMakeLists.txt nomadim/include nomadim/src nomadim/app nomadim/tests
git commit -m "feat(nomadim): project skeleton + CMake + smoke test"
```

---

## Task 1: Execution model

**Files:**
- Create: `nomadim/include/nomadim/execution.hpp`
- Create: `nomadim/src/execution.cpp`
- Test: `nomadim/tests/test_execution.cpp`
- Modify: `nomadim/CMakeLists.txt` (add sources)

- [ ] **Step 1: Add the test file and register it** — first edit `nomadim/CMakeLists.txt`:
  in the `add_library(nomadim_core ...)` list add `src/execution.cpp`, and in
  `add_executable(nomadim_tests ...)` add `tests/test_execution.cpp`.

- [ ] **Step 2: Write the failing test** — `nomadim/tests/test_execution.cpp`

```cpp
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
```

- [ ] **Step 3: Run it to confirm it fails**

Run: `cmake --build nomadim/build -j 2>&1 | head` — Expected: compile error
(`execution.hpp` not found / `Execution` undefined).

- [ ] **Step 4: Write the header** — `nomadim/include/nomadim/execution.hpp`

```cpp
#ifndef NOMADIM_EXECUTION_HPP
#define NOMADIM_EXECUTION_HPP

#include <vector>
#include <utility>

namespace nomadim {

// A distributed execution: n_procs processes plus an ordered list of
// synchronization events, each a pair of distinct process indices.
struct Execution {
    int n_procs = 0;
    std::vector<std::pair<int,int>> syncs;

    // Throws std::invalid_argument if n_procs <= 0, any endpoint is out of
    // [0, n_procs), or any sync pairs a process with itself.
    void validate() const;
};

} // namespace nomadim

#endif // NOMADIM_EXECUTION_HPP
```

- [ ] **Step 5: Write the implementation** — `nomadim/src/execution.cpp`

```cpp
#include "nomadim/execution.hpp"
#include <stdexcept>
#include <string>

namespace nomadim {

void Execution::validate() const {
    if (n_procs <= 0)
        throw std::invalid_argument("n_procs must be positive, got " + std::to_string(n_procs));
    for (auto const& s : syncs) {
        if (s.first < 0 || s.first >= n_procs || s.second < 0 || s.second >= n_procs)
            throw std::invalid_argument("sync endpoint out of range [0, " + std::to_string(n_procs) + ")");
        if (s.first == s.second)
            throw std::invalid_argument("sync cannot pair a process with itself");
    }
}

} // namespace nomadim
```

- [ ] **Step 6: Build and run tests**

Run: `cmake --build nomadim/build -j && ctest --test-dir nomadim/build --output-on-failure -R Execution`
Expected: 4 Execution tests PASS.

- [ ] **Step 7: Commit**

```bash
git add nomadim/CMakeLists.txt nomadim/include/nomadim/execution.hpp nomadim/src/execution.cpp nomadim/tests/test_execution.cpp
git commit -m "feat(nomadim): Execution model with validation"
```

---

## Task 2: ProcessGraph (event-structure DAG builder)

Faithful port of upstream `ProcessesGraph::init`/`sync`. Builds the DAG whose
reachability is the happened-before poset.

**Files:**
- Create: `nomadim/include/nomadim/process_graph.hpp`
- Create: `nomadim/src/process_graph.cpp`
- Test: `nomadim/tests/test_process_graph.cpp`
- Modify: `nomadim/CMakeLists.txt` (add `src/process_graph.cpp`, `tests/test_process_graph.cpp`)

- [ ] **Step 1: Register sources** in `nomadim/CMakeLists.txt` as in Task 1 Step 1.

- [ ] **Step 2: Write the failing test** — `nomadim/tests/test_process_graph.cpp`

```cpp
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
    // 4 initial + 3 per sync * 4 syncs = 16  => 4 + 12 = 16
    EXPECT_EQ((int)g.graph.size(), 16);
}
```

- [ ] **Step 3: Run to confirm failure**

Run: `cmake --build nomadim/build -j 2>&1 | head` — Expected: `process_graph.hpp` not found.

- [ ] **Step 4: Write the header** — `nomadim/include/nomadim/process_graph.hpp`

```cpp
#ifndef NOMADIM_PROCESS_GRAPH_HPP
#define NOMADIM_PROCESS_GRAPH_HPP

#include "nomadim/types.hpp"
#include "nomadim/execution.hpp"
#include <vector>
#include <string>
#include <unordered_set>
#include <utility>

namespace nomadim {

struct Label {
    int proc;
    int num;
};

// Event-structure DAG built from an execution. Each process is a chain of event
// vertices; each sync inserts a meet vertex joining the current last vertices of
// two processes and spawns two new last vertices.
class ProcessGraph {
public:
    int proc_num = 0;

    adjacency_list graph;                       // DAG adjacency (event -> successors)
    std::vector<int> proc_last_vertex;
    int next_vertex = 0;

    std::vector<std::unordered_set<int>> network;   // process-level sync adjacency
    std::vector<Label> labels;
    std::vector<std::vector<int>> proc_verteces;
    std::vector<std::pair<int,int>> syncs;

    using PEHash = std::vector<std::string>;
    PEHash proc_sync_name;                      // per-process synchronization signature

    void init(int process_num);
    void sync(int proc1, int proc2);

    // Convenience: init(e.n_procs) then replay e.syncs.
    static ProcessGraph build(const Execution& e);

private:
    int add_vertex_to_proc(int proc);
};

} // namespace nomadim

#endif // NOMADIM_PROCESS_GRAPH_HPP
```

- [ ] **Step 5: Write the implementation** — `nomadim/src/process_graph.cpp`
  (faithful port of upstream `init`/`sync`/`add_vertex_to_proc`)

```cpp
#include "nomadim/process_graph.hpp"
#include <cassert>

namespace nomadim {

void ProcessGraph::init(int process_num) {
    graph.clear();
    proc_num = process_num;
    proc_last_vertex.clear();
    next_vertex = 0;
    labels.clear();
    proc_verteces.clear();

    proc_last_vertex.resize(proc_num);
    proc_verteces.resize(proc_num);

    for (int i = 0; i < proc_num; ++i) {
        int cur_vert = next_vertex++;
        graph.push_back({});
        proc_last_vertex[i] = cur_vert;
        labels.push_back({i, 0});
        proc_verteces[i].push_back(cur_vert);
    }

    network.clear();
    network.resize(proc_num);
    proc_sync_name.clear();
    proc_sync_name.resize(proc_num);
}

int ProcessGraph::add_vertex_to_proc(int proc) {
    assert(proc >= 0 && proc < proc_num);
    int cur_vert = proc_last_vertex[proc];
    Label cur_label = labels[cur_vert];

    int new_vertex = next_vertex++;
    graph.push_back({});
    graph[cur_vert].push_back(new_vertex);
    proc_last_vertex[proc] = new_vertex;
    labels.push_back({proc, cur_label.num + 1});
    proc_verteces[proc].push_back(new_vertex);
    return new_vertex;
}

void ProcessGraph::sync(int proc1, int proc2) {
    assert(proc1 >= 0 && proc1 < proc_num);
    assert(proc2 >= 0 && proc2 < proc_num);

    syncs.emplace_back(proc1, proc2);

    int p1 = proc_last_vertex[proc1];
    int p2 = proc_last_vertex[proc2];

    int new_vertex = next_vertex++;  graph.push_back({});
    int p1nv = next_vertex++;        graph.push_back({});
    int p2nv = next_vertex++;        graph.push_back({});

    graph[p1].push_back(new_vertex);
    graph[p2].push_back(new_vertex);
    graph[new_vertex].push_back(p1nv);
    graph[new_vertex].push_back(p2nv);

    proc_last_vertex[proc1] = p1nv;
    proc_last_vertex[proc2] = p2nv;
    proc_verteces[proc1].push_back(p1nv);
    proc_verteces[proc2].push_back(p2nv);

    labels.push_back({-1, -1});
    labels.push_back({proc1, labels[p1].num + 1});
    labels.push_back({proc2, labels[p2].num + 1});

    network[proc1].insert(proc2);
    network[proc2].insert(proc1);

    char sync_num = (char)(syncs.size() - 1) + '0';
    proc_sync_name[proc1] += sync_num;
    proc_sync_name[proc2] += sync_num;
}

ProcessGraph ProcessGraph::build(const Execution& e) {
    ProcessGraph g;
    g.init(e.n_procs);
    for (auto const& s : e.syncs) g.sync(s.first, s.second);
    return g;
}

} // namespace nomadim
```

- [ ] **Step 6: Build and run tests**

Run: `cmake --build nomadim/build -j && ctest --test-dir nomadim/build --output-on-failure -R ProcessGraph`
Expected: 3 ProcessGraph tests PASS.

- [ ] **Step 7: Commit**

```bash
git add nomadim/CMakeLists.txt nomadim/include/nomadim/process_graph.hpp nomadim/src/process_graph.cpp nomadim/tests/test_process_graph.cpp
git commit -m "feat(nomadim): ProcessGraph event-structure DAG builder"
```

---

## Task 3: Floyd transitive closure

**Files:**
- Create: `nomadim/include/nomadim/floyd.hpp`
- Create: `nomadim/src/floyd.cpp`
- Test: `nomadim/tests/test_floyd.cpp`
- Modify: `nomadim/CMakeLists.txt`

- [ ] **Step 1: Register** `src/floyd.cpp` and `tests/test_floyd.cpp`.

- [ ] **Step 2: Write the failing test** — `nomadim/tests/test_floyd.cpp`

```cpp
#include <gtest/gtest.h>
#include "nomadim/floyd.hpp"
#include "nomadim/types.hpp"
#include <vector>

using namespace nomadim;

TEST(Floyd, ComputesReachabilityDistances) {
    // chain 0 -> 1 -> 2
    adjacency_list g = {{1}, {2}, {}};
    std::vector<int> m = make_graph_matrix(g);
    floyd(m.data(), 3);
    EXPECT_EQ(m[0*3 + 2], 2);   // 0 reaches 2 in 2 steps
    EXPECT_EQ(m[2*3 + 0], INF); // 2 does not reach 0
    EXPECT_EQ(m[1*3 + 1], 0);
}
```

- [ ] **Step 3: Run to confirm failure** — Expected: `floyd.hpp` not found.

- [ ] **Step 4: Write the header** — `nomadim/include/nomadim/floyd.hpp`

```cpp
#ifndef NOMADIM_FLOYD_HPP
#define NOMADIM_FLOYD_HPP

#include "nomadim/types.hpp"
#include <vector>

namespace nomadim {

// Build an n*n distance matrix (row-major) from an adjacency list:
// 0 on the diagonal, 1 for each edge, INF otherwise.
std::vector<int> make_graph_matrix(const adjacency_list& g);

// Floyd-Warshall all-pairs shortest paths in place.
void floyd(int* matrix, int n);

// Relax only paths passing through vertex v (used by critical-pair test).
void floyd_advance_vertex(int* matrix, int n, int v);

} // namespace nomadim

#endif // NOMADIM_FLOYD_HPP
```

- [ ] **Step 5: Write the implementation** — `nomadim/src/floyd.cpp`

```cpp
#include "nomadim/floyd.hpp"

namespace nomadim {

std::vector<int> make_graph_matrix(const adjacency_list& g) {
    int n = (int)g.size();
    std::vector<int> matrix(n * n, INF);
    for (int i = 0; i < n; ++i) matrix[i * n + i] = 0;
    for (int v = 0; v < n; ++v)
        for (int u : g[v]) matrix[v * n + u] = 1;
    return matrix;
}

void floyd(int* matrix, int n) {
    for (int k = 0; k < n; ++k)
        for (int i = 0; i < n; ++i) {
            int v = matrix[i * n + k];
            for (int j = 0; j < n; ++j) {
                int val = v + matrix[k * n + j];
                if (matrix[i * n + j] > val) matrix[i * n + j] = val;
            }
        }
}

void floyd_advance_vertex(int* matrix, int n, int v) {
    int k = v;
    for (int i = 0; i < n; ++i) {
        int vv = matrix[i * n + k];
        for (int j = 0; j < n; ++j) {
            int val = vv + matrix[k * n + j];
            if (matrix[i * n + j] > val) matrix[i * n + j] = val;
        }
    }
}

} // namespace nomadim
```

- [ ] **Step 6: Build and run tests**

Run: `cmake --build nomadim/build -j && ctest --test-dir nomadim/build --output-on-failure -R Floyd`
Expected: Floyd test PASSES.

- [ ] **Step 7: Commit**

```bash
git add nomadim/CMakeLists.txt nomadim/include/nomadim/floyd.hpp nomadim/src/floyd.cpp nomadim/tests/test_floyd.cpp
git commit -m "feat(nomadim): Floyd transitive closure"
```

---

## Task 4: Dimension-2 test

The headline algorithm: critical pairs + incompatibility-graph bipartiteness.
Operates on a plain `adjacency_list`, so it serves both executions and posets.

**Files:**
- Create: `nomadim/include/nomadim/dimension.hpp`
- Create: `nomadim/src/dimension.cpp`
- Test: `nomadim/tests/test_dimension.cpp`
- Modify: `nomadim/CMakeLists.txt`

- [ ] **Step 1: Register** `src/dimension.cpp` and `tests/test_dimension.cpp`.

- [ ] **Step 2: Write the failing test** — `nomadim/tests/test_dimension.cpp`

```cpp
#include <gtest/gtest.h>
#include "nomadim/dimension.hpp"
#include "nomadim/process_graph.hpp"
#include "nomadim/execution.hpp"
#include "nomadim/types.hpp"

using namespace nomadim;

TEST(Dimension, HelpersDetectCycleAndBipartite) {
    adjacency_list cyc = {{1}, {2}, {0}};
    EXPECT_TRUE(have_cycle(cyc));
    adjacency_list dag = {{1}, {2}, {}};
    EXPECT_FALSE(have_cycle(dag));

    adjacency_list even = {{1}, {0, 2}, {1}}; // path: bipartite
    EXPECT_TRUE(is_bipartite(even));
    adjacency_list tri = {{1, 2}, {0, 2}, {0, 1}}; // triangle: not bipartite
    EXPECT_FALSE(is_bipartite(tri));
}

// chain has dimension 1 (no critical pairs); single sync expands to a dim-2
// poset. Both verified against the upstream algorithm as oracle.
TEST(Dimension, ChainIsDim2) {
    adjacency_list chain = {{1}, {2}, {3}, {}};
    EXPECT_TRUE(is_dim2(chain));
}

TEST(Dimension, SingleSyncExecutionIsDim2) {
    Execution e{2, {{0, 1}}};
    ProcessGraph g = ProcessGraph::build(e);
    EXPECT_TRUE(is_dim2(g.graph));
}

// Matches upstream check_poset: this hardcoded execution is NOT 2-dimensional
// (25 critical pairs; incompatibility graph not bipartite).
TEST(Dimension, CanonicalExecutionIsNotDim2) {
    Execution e{4, {{0,1},{1,2},{2,3},{0,2}}};
    ProcessGraph g = ProcessGraph::build(e);
    EXPECT_FALSE(is_dim2(g.graph));
}

TEST(Dimension, StandardExampleS3IsNotDim2) {
    // S_3: minimals 0,1,2 ; maximals 3,4,5 ; a_i < b_j for i != j.
    adjacency_list s3(6);
    s3[0] = {4, 5};
    s3[1] = {3, 5};
    s3[2] = {3, 4};
    EXPECT_FALSE(is_dim2(s3));
}
```

- [ ] **Step 3: Run to confirm failure** — Expected: `dimension.hpp` not found.

- [ ] **Step 4: Write the header** — `nomadim/include/nomadim/dimension.hpp`

```cpp
#ifndef NOMADIM_DIMENSION_HPP
#define NOMADIM_DIMENSION_HPP

#include "nomadim/types.hpp"
#include <vector>

namespace nomadim {

// True if the directed graph contains a cycle (DFS, recursion stack).
bool have_cycle(const adjacency_list& g);

// True if the undirected graph (given as symmetric adjacency) is 2-colorable.
bool is_bipartite(const adjacency_list& g);

// (x,y) is critical if forcing edge x->y collapses no OTHER incomparable pair.
// `matrix` is the n*n transitive-closure distance matrix (already Floyd'd).
bool check_if_critical(const int* matrix, int n, int x, int y);

// All critical pairs of the poset whose closure is `matrix` (n*n, modified in place).
std::vector<critical_pair> find_critical_pairs(int* matrix, int n);

// Build the incompatibility graph on critical pairs (two conflict if reversing
// both creates a cycle in `poset_graph`) and return whether it is bipartite.
bool check_critical_pairs_graph(const adjacency_list& poset_graph,
                                const std::vector<critical_pair>& critical_pairs);

// True iff the poset given by adjacency `g` has order dimension <= 2.
bool is_dim2(const adjacency_list& g);

} // namespace nomadim

#endif // NOMADIM_DIMENSION_HPP
```

- [ ] **Step 5: Write the implementation** — `nomadim/src/dimension.cpp`
  (faithful port of upstream `have_cycle`, `is_bipartite`, `check_if_critical`,
  `find_critical_pairs`, `check_critical_pairs_graph`, `is_poset_2_dimensional`)

```cpp
#include "nomadim/dimension.hpp"
#include "nomadim/floyd.hpp"
#include <functional>
#include <vector>
#include <cstring>

namespace nomadim {

bool have_cycle(const adjacency_list& g) {
    std::vector<bool> used(g.size(), false), cur_way(g.size(), false);
    std::function<bool(int)> dfs = [&](int v) -> bool {
        used[v] = true;
        cur_way[v] = true;
        for (int u : g[v]) {
            if (cur_way[u]) return true;
            if (!used[u] && dfs(u)) return true;
        }
        cur_way[v] = false;
        return false;
    };
    for (int i = 0; i < (int)g.size(); ++i)
        if (!used[i] && dfs(i)) return true;
    return false;
}

bool is_bipartite(const adjacency_list& g) {
    std::vector<int> label(g.size(), -1);
    std::function<bool(int,int)> dfs = [&](int v, int lbl) -> bool {
        label[v] = lbl;
        int nl = lbl == 0 ? 1 : 0;
        for (int u : g[v]) {
            if (label[u] != -1 && label[u] != nl) return false;
            if (label[u] == -1 && !dfs(u, nl)) return false;
        }
        return true;
    };
    for (int i = 0; i < (int)g.size(); ++i)
        if (label[i] == -1 && !dfs(i, 0)) return false;
    return true;
}

bool check_if_critical(const int* matrix, int n, int x, int y) {
    std::vector<int> nm(matrix, matrix + n * n);
    nm[x * n + y] = 1;
    floyd_advance_vertex(nm.data(), n, x);
    floyd_advance_vertex(nm.data(), n, y);
    for (int v = 0; v < n; ++v)
        for (int u = 0; u < n; ++u) {
            if (v == x && u == y) continue;
            if (matrix[v * n + u] == INF && nm[v * n + u] != INF) return false;
        }
    return true;
}

std::vector<critical_pair> find_critical_pairs(int* matrix, int n) {
    std::vector<critical_pair> cps;
    floyd(matrix, n);
    for (int v = 0; v < n; ++v)
        for (int u = 0; u < n; ++u)
            if (matrix[v * n + u] == INF && matrix[u * n + v] == INF)
                if (check_if_critical(matrix, n, v, u))
                    cps.push_back({v, u});
    return cps;
}

bool check_critical_pairs_graph(const adjacency_list& poset_graph,
                                const std::vector<critical_pair>& cps) {
    adjacency_list icg(cps.size());
    for (size_t i = 0; i < cps.size(); ++i)
        for (size_t j = i + 1; j < cps.size(); ++j) {
            adjacency_list lg = poset_graph;
            lg[cps[i].y].push_back(cps[i].x);
            lg[cps[j].y].push_back(cps[j].x);
            if (have_cycle(lg)) {
                icg[i].push_back((int)j);
                icg[j].push_back((int)i);
            }
        }
    return is_bipartite(icg);
}

bool is_dim2(const adjacency_list& g) {
    std::vector<int> matrix = make_graph_matrix(g);
    int n = (int)g.size();
    floyd(matrix.data(), n);
    auto cps = find_critical_pairs(matrix.data(), n);
    return check_critical_pairs_graph(g, cps);
}

} // namespace nomadim
```

- [ ] **Step 6: Build and run tests**

Run: `cmake --build nomadim/build -j && ctest --test-dir nomadim/build --output-on-failure -R Dimension`
Expected: 5 Dimension tests PASS (chain and single-sync are dim2; the canonical
4-proc execution and S_3 are NOT dim2 — these expectations were verified against
the upstream binary as an oracle; do not change the algorithm to flip them).

- [ ] **Step 7: Commit**

```bash
git add nomadim/CMakeLists.txt nomadim/include/nomadim/dimension.hpp nomadim/src/dimension.cpp nomadim/tests/test_dimension.cpp
git commit -m "feat(nomadim): dimension-2 test (critical pairs + bipartiteness)"
```

---

## Task 5: General Poset + conversion from ProcessGraph

**Files:**
- Create: `nomadim/include/nomadim/poset.hpp`
- Create: `nomadim/src/poset.cpp`
- Test: `nomadim/tests/test_poset.cpp`
- Modify: `nomadim/CMakeLists.txt`

- [ ] **Step 1: Register** `src/poset.cpp` and `tests/test_poset.cpp`.

- [ ] **Step 2: Write the failing test** — `nomadim/tests/test_poset.cpp`

```cpp
#include <gtest/gtest.h>
#include "nomadim/poset.hpp"
#include "nomadim/process_graph.hpp"
#include "nomadim/execution.hpp"
#include "nomadim/dimension.hpp"
#include <stdexcept>

using namespace nomadim;

TEST(Poset, ValidatesBounds) {
    Poset p{3, {{0,1},{1,2}}};
    EXPECT_NO_THROW(p.validate());
    Poset bad{2, {{0,5}}};
    EXPECT_THROW(bad.validate(), std::invalid_argument);
}

TEST(Poset, RejectsCyclicEdges) {
    Poset cyc{3, {{0,1},{1,2},{2,0}}};
    EXPECT_THROW(cyc.validate(), std::invalid_argument);
}

TEST(Poset, FromProcessGraphMatchesGraph) {
    Execution e{4, {{0,1},{1,2},{2,3},{0,2}}};
    ProcessGraph g = ProcessGraph::build(e);
    Poset p = Poset::from(g);
    EXPECT_EQ(p.n_vertices, (int)g.graph.size());
    EXPECT_EQ(p.edges, g.graph);
    EXPECT_TRUE(is_dim2(p.edges));
}
```

- [ ] **Step 3: Run to confirm failure** — Expected: `poset.hpp` not found.

- [ ] **Step 4: Write the header** — `nomadim/include/nomadim/poset.hpp`

```cpp
#ifndef NOMADIM_POSET_HPP
#define NOMADIM_POSET_HPP

#include "nomadim/types.hpp"

namespace nomadim {

class ProcessGraph; // fwd decl

// A general poset given by its cover/adjacency relation. edges[u] lists the
// vertices directly above u; the reachability closure is the partial order.
struct Poset {
    int n_vertices = 0;
    adjacency_list edges;

    // Throws std::invalid_argument if n_vertices < 0, edges.size() != n_vertices,
    // any endpoint is out of range, or the relation contains a cycle.
    void validate() const;

    // Build a Poset from a process-graph DAG (verbatim adjacency).
    static Poset from(const ProcessGraph& g);
};

} // namespace nomadim

#endif // NOMADIM_POSET_HPP
```

- [ ] **Step 5: Write the implementation** — `nomadim/src/poset.cpp`

```cpp
#include "nomadim/poset.hpp"
#include "nomadim/process_graph.hpp"
#include "nomadim/dimension.hpp"   // have_cycle
#include <stdexcept>
#include <string>

namespace nomadim {

void Poset::validate() const {
    if (n_vertices < 0)
        throw std::invalid_argument("n_vertices must be non-negative");
    if ((int)edges.size() != n_vertices)
        throw std::invalid_argument("edges.size() must equal n_vertices");
    for (int u = 0; u < n_vertices; ++u)
        for (int v : edges[u])
            if (v < 0 || v >= n_vertices)
                throw std::invalid_argument("edge endpoint out of range");
    if (have_cycle(edges))
        throw std::invalid_argument("poset cover relation must be acyclic");
}

Poset Poset::from(const ProcessGraph& g) {
    Poset p;
    p.n_vertices = (int)g.graph.size();
    p.edges = g.graph;
    return p;
}

} // namespace nomadim
```

- [ ] **Step 6: Build and run tests**

Run: `cmake --build nomadim/build -j && ctest --test-dir nomadim/build --output-on-failure -R Poset`
Expected: 3 Poset tests PASS.

- [ ] **Step 7: Commit**

```bash
git add nomadim/CMakeLists.txt nomadim/include/nomadim/poset.hpp nomadim/src/poset.cpp nomadim/tests/test_poset.cpp
git commit -m "feat(nomadim): general Poset + conversion from ProcessGraph"
```

---

## Task 6: Isomorphism

**Files:**
- Create: `nomadim/include/nomadim/isomorphism.hpp`
- Create: `nomadim/src/isomorphism.cpp`
- Test: `nomadim/tests/test_isomorphism.cpp`
- Modify: `nomadim/CMakeLists.txt`

- [ ] **Step 1: Register** `src/isomorphism.cpp` and `tests/test_isomorphism.cpp`.

- [ ] **Step 2: Write the failing test** — `nomadim/tests/test_isomorphism.cpp`

```cpp
#include <gtest/gtest.h>
#include "nomadim/isomorphism.hpp"
#include "nomadim/process_graph.hpp"
#include "nomadim/execution.hpp"

using namespace nomadim;

TEST(Isomorphism, ReflexiveAndPermutationInvariant) {
    ProcessGraph a = ProcessGraph::build(Execution{4, {{0,1},{1,2},{2,3},{0,2}}});
    ProcessGraph b = ProcessGraph::build(Execution{4, {{0,1},{1,2},{2,3},{0,2}}});
    EXPECT_TRUE(is_isomorphic(a, b));
}

TEST(Isomorphism, DistinguishesDifferentExecutions) {
    // path-of-syncs vs star-of-syncs: structurally distinct, not isomorphic
    // (verified against upstream as oracle). Do NOT use (0,1),(1,2) vs
    // (0,1),(0,2) here -- those ARE isomorphic via relabeling.
    ProcessGraph path = ProcessGraph::build(Execution{4, {{0,1},{1,2},{2,3}}});
    ProcessGraph star = ProcessGraph::build(Execution{4, {{0,1},{0,2},{0,3}}});
    EXPECT_FALSE(is_isomorphic(path, star));
}

TEST(Isomorphism, GenerateAllIsomorphicCardinality) {
    ProcessGraph a = ProcessGraph::build(Execution{3, {{0,1}}});
    auto all = generate_all_isomorphic(a);
    EXPECT_EQ(all.size(), 6u); // 3! permutations
}
```

- [ ] **Step 3: Run to confirm failure** — Expected: `isomorphism.hpp` not found.

- [ ] **Step 4: Write the header** — `nomadim/include/nomadim/isomorphism.hpp`

```cpp
#ifndef NOMADIM_ISOMORPHISM_HPP
#define NOMADIM_ISOMORPHISM_HPP

#include "nomadim/process_graph.hpp"
#include <vector>

namespace nomadim {

// True if the two process graphs are isomorphic under a process permutation.
bool is_isomorphic(const ProcessGraph& l, const ProcessGraph& r);

// All process graphs obtained by permuting the process labels of `pg`'s syncs.
std::vector<ProcessGraph> generate_all_isomorphic(const ProcessGraph& pg);

// Canonical (sorted) per-process synchronization signature, used as a cache key.
ProcessGraph::PEHash canonical_sync_name(const ProcessGraph& pg);

} // namespace nomadim

#endif // NOMADIM_ISOMORPHISM_HPP
```

- [ ] **Step 5: Write the implementation** — `nomadim/src/isomorphism.cpp`
  (faithful port of upstream `is_isomorphic` and `generate_all_isomorphic`)

```cpp
#include "nomadim/isomorphism.hpp"
#include <algorithm>
#include <numeric>

namespace nomadim {

bool is_isomorphic(const ProcessGraph& pgl, const ProcessGraph& pgr) {
    if (pgl.proc_num != pgr.proc_num) return false;
    if (pgl.graph.size() != pgr.graph.size()) return false;
    if (pgl.proc_verteces.size() != pgr.proc_verteces.size()) return false;
    if (pgl.labels.size() != pgr.labels.size()) return false;

    std::vector<int> perm(pgr.proc_num);
    std::iota(perm.begin(), perm.end(), 0);

    bool isomorphic = false;
    do {
        bool sizes_ok = true;
        for (size_t i = 0; i < pgl.proc_verteces.size() && sizes_ok; ++i)
            if (pgl.proc_verteces[i].size() != pgr.proc_verteces[perm[i]].size())
                sizes_ok = false;
        if (!sizes_ok) continue;

        bool labels_ok = true;
        for (int p = 0; p < (int)pgl.proc_verteces.size() && labels_ok; ++p) {
            for (size_t i = 0; i < pgl.proc_verteces[p].size() && labels_ok; ++i) {
                int vl = pgl.proc_verteces[p][i];
                int vr = pgr.proc_verteces[perm[p]][i];
                if (pgl.labels[vl].num != pgr.labels[vr].num) { labels_ok = false; break; }
                if (pgl.graph[vl].size() != pgr.graph[vr].size()) { labels_ok = false; break; }
                if (!pgl.graph[vl].empty()) {
                    int vls = pgl.graph[vl][0];
                    int vrs = pgr.graph[vr][0];
                    int vlas1 = pgl.graph[vls][0], vlas2 = pgl.graph[vls][1];
                    int vras1 = pgr.graph[vrs][0], vras2 = pgr.graph[vrs][1];
                    int vlo = (pgl.labels[vlas1].proc == p) ? vlas2 : vlas1;
                    int vro = (pgr.labels[vras1].proc == perm[p]) ? vras2 : vras1;
                    if (perm[pgl.labels[vlo].proc] != pgr.labels[vro].proc ||
                        pgl.labels[vlo].num != pgr.labels[vro].num) {
                        labels_ok = false; break;
                    }
                }
            }
        }
        if (!labels_ok) continue;
        isomorphic = true;
    } while (!isomorphic && std::next_permutation(perm.begin(), perm.end()));

    return isomorphic;
}

std::vector<ProcessGraph> generate_all_isomorphic(const ProcessGraph& pg) {
    std::vector<int> perm(pg.proc_num);
    std::iota(perm.begin(), perm.end(), 0);
    std::vector<ProcessGraph> ret;
    do {
        ProcessGraph npg;
        npg.init(pg.proc_num);
        for (auto const& s : pg.syncs)
            npg.sync(std::min(perm[s.first], perm[s.second]),
                     std::max(perm[s.first], perm[s.second]));
        ret.push_back(npg);
    } while (std::next_permutation(perm.begin(), perm.end()));
    return ret;
}

ProcessGraph::PEHash canonical_sync_name(const ProcessGraph& pg) {
    auto names = pg.proc_sync_name;
    std::sort(names.begin(), names.end());
    return names;
}

} // namespace nomadim
```

- [ ] **Step 6: Build and run tests**

Run: `cmake --build nomadim/build -j && ctest --test-dir nomadim/build --output-on-failure -R Isomorphism`
Expected: 3 Isomorphism tests PASS.

- [ ] **Step 7: Commit**

```bash
git add nomadim/CMakeLists.txt nomadim/include/nomadim/isomorphism.hpp nomadim/src/isomorphism.cpp nomadim/tests/test_isomorphism.cpp
git commit -m "feat(nomadim): process-graph isomorphism + canonical sync name"
```

---

## Task 7: Enumerator (multithreaded + multifibered)

Port of upstream `enumerate_isomorphic` generate_graph: recursive sync expansion
pruned by the canonical sync-name cache. Full synchronization is tested with the
upstream `is_full_syncronized` predicate; fully-synced dim-2 results are
deduplicated by isomorphism. The returned **count** is deterministic regardless
of thread count.

> **IMPLEMENTATION NOTE (supersedes the boost::fiber work-stealing code shown
> below):** boost::fiber was dropped entirely (the user authorized replacing it
> if it failed, and it did). Two boost::fiber dead-ends: (1) the `work_stealing`
> scheduler SIGBUS-crashes when its threads are created/destroyed across repeated
> `enumerate()` calls (process-global state; confirmed via the macOS `.ips` crash
> report, not a stack overflow); (2) the default round-robin scheduler with one
> fiber per first-level branch is correct but gets no speedup — by symmetry the
> first-level syncs are all isomorphic, so the cache collapses them to one active
> branch (one core).
>
> The shipped design is a plain **std::thread work-pool** (no Boost): a shared
> work deque of `(ProcessGraph, sync_num)` tasks; `threads` workers pop tasks,
> process the node, and queue shallow children / inline deep ones. Duplicates are
> pruned via a 64-shard cache BEFORE queuing, so distinct subtrees spread across
> cores (measured ~5.6x j=1→j=8). Results are bucketed by a cheap isomorphism
> invariant (vertex count + sorted per-process event counts) so `is_isomorphic`
> only compares within a bucket. Counts are deterministic regardless of thread
> count. Boost is NOT a dependency. See the committed `nomadim/src/enumerate.cpp`.

**Files:**
- Create: `nomadim/include/nomadim/enumerate.hpp`
- Create: `nomadim/src/enumerate.cpp`
- Test: `nomadim/tests/test_enumerate.cpp`
- Modify: `nomadim/CMakeLists.txt`

- [ ] **Step 1: Register** `src/enumerate.cpp` and `tests/test_enumerate.cpp`.

- [ ] **Step 2: Write the failing test** — `nomadim/tests/test_enumerate.cpp`

```cpp
#include <gtest/gtest.h>
#include "nomadim/enumerate.hpp"

using namespace nomadim;

// Default tier: cheap golden counts (run on every invocation).
TEST(Enumerate, GoldenCountsDefaultTier) {
    EXPECT_EQ(enumerate(2, 8, 1).count, 1);
    EXPECT_EQ(enumerate(3, 3, 1).count, 2);
    EXPECT_EQ(enumerate(3, 4, 1).count, 6);
    EXPECT_EQ(enumerate(3, 5, 1).count, 12);
    EXPECT_EQ(enumerate(3, 6, 1).count, 20);
    EXPECT_EQ(enumerate(4, 5, 1).count, 10);
    EXPECT_EQ(enumerate(4, 6, 1).count, 102);
    EXPECT_EQ(enumerate(4, 7, 1).count, 634);
    EXPECT_EQ(enumerate(5, 7, 1).count, 40);
}

TEST(Enumerate, ThreadCountDoesNotChangeResult) {
    EXPECT_EQ(enumerate(4, 5, 1).count, enumerate(4, 5, 4).count);
}

#ifdef NOMADIM_SLOW_TESTS
TEST(EnumerateSlow, GoldenCountsSlowTier) {
    EXPECT_EQ(enumerate(4, 8, 4).count, 3058);
    EXPECT_EQ(enumerate(4, 9, 4).count, 12784);
    EXPECT_EQ(enumerate(5, 8, 4).count, 704);
    EXPECT_EQ(enumerate(6, 9, 4).count, 1036);
}
#endif
```

- [ ] **Step 3: Run to confirm failure** — Expected: `enumerate.hpp` not found.

- [ ] **Step 4: Write the header** — `nomadim/include/nomadim/enumerate.hpp`

```cpp
#ifndef NOMADIM_ENUMERATE_HPP
#define NOMADIM_ENUMERATE_HPP

#include "nomadim/process_graph.hpp"
#include <vector>

namespace nomadim {

struct EnumerateResult {
    int count = 0;                            // # non-isomorphic dim-2 synced executions
    int isomorphic_hits = 0;                  // # collapsed by isomorphism
    std::vector<ProcessGraph> results;        // the representatives
};

// True if, in g's transitive closure, every process' last vertex is reachable
// from every process' start (fully synchronized execution).
bool is_full_synchronized(const ProcessGraph& g);

// Enumerate non-isomorphic, fully-synchronized, dimension-2 executions of
// n_procs processes using up to max_sync syncs, with `threads` worker threads
// (>= 1; 1 = single-threaded). The .count is independent of `threads`.
EnumerateResult enumerate(int n_procs, int max_sync, unsigned threads);

} // namespace nomadim

#endif // NOMADIM_ENUMERATE_HPP
```

- [ ] **Step 5: Write the implementation** — `nomadim/src/enumerate.cpp`
  (port of upstream `is_full_syncronized` + `generate_graph`, with the cache,
  isomorphism dedup, and boost::fiber work-stealing parametrized by `threads`)

```cpp
#include "nomadim/enumerate.hpp"
#include "nomadim/floyd.hpp"
#include "nomadim/dimension.hpp"
#include "nomadim/isomorphism.hpp"

#include <boost/fiber/all.hpp>
#include <unordered_set>
#include <mutex>
#include <thread>
#include <atomic>
#include <algorithm>

namespace nomadim {
namespace bf = boost::fibers;

bool is_full_synchronized(const ProcessGraph& g) {
    std::vector<int> m = make_graph_matrix(g.graph);
    int n = (int)g.graph.size();
    floyd(m.data(), n);
    for (int start = 0; start < g.proc_num; ++start)
        for (int last : g.proc_last_vertex)
            if (m[start * n + last] == INF) return false;
    return true;
}

namespace {

// PEHash hashing for the prune cache.
struct PEHashHash {
    size_t operator()(const ProcessGraph::PEHash& s) const noexcept {
        std::hash<std::string> h; size_t ret = 0;
        for (auto const& x : s) ret ^= h(x) + 0x9e3779b97f4a7c15ULL + (ret << 6) + (ret >> 2);
        return ret;
    }
};

struct EnumState {
    int max_sync;
    std::unordered_set<ProcessGraph::PEHash, PEHashHash> cache;
    bf::mutex cache_mut;
    bf::mutex rp_mut;
    std::vector<ProcessGraph> results;
    std::atomic<int> count{0};
    std::atomic<int> iso_hits{0};
    std::atomic<int> fork_count{0};

    using salloc_t = bf::fixedsize_stack;
    salloc_t* salloc = nullptr;
};

void generate_graph(EnumState& st, ProcessGraph g, int sync_num) {
    if (sync_num > st.max_sync) return;

    {
        std::lock_guard<bf::mutex> lk(st.cache_mut);
        auto key = canonical_sync_name(g);
        if (st.cache.find(key) != st.cache.end()) return;
        st.cache.insert(std::move(key));
    }

    if (is_full_synchronized(g)) {
        if (is_dim2(g.graph)) {
            bool iso = false;
            {
                std::lock_guard<bf::mutex> lk(st.rp_mut);
                for (auto const& p : st.results)
                    if (is_isomorphic(p, g)) { iso = true; break; }
                if (!iso) st.results.push_back(g);
            }
            if (iso) st.iso_hits++;
            else st.count++;
        }
        return;
    }

    int proc_num = g.proc_num;
    for (int p1 = 0; p1 < proc_num; ++p1)
        for (int p2 = p1 + 1; p2 < proc_num; ++p2) {
            ProcessGraph ng = g;
            ng.sync(p1, p2);
            if (st.fork_count < 4) {
                st.fork_count++;
                bf::fiber{
                    bf::launch::dispatch,
                    std::allocator_arg, *st.salloc,
                    [&st](ProcessGraph gg, int s){ generate_graph(st, std::move(gg), s); },
                    std::move(ng), sync_num + 1
                }.join();
                st.fork_count--;
            } else {
                generate_graph(st, std::move(ng), sync_num + 1);
            }
        }
}

} // namespace

EnumerateResult enumerate(int n_procs, int max_sync, unsigned threads) {
    if (threads < 1) threads = 1;

    EnumState st;
    st.max_sync = max_sync;
    EnumState::salloc_t salloc{ EnumState::salloc_t::traits_type::page_size() * 4 };
    st.salloc = &salloc;

    bf::use_scheduling_algorithm<bf::algo::work_stealing>(threads);

    std::mutex mtx;
    bf::condition_variable_any cnd;
    bool done = false;

    std::vector<std::thread> pool;
    for (unsigned i = 1; i < threads; ++i) {
        pool.emplace_back([threads, &mtx, &done, &cnd] {
            bf::use_scheduling_algorithm<bf::algo::work_stealing>(threads);
            std::unique_lock<std::mutex> lk(mtx);
            cnd.wait(lk, [&done]{ return done; });
        });
    }

    ProcessGraph g;
    g.init(n_procs);
    bf::fiber{
        bf::launch::dispatch,
        std::allocator_arg, salloc,
        [&st](ProcessGraph gg){ generate_graph(st, std::move(gg), 0); },
        std::move(g)
    }.join();

    { std::unique_lock<std::mutex> lk(mtx); done = true; }
    cnd.notify_all();
    for (auto& t : pool) t.join();

    EnumerateResult r;
    r.count = st.count.load();
    r.isomorphic_hits = st.iso_hits.load();
    r.results = std::move(st.results);
    return r;
}

} // namespace nomadim
```

- [ ] **Step 6: Build and run the default-tier tests**

Run: `cmake --build nomadim/build -j && ctest --test-dir nomadim/build --output-on-failure -R Enumerate`
Expected: `Enumerate.GoldenCountsDefaultTier` and `Enumerate.ThreadCountDoesNotChangeResult` PASS.
(If a count is off, the bug is in the ported algorithm — debug against upstream
before proceeding; do not adjust the expected numbers.)

- [ ] **Step 7: Verify the slow tier builds and passes**

Run:
```bash
cmake -S nomadim -B nomadim/build-slow -DNOMADIM_SLOW_TESTS=ON
cmake --build nomadim/build-slow -j
ctest --test-dir nomadim/build-slow --output-on-failure -R EnumerateSlow
```
Expected: `EnumerateSlow.GoldenCountsSlowTier` PASSES (may take a few minutes).

- [ ] **Step 8: Commit**

```bash
git add nomadim/CMakeLists.txt nomadim/include/nomadim/enumerate.hpp nomadim/src/enumerate.cpp nomadim/tests/test_enumerate.cpp
git commit -m "feat(nomadim): multithreaded+multifibered dim-2 enumerator"
```

---

## Task 8: YAML I/O

Both schemas. A document has optional top-level `execution` and/or `poset` keys.

**Files:**
- Create: `nomadim/include/nomadim/io.hpp`
- Create: `nomadim/src/io.cpp`
- Test: `nomadim/tests/test_io.cpp`
- Modify: `nomadim/CMakeLists.txt`

- [ ] **Step 1: Register** `src/io.cpp` and `tests/test_io.cpp`.

- [ ] **Step 2: Write the failing test** — `nomadim/tests/test_io.cpp`

```cpp
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
        "poset:\n  n_vertices: 2\n  edges: [[0,1],[]]\n");
    EXPECT_TRUE(d.execution.has_value());
    EXPECT_TRUE(d.poset.has_value());
}

TEST(Io, RejectsMalformedSyncPair) {
    EXPECT_THROW(parse_document("execution:\n  n_procs: 2\n  syncs: [[0,1,2]]\n"),
                 std::runtime_error);
}

TEST(Io, RejectsDocumentWithNeitherKey) {
    EXPECT_THROW(parse_document("foo: 1\n"), std::runtime_error);
}
```

- [ ] **Step 3: Run to confirm failure** — Expected: `io.hpp` not found.

- [ ] **Step 4: Write the header** — `nomadim/include/nomadim/io.hpp`

```cpp
#ifndef NOMADIM_IO_HPP
#define NOMADIM_IO_HPP

#include "nomadim/execution.hpp"
#include "nomadim/poset.hpp"
#include <optional>
#include <string>

namespace nomadim {

// A parsed YAML document: may contain an execution, a poset, or both.
struct Document {
    std::optional<Execution> execution;
    std::optional<Poset> poset;
};

// Parse YAML text. Throws std::runtime_error on parse errors, on malformed
// sync/edge pairs (each must be a 2-element list), or if neither top-level key
// (`execution`/`poset`) is present. The contained values are validated.
Document parse_document(const std::string& text);

// Read and parse a file (throws std::runtime_error if it cannot be opened).
Document load_file(const std::string& path);

// Serialize to YAML text.
std::string dump_execution(const Execution& e);
std::string dump_poset(const Poset& p);

// Write text to a file (throws std::runtime_error if it cannot be opened).
void save_file(const std::string& path, const std::string& text);

} // namespace nomadim

#endif // NOMADIM_IO_HPP
```

- [ ] **Step 5: Write the implementation** — `nomadim/src/io.cpp`

```cpp
#include "nomadim/io.hpp"
#include <yaml-cpp/yaml.h>
#include <fstream>
#include <sstream>
#include <stdexcept>

namespace nomadim {

namespace {
std::pair<int,int> read_pair(const YAML::Node& n, const char* what) {
    if (!n.IsSequence() || n.size() != 2)
        throw std::runtime_error(std::string(what) + " must be a 2-element list");
    return {n[0].as<int>(), n[1].as<int>()};
}
} // namespace

Document parse_document(const std::string& text) {
    YAML::Node root;
    try {
        root = YAML::Load(text);
    } catch (const YAML::Exception& e) {
        throw std::runtime_error(std::string("YAML parse error: ") + e.what());
    }
    if (!root || !root.IsMap())
        throw std::runtime_error("document must be a YAML mapping");

    Document doc;
    if (root["execution"]) {
        const YAML::Node& en = root["execution"];
        Execution e;
        e.n_procs = en["n_procs"].as<int>();
        if (en["syncs"])
            for (const auto& s : en["syncs"]) e.syncs.push_back(read_pair(s, "sync"));
        e.validate();
        doc.execution = std::move(e);
    }
    if (root["poset"]) {
        const YAML::Node& pn = root["poset"];
        Poset p;
        p.n_vertices = pn["n_vertices"].as<int>();
        p.edges.assign(p.n_vertices, {});
        if (pn["edges"])
            for (const auto& edge : pn["edges"]) {
                auto uv = read_pair(edge, "edge");
                if (uv.first < 0 || uv.first >= p.n_vertices)
                    throw std::runtime_error("edge source out of range");
                p.edges[uv.first].push_back(uv.second);
            }
        p.validate();
        doc.poset = std::move(p);
    }
    if (!doc.execution && !doc.poset)
        throw std::runtime_error("document must contain an 'execution' or 'poset' key");
    return doc;
}

Document load_file(const std::string& path) {
    std::ifstream in(path);
    if (!in) throw std::runtime_error("cannot open file: " + path);
    std::stringstream ss; ss << in.rdbuf();
    return parse_document(ss.str());
}

std::string dump_execution(const Execution& e) {
    YAML::Emitter out;
    out << YAML::BeginMap << YAML::Key << "execution" << YAML::Value << YAML::BeginMap;
    out << YAML::Key << "n_procs" << YAML::Value << e.n_procs;
    out << YAML::Key << "syncs" << YAML::Value << YAML::BeginSeq;
    for (auto const& s : e.syncs) {
        out << YAML::Flow << YAML::BeginSeq << s.first << s.second << YAML::EndSeq;
    }
    out << YAML::EndSeq << YAML::EndMap << YAML::EndMap;
    return out.c_str();
}

std::string dump_poset(const Poset& p) {
    YAML::Emitter out;
    out << YAML::BeginMap << YAML::Key << "poset" << YAML::Value << YAML::BeginMap;
    out << YAML::Key << "n_vertices" << YAML::Value << p.n_vertices;
    out << YAML::Key << "edges" << YAML::Value << YAML::BeginSeq;
    for (int u = 0; u < p.n_vertices; ++u)
        for (int v : p.edges[u])
            out << YAML::Flow << YAML::BeginSeq << u << v << YAML::EndSeq;
    out << YAML::EndSeq << YAML::EndMap << YAML::EndMap;
    return out.c_str();
}

void save_file(const std::string& path, const std::string& text) {
    std::ofstream o(path);
    if (!o) throw std::runtime_error("cannot open file for writing: " + path);
    o << text;
}

} // namespace nomadim
```

Note: `dump_poset` then `parse_document` round-trips edges exactly because the
parser appends per source vertex in document order, matching the emitter's
`for u { for v }` order.

- [ ] **Step 6: Build and run tests**

Run: `cmake --build nomadim/build -j && ctest --test-dir nomadim/build --output-on-failure -R Io`
Expected: 5 Io tests PASS.

- [ ] **Step 7: Commit**

```bash
git add nomadim/CMakeLists.txt nomadim/include/nomadim/io.hpp nomadim/src/io.cpp nomadim/tests/test_io.cpp
git commit -m "feat(nomadim): YAML I/O for execution and poset documents"
```

---

## Task 9: CLI (check / enumerate / convert)

**Files:**
- Create: `nomadim/app/cmd_check.hpp`, `nomadim/app/cmd_check.cpp`
- Create: `nomadim/app/cmd_enumerate.hpp`, `nomadim/app/cmd_enumerate.cpp`
- Create: `nomadim/app/cmd_convert.hpp`, `nomadim/app/cmd_convert.cpp`
- Modify: `nomadim/app/main.cpp` (replace stub)
- Create: `nomadim/data/exec_4_canonical.yaml`, `nomadim/data/poset_s3.yaml`
- Test: `nomadim/tests/test_cli.cmake` invocations via CTest (added in CMakeLists)
- Modify: `nomadim/CMakeLists.txt`

- [ ] **Step 1: Register CLI sources** in `nomadim/CMakeLists.txt`: change the
  `nomadim` target to
  `add_executable(nomadim app/main.cpp app/cmd_check.cpp app/cmd_enumerate.cpp app/cmd_convert.cpp)`.

- [ ] **Step 2: Create the data fixtures**

`nomadim/data/exec_dim2.yaml` (a single sync expands to a dim-2 poset — verified
dim2=true against the upstream oracle):
```yaml
execution:
  n_procs: 2
  syncs:
    - [0, 1]
```

`nomadim/data/exec_4_canonical.yaml` (the upstream hardcoded example; NOT dim-2):
```yaml
execution:
  n_procs: 4
  syncs:
    - [0, 1]
    - [1, 2]
    - [2, 3]
    - [0, 2]
```

`nomadim/data/poset_s3.yaml`:
```yaml
poset:
  n_vertices: 6
  edges:
    - [0, 4]
    - [0, 5]
    - [1, 3]
    - [1, 5]
    - [2, 3]
    - [2, 4]
```

- [ ] **Step 3: Write `cmd_check`** — header `nomadim/app/cmd_check.hpp`

```cpp
#ifndef NOMADIM_CMD_CHECK_HPP
#define NOMADIM_CMD_CHECK_HPP
#include <string>
namespace nomadim { int cmd_check(const std::string& path); }
#endif
```

  impl `nomadim/app/cmd_check.cpp`

```cpp
#include "cmd_check.hpp"
#include "nomadim/io.hpp"
#include "nomadim/process_graph.hpp"
#include "nomadim/dimension.hpp"
#include "nomadim/floyd.hpp"
#include <iostream>

namespace nomadim {

int cmd_check(const std::string& path) {
    Document d = load_file(path);
    adjacency_list adj;
    if (d.poset) {
        adj = d.poset->edges;
    } else {
        ProcessGraph g = ProcessGraph::build(*d.execution);
        adj = g.graph;
    }
    std::vector<int> m = make_graph_matrix(adj);
    int n = (int)adj.size();
    floyd(m.data(), n);
    auto cps = find_critical_pairs(m.data(), n);
    bool dim2 = check_critical_pairs_graph(adj, cps);

    std::cout << "Vertices: " << n << "\n";
    std::cout << "Critical pairs: " << cps.size() << "\n";
    for (size_t i = 0; i < cps.size(); ++i)
        std::cout << "  " << i << ": " << cps[i].x << " " << cps[i].y << "\n";
    std::cout << (dim2 ? "Dimension <= 2: YES" : "Dimension <= 2: NO") << "\n";
    return dim2 ? 0 : 2;
}

} // namespace nomadim
```

- [ ] **Step 4: Write `cmd_enumerate`** — header `nomadim/app/cmd_enumerate.hpp`

```cpp
#ifndef NOMADIM_CMD_ENUMERATE_HPP
#define NOMADIM_CMD_ENUMERATE_HPP
#include <string>
namespace nomadim {
int cmd_enumerate(int n_procs, int max_sync, unsigned threads, const std::string& out_path);
}
#endif
```

  impl `nomadim/app/cmd_enumerate.cpp`

```cpp
#include "cmd_enumerate.hpp"
#include "nomadim/enumerate.hpp"
#include "nomadim/io.hpp"
#include "nomadim/execution.hpp"
#include <iostream>
#include <fstream>

namespace nomadim {

int cmd_enumerate(int n_procs, int max_sync, unsigned threads, const std::string& out_path) {
    EnumerateResult r = enumerate(n_procs, max_sync, threads);
    std::cout << "Processes: " << n_procs << "  max syncs: " << max_sync
              << "  threads: " << threads << "\n";
    std::cout << "Non-isomorphic dim-2 synced executions: " << r.count
              << "  (isomorphic hits: " << r.isomorphic_hits << ")\n";

    if (!out_path.empty()) {
        std::ofstream o(out_path);
        if (!o) { std::cerr << "cannot open " << out_path << "\n"; return 1; }
        for (auto const& g : r.results) {
            Execution e{g.proc_num, g.syncs};
            o << dump_execution(e) << "---\n";
        }
        std::cout << "Wrote " << r.results.size() << " executions to " << out_path << "\n";
    }
    return 0;
}

} // namespace nomadim
```

- [ ] **Step 5: Write `cmd_convert`** — header `nomadim/app/cmd_convert.hpp`

```cpp
#ifndef NOMADIM_CMD_CONVERT_HPP
#define NOMADIM_CMD_CONVERT_HPP
#include <string>
namespace nomadim { int cmd_convert(const std::string& in, const std::string& out); }
#endif
```

  impl `nomadim/app/cmd_convert.cpp`

```cpp
#include "cmd_convert.hpp"
#include "nomadim/io.hpp"
#include "nomadim/process_graph.hpp"
#include "nomadim/poset.hpp"
#include <iostream>

namespace nomadim {

int cmd_convert(const std::string& in, const std::string& out) {
    Document d = load_file(in);
    if (!d.execution) {
        std::cerr << "convert expects an 'execution' document\n";
        return 1;
    }
    ProcessGraph g = ProcessGraph::build(*d.execution);
    Poset p = Poset::from(g);
    save_file(out, dump_poset(p));
    std::cout << "Wrote expanded poset (" << p.n_vertices << " vertices) to " << out << "\n";
    return 0;
}

} // namespace nomadim
```

- [ ] **Step 6: Replace `nomadim/app/main.cpp`**

```cpp
#include "cmd_check.hpp"
#include "cmd_enumerate.hpp"
#include "cmd_convert.hpp"
#include "nomadim/types.hpp"
#include <CLI/CLI.hpp>
#include <thread>
#include <iostream>

int main(int argc, char** argv) {
    CLI::App app{"nomadim: poset dimension-2 tooling"};
    app.set_version_flag("--version", std::string(nomadim::version()));
    app.require_subcommand(1);

    std::string check_path;
    auto* check = app.add_subcommand("check", "Report whether a poset/execution has dimension <= 2");
    check->add_option("file", check_path, "YAML poset/execution file")->required();

    int n_procs = 0, max_sync = -1;
    unsigned threads = std::thread::hardware_concurrency();
    std::string enum_out;
    auto* en = app.add_subcommand("enumerate", "Enumerate non-isomorphic dim-2 executions");
    en->add_option("-n,--procs", n_procs, "Number of processes")->required();
    en->add_option("-k,--max-sync", max_sync, "Max synchronizations (default: 2*n_procs)");
    en->add_option("-j,--threads", threads, "Worker threads (>=1)")->check(CLI::PositiveNumber);
    en->add_option("-o,--out", enum_out, "Write found executions to this YAML file");

    std::string conv_in, conv_out;
    auto* conv = app.add_subcommand("convert", "Expand an execution into a poset document");
    conv->add_option("input", conv_in, "Input execution YAML")->required();
    conv->add_option("output", conv_out, "Output poset YAML")->required();

    CLI11_PARSE(app, argc, argv);

    try {
        if (*check)  return nomadim::cmd_check(check_path);
        if (*en) {
            if (max_sync < 0) max_sync = 2 * n_procs;
            return nomadim::cmd_enumerate(n_procs, max_sync, threads, enum_out);
        }
        if (*conv)   return nomadim::cmd_convert(conv_in, conv_out);
    } catch (const std::exception& e) {
        std::cerr << "error: " << e.what() << "\n";
        return 1;
    }
    return 0;
}
```

- [ ] **Step 7: Add CTest end-to-end checks** — append to `nomadim/CMakeLists.txt`:

```cmake
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
```

- [ ] **Step 8: Build and run all tests**

Run: `cmake --build nomadim/build -j && ctest --test-dir nomadim/build --output-on-failure`
Expected: all unit tests plus `cli_check_dim2`, `cli_check_not_dim2`,
`cli_enumerate_4_5` PASS.

- [ ] **Step 9: Manual smoke of the CLI**

Run:
```bash
./nomadim/build/nomadim check nomadim/data/exec_dim2.yaml          # YES
./nomadim/build/nomadim check nomadim/data/exec_4_canonical.yaml   # NO
./nomadim/build/nomadim convert nomadim/data/exec_4_canonical.yaml /tmp/poset.yaml && cat /tmp/poset.yaml
./nomadim/build/nomadim enumerate -n 4 -k 5 -j 2
```
Expected: YES then NO verdicts; a poset YAML with 16 vertices; count line `... : 10`.

- [ ] **Step 10: Commit**

```bash
git add nomadim/CMakeLists.txt nomadim/app nomadim/data
git commit -m "feat(nomadim): CLI (check/enumerate/convert) + end-to-end tests"
```

---

## Task 10: README and repo integration notes

**Files:**
- Create: `nomadim/README.md`
- Modify: `CLAUDE.md` (note the separate C++ build)

- [ ] **Step 1: Write `nomadim/README.md`**

````markdown
# nomadim

C++ port of the NomaDimension poset dimension-2 tooling: a `libnomadim` core plus
a `nomadim` CLI that reads/writes posets as YAML, checks whether a poset has
order dimension ≤ 2, and enumerates non-isomorphic dimension-2 executions of
*N* processes.

This project builds with CMake and is **independent of the repository's Coq/dune
build**.

## Prerequisites

Boost's compiled `fiber` and `context` libraries (the enumerator is multithreaded
and multifibered):

```bash
brew install boost cmake                                   # macOS
sudo apt-get install libboost-fiber-dev libboost-context-dev cmake  # Debian/Ubuntu
```

yaml-cpp, CLI11, and GoogleTest are fetched automatically by CMake.

## Build & test

```bash
cmake -S nomadim -B nomadim/build -DCMAKE_BUILD_TYPE=Release
cmake --build nomadim/build -j
ctest --test-dir nomadim/build --output-on-failure
```

Heavy golden-count enumerations are off by default; enable with
`-DNOMADIM_SLOW_TESTS=ON`.

## Usage

```bash
nomadim check poset.yaml              # report dim<=2 + critical pairs
nomadim enumerate -n 4 -k 5 [-j 8] [-o out.yaml]
nomadim convert exec.yaml poset.yaml  # expand an execution into a poset
```

## File format (YAML)

Execution document:
```yaml
execution:
  n_procs: 4
  syncs: [[0,1],[1,2],[2,3],[0,2]]
```

General poset document (edge `[u,v]` means `u` below `v`):
```yaml
poset:
  n_vertices: 5
  edges: [[0,2],[1,2],[2,4]]
```
````

- [ ] **Step 2: Add a build note to `CLAUDE.md`** — under the "Build commands"
  section, add this paragraph:

```markdown
### C++ subproject (`nomadim/`)

The `nomadim/` directory is a standalone CMake C++ project (the NomaDimension
port) and is **not** part of the Coq/dune build — the `timed-build.sh` wrapper
does not apply. Build it with `cmake -S nomadim -B nomadim/build && cmake --build
nomadim/build -j` and test with `ctest --test-dir nomadim/build`. It requires
Boost (fiber, context); see `nomadim/README.md`.
```

- [ ] **Step 3: Final whole-suite verification**

Run: `ctest --test-dir nomadim/build --output-on-failure`
Expected: 100% tests passed.

- [ ] **Step 4: Commit**

```bash
git add nomadim/README.md CLAUDE.md
git commit -m "docs(nomadim): README + repo build-integration note"
```

---

## Self-Review Notes

- **Spec coverage:** check (Task 9), enumerate-by-N (Task 7+9), YAML both-schema
  read/write (Task 8), single multi-command binary (Task 9), `--threads`
  (Task 7+9), GoogleTest + golden tiers (Task 7), top-level `nomadim/` + FetchContent
  + Boost (Task 0), validation/error handling (Tasks 1/5/8), convert (Task 9). All
  spec sections map to a task.
- **Dropped per spec:** grouped + flat-grid generators, `common.cpp` sandbox — no
  tasks, intentionally.
- **Type consistency:** `enumerate(int,int,unsigned)`, `EnumerateResult{count,
  isomorphic_hits,results}`, `is_dim2(adjacency_list)`, `ProcessGraph::build`,
  `Poset::from`, `parse_document`/`dump_execution`/`dump_poset`,
  `is_full_synchronized` — all referenced consistently across tasks.
- **Known faithful-port limitation:** `proc_sync_name` encodes sync indices as
  single `char + '0'`, so it is only reliable for small sync counts (well within
  the golden N/K range); preserved from upstream deliberately.
