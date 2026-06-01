# nomadim Comprehensive Unit Tests Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add direct unit tests for every public function of `libnomadim` (plus file I/O and the `compare.py` gate), and remove one dead private method, so each function is verified independently.

**Architecture:** Extend the existing per-module `tests/test_*.cpp` GoogleTest files with focused, deterministic tests; pin dimension/enumeration expected values to the upstream-oracle-verified numbers; add a stdlib `unittest` test for `bench/compare.py` wired into CTest.

**Tech Stack:** C++17, GoogleTest, CMake/CTest, Python 3 (stdlib unittest).

---

## Conventions for every task

- Build & run a single suite with: `cmake --build nomadim/build -j && ctest --test-dir nomadim/build --output-on-failure -R <Suite>`.
- Tests are appended to the existing file; keep existing tests intact.
- `Label` has no `operator==`; compare `.proc` and `.num` fields individually.
- No AI watermarks / `Co-Authored-By`. Do not switch branches. Do not commit `nomadim/build*/`.

---

## Task 1: Remove dead `add_vertex_to_proc`

**Files:**
- Modify: `nomadim/include/nomadim/process_graph.hpp`
- Modify: `nomadim/src/process_graph.cpp`

- [ ] **Step 1: Remove the declaration** — in `process_graph.hpp`, delete the `private:` member declaration block:

```cpp
private:
    int add_vertex_to_proc(int proc);
```
(Delete those two lines and the now-empty `private:` label. The class then ends after `static ProcessGraph build(const Execution& e);` followed by `};`.)

- [ ] **Step 2: Remove the definition** — in `src/process_graph.cpp`, delete the entire `int ProcessGraph::add_vertex_to_proc(int proc) { ... }` function (from its signature through its closing brace).

- [ ] **Step 3: Build and run the full suite**

Run: `cmake --build nomadim/build -j && ctest --test-dir nomadim/build --output-on-failure`
Expected: builds with no errors; `100% tests passed` (38 tests).

- [ ] **Step 4: Commit**

```bash
git add nomadim/include/nomadim/process_graph.hpp nomadim/src/process_graph.cpp
git commit -m "refactor(nomadim): remove unused private add_vertex_to_proc"
```

---

## Task 2: floyd tests

**Files:**
- Modify: `nomadim/tests/test_floyd.cpp`

- [ ] **Step 1: Append the tests** to `nomadim/tests/test_floyd.cpp` (after the existing `TEST`):

```cpp
TEST(Floyd, MakeGraphMatrixLayout) {
    // chain 0 -> 1 -> 2
    adjacency_list g = {{1}, {2}, {}};
    std::vector<int> m = make_graph_matrix(g);
    ASSERT_EQ(m.size(), 9u);
    EXPECT_EQ(m[0*3 + 0], 0);    // diagonal
    EXPECT_EQ(m[1*3 + 1], 0);
    EXPECT_EQ(m[0*3 + 1], 1);    // edge 0->1
    EXPECT_EQ(m[1*3 + 2], 1);    // edge 1->2
    EXPECT_EQ(m[0*3 + 2], INF);  // no direct edge 0->2
    EXPECT_EQ(m[1*3 + 0], INF);  // no edge 1->0
}

TEST(Floyd, DisconnectedStaysInf) {
    adjacency_list g = {{1}, {0}, {3}, {2}};  // {0,1} and {2,3} separate
    std::vector<int> m = make_graph_matrix(g);
    floyd(m.data(), 4);
    EXPECT_EQ(m[0*4 + 1], 1);
    EXPECT_EQ(m[0*4 + 2], INF);  // no path between components
    EXPECT_EQ(m[2*4 + 0], INF);
}

TEST(Floyd, DiamondTakesShortestPath) {
    // 0->1, 0->2, 1->3, 2->3 : 0 reaches 3 in 2 steps
    adjacency_list g = {{1, 2}, {3}, {3}, {}};
    std::vector<int> m = make_graph_matrix(g);
    floyd(m.data(), 4);
    EXPECT_EQ(m[0*4 + 3], 2);
    EXPECT_EQ(m[3*4 + 0], INF);
}

TEST(Floyd, SingleVertex) {
    adjacency_list g = {{}};
    std::vector<int> m = make_graph_matrix(g);
    floyd(m.data(), 1);
    EXPECT_EQ(m[0], 0);
}

TEST(Floyd, AdvanceVertexRelaxesOnlyThroughThatVertex) {
    // edges 0->1, 1->2, NOT closed (0->2 == INF until we relax through 1)
    adjacency_list g = {{1}, {2}, {}};
    std::vector<int> m = make_graph_matrix(g);
    EXPECT_EQ(m[0*3 + 2], INF);
    floyd_advance_vertex(m.data(), 3, 1);   // relax paths through vertex 1
    EXPECT_EQ(m[0*3 + 2], 2);                // 0->1->2 discovered
    // a longer chain: advancing through 1 must NOT close 0->3
    adjacency_list g2 = {{1}, {2}, {3}, {}};
    std::vector<int> m2 = make_graph_matrix(g2);
    floyd_advance_vertex(m2.data(), 4, 1);
    EXPECT_EQ(m2[0*4 + 2], 2);    // through vertex 1
    EXPECT_EQ(m2[0*4 + 3], INF);  // not through vertex 1 alone
}
```

- [ ] **Step 2: Build and run**

Run: `cmake --build nomadim/build -j && ctest --test-dir nomadim/build --output-on-failure -R Floyd`
Expected: all Floyd tests PASS (6 total).

- [ ] **Step 3: Commit**

```bash
git add nomadim/tests/test_floyd.cpp
git commit -m "test(nomadim): cover make_graph_matrix and floyd_advance_vertex"
```

---

## Task 3: process_graph bookkeeping tests

**Files:**
- Modify: `nomadim/tests/test_process_graph.cpp`

- [ ] **Step 1: Append the tests** to `nomadim/tests/test_process_graph.cpp`:

```cpp
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
    // vertices: 0,1 initial; 2 meet; 3,4 successors
    ASSERT_EQ((int)g.graph.size(), 5);
    EXPECT_EQ(g.graph[0], (std::vector<int>{2}));
    EXPECT_EQ(g.graph[1], (std::vector<int>{2}));
    EXPECT_EQ(g.graph[2], (std::vector<int>{3, 4}));  // meet -> two successors
    EXPECT_TRUE(g.graph[3].empty());
    EXPECT_TRUE(g.graph[4].empty());
    EXPECT_EQ(g.proc_last_vertex, (std::vector<int>{3, 4}));
    EXPECT_EQ(g.proc_verteces[0], (std::vector<int>{0, 3}));
    EXPECT_EQ(g.proc_verteces[1], (std::vector<int>{1, 4}));
    EXPECT_EQ(g.labels[2].proc, -1); EXPECT_EQ(g.labels[2].num, -1);  // meet vertex
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
```

- [ ] **Step 2: Build and run**

Run: `cmake --build nomadim/build -j && ctest --test-dir nomadim/build --output-on-failure -R ProcessGraph`
Expected: all ProcessGraph tests PASS (6 total).

- [ ] **Step 3: Commit**

```bash
git add nomadim/tests/test_process_graph.cpp
git commit -m "test(nomadim): verify ProcessGraph labels/network/sync-name bookkeeping"
```

---

## Task 4: dimension tests (helpers + critical-pair internals)

**Files:**
- Modify: `nomadim/tests/test_dimension.cpp`

- [ ] **Step 1: Add the floyd include** — at the top of `nomadim/tests/test_dimension.cpp`, after the existing includes add:

```cpp
#include "nomadim/floyd.hpp"
```

- [ ] **Step 2: Append the tests**:

```cpp
TEST(Dimension, HaveCycleEdgeCases) {
    EXPECT_FALSE(have_cycle(adjacency_list{}));         // empty graph
    EXPECT_FALSE(have_cycle(adjacency_list{{}}));        // single node, no edge
    EXPECT_TRUE(have_cycle(adjacency_list{{0}}));        // self-loop
    EXPECT_TRUE(have_cycle(adjacency_list{{1},{0}}));    // 2-cycle
    EXPECT_FALSE(have_cycle(adjacency_list{{1},{2},{}})); // DAG chain
}

TEST(Dimension, IsBipartiteEdgeCases) {
    EXPECT_TRUE(is_bipartite(adjacency_list{}));         // empty
    EXPECT_TRUE(is_bipartite(adjacency_list{{}}));        // single node
    // even cycle C4 (undirected, symmetric adjacency): bipartite
    EXPECT_TRUE(is_bipartite(adjacency_list{{1,3},{0,2},{1,3},{0,2}}));
    // triangle: not bipartite
    EXPECT_FALSE(is_bipartite(adjacency_list{{1,2},{0,2},{0,1}}));
}

TEST(Dimension, CheckIfCriticalOnSmallPoset) {
    // poset: edge 1->2, vertex 0 isolated. Closed matrix required.
    adjacency_list g = {{}, {2}, {}};
    std::vector<int> m = make_graph_matrix(g);
    floyd(m.data(), 3);
    // forcing 0->1 also makes 0->2 comparable => NOT critical
    EXPECT_FALSE(check_if_critical(m.data(), 3, 0, 1));
    // forcing 1->0 collapses no other incomparable pair => critical
    EXPECT_TRUE(check_if_critical(m.data(), 3, 1, 0));
}

TEST(Dimension, FindCriticalPairsCounts) {
    // canonical execution -> 25 (oracle-verified)
    {
        ProcessGraph g = ProcessGraph::build(Execution{4, {{0,1},{1,2},{2,3},{0,2}}});
        std::vector<int> m = make_graph_matrix(g.graph);
        EXPECT_EQ(find_critical_pairs(m.data(), (int)g.graph.size()).size(), 25u);
    }
    // S_3 -> 3
    {
        adjacency_list s3(6); s3[0] = {4,5}; s3[1] = {3,5}; s3[2] = {3,4};
        std::vector<int> m = make_graph_matrix(s3);
        EXPECT_EQ(find_critical_pairs(m.data(), 6).size(), 3u);
    }
    // chain of 4 -> 0 (no incomparable pairs)
    {
        adjacency_list chain = {{1},{2},{3},{}};
        std::vector<int> m = make_graph_matrix(chain);
        EXPECT_EQ(find_critical_pairs(m.data(), 4).size(), 0u);
    }
    // antichain of 3 -> 6 (all ordered incomparable pairs are critical)
    {
        adjacency_list a3(3);
        std::vector<int> m = make_graph_matrix(a3);
        EXPECT_EQ(find_critical_pairs(m.data(), 3).size(), 6u);
    }
}

TEST(Dimension, CheckCriticalPairsGraphBipartiteness) {
    // antichain of 3: critical-pair incompatibility graph is bipartite => dim 2
    adjacency_list a3(3);
    std::vector<int> m = make_graph_matrix(a3);
    auto cps = find_critical_pairs(m.data(), 3);
    EXPECT_TRUE(check_critical_pairs_graph(a3, cps));
    // S_3: not bipartite => not dim 2
    adjacency_list s3(6); s3[0] = {4,5}; s3[1] = {3,5}; s3[2] = {3,4};
    std::vector<int> ms = make_graph_matrix(s3);
    auto cps3 = find_critical_pairs(ms.data(), 6);
    EXPECT_FALSE(check_critical_pairs_graph(s3, cps3));
}
```

- [ ] **Step 3: Build and run**

Run: `cmake --build nomadim/build -j && ctest --test-dir nomadim/build --output-on-failure -R Dimension`
Expected: all Dimension tests PASS (10 total). The counts 25/3/0/6 must match exactly; if they do not, STOP — do not change the expected numbers (they are oracle-verified), report the discrepancy.

- [ ] **Step 4: Commit**

```bash
git add nomadim/tests/test_dimension.cpp
git commit -m "test(nomadim): cover have_cycle/is_bipartite/check_if_critical/find_critical_pairs"
```

---

## Task 5: isomorphism tests

**Files:**
- Modify: `nomadim/tests/test_isomorphism.cpp`

- [ ] **Step 1: Append the tests**:

```cpp
TEST(Isomorphism, CanonicalSyncNamePermutationInvariant) {
    // a single sync on different process pairs is the same up to relabeling
    ProcessGraph a = ProcessGraph::build(Execution{4, {{0,1}}});
    ProcessGraph b = ProcessGraph::build(Execution{4, {{2,3}}});
    EXPECT_EQ(canonical_sync_name(a), canonical_sync_name(b));
}

TEST(Isomorphism, CanonicalSyncNameSortedAndDistinguishes) {
    ProcessGraph a = ProcessGraph::build(Execution{4, {{0,1}}});
    auto key = canonical_sync_name(a);
    EXPECT_TRUE(std::is_sorted(key.begin(), key.end()));
    // path vs star differ
    ProcessGraph path = ProcessGraph::build(Execution{4, {{0,1},{1,2},{2,3}}});
    ProcessGraph star = ProcessGraph::build(Execution{4, {{0,1},{0,2},{0,3}}});
    EXPECT_NE(canonical_sync_name(path), canonical_sync_name(star));
}

TEST(Isomorphism, GenerateAllIsomorphicCardinalityN4) {
    ProcessGraph a = ProcessGraph::build(Execution{4, {{0,1}}});
    EXPECT_EQ(generate_all_isomorphic(a).size(), 24u);  // 4!
}

TEST(Isomorphism, NotIsomorphicWhenShapeDiffers) {
    ProcessGraph a = ProcessGraph::build(Execution{3, {{0,1}}});
    ProcessGraph diff_procs = ProcessGraph::build(Execution{4, {{0,1}}});
    EXPECT_FALSE(is_isomorphic(a, diff_procs));          // different proc_num
    ProcessGraph more_syncs = ProcessGraph::build(Execution{3, {{0,1},{1,2}}});
    EXPECT_FALSE(is_isomorphic(a, more_syncs));          // different graph size
    EXPECT_TRUE(is_isomorphic(a, a));                    // reflexive
}
```

- [ ] **Step 2: Add the `<algorithm>` include** (for `std::is_sorted`) at the top of `nomadim/tests/test_isomorphism.cpp` if not already present:

```cpp
#include <algorithm>
```

- [ ] **Step 3: Build and run**

Run: `cmake --build nomadim/build -j && ctest --test-dir nomadim/build --output-on-failure -R Isomorphism`
Expected: all Isomorphism tests PASS (7 total).

- [ ] **Step 4: Commit**

```bash
git add nomadim/tests/test_isomorphism.cpp
git commit -m "test(nomadim): cover canonical_sync_name and is_isomorphic edge cases"
```

---

## Task 6: enumerate tests (is_full_synchronized + invariants)

**Files:**
- Modify: `nomadim/tests/test_enumerate.cpp`

- [ ] **Step 1: Add includes** — at the top of `nomadim/tests/test_enumerate.cpp`, after the existing includes add:

```cpp
#include "nomadim/process_graph.hpp"
#include "nomadim/execution.hpp"
```

- [ ] **Step 2: Append the tests**:

```cpp
TEST(Enumerate, IsFullSynchronized) {
    // one sync between the only two processes fully synchronizes them
    ProcessGraph synced = ProcessGraph::build(Execution{2, {{0,1}}});
    EXPECT_TRUE(is_full_synchronized(synced));
    // processes 2 and 3 never sync with 0,1 => not fully synchronized
    ProcessGraph partial = ProcessGraph::build(Execution{4, {{0,1}}});
    EXPECT_FALSE(is_full_synchronized(partial));
}

TEST(Enumerate, ResultInvariants) {
    EnumerateResult r = enumerate(3, 5, 1);
    EXPECT_EQ(r.count, 12);                          // golden
    EXPECT_EQ((int)r.results.size(), r.count);       // representatives match count
    EXPECT_GE(r.isomorphic_hits, 0);
}

TEST(Enumerate, SmallExactCount) {
    EXPECT_EQ(enumerate(2, 1, 1).count, 1);
}

TEST(Enumerate, ThreadInvarianceSecondConfig) {
    EXPECT_EQ(enumerate(3, 5, 1).count, enumerate(3, 5, 4).count);
}
```

- [ ] **Step 3: Build and run**

Run: `cmake --build nomadim/build -j && ctest --test-dir nomadim/build --output-on-failure -R Enumerate`
Expected: all Enumerate default-tier tests PASS (the new ones + existing `GoldenCountsDefaultTier`, `ThreadCountDoesNotChangeResult`).

- [ ] **Step 4: Commit**

```bash
git add nomadim/tests/test_enumerate.cpp
git commit -m "test(nomadim): cover is_full_synchronized and enumerate invariants"
```

---

## Task 7: execution + poset tests

**Files:**
- Modify: `nomadim/tests/test_execution.cpp`
- Modify: `nomadim/tests/test_poset.cpp`

- [ ] **Step 1: Append to `nomadim/tests/test_execution.cpp`**:

```cpp
TEST(Execution, EmptySyncsValid) {
    Execution e{3, {}};
    EXPECT_NO_THROW(e.validate());
}

TEST(Execution, RejectsNegativeEndpoint) {
    Execution e{2, {{-1, 0}}};
    EXPECT_THROW(e.validate(), std::invalid_argument);
}
```

- [ ] **Step 2: Append to `nomadim/tests/test_poset.cpp`**:

```cpp
TEST(Poset, EmptyPosetValid) {
    Poset p{0, {}};
    EXPECT_NO_THROW(p.validate());
}

TEST(Poset, RejectsEdgesSizeMismatch) {
    Poset p{2, {{}}};   // edges.size() (1) != n_vertices (2)
    EXPECT_THROW(p.validate(), std::invalid_argument);
}

TEST(Poset, RejectsSelfLoopEdge) {
    Poset p{1, {{0}}};  // edge 0->0 is a 1-cycle
    EXPECT_THROW(p.validate(), std::invalid_argument);
}

TEST(Poset, FromProcessGraphCopiesGraph) {
    ProcessGraph g = ProcessGraph::build(Execution{4, {{0,1},{1,2},{2,3},{0,2}}});
    Poset p = Poset::from(g);
    EXPECT_EQ(p.n_vertices, (int)g.graph.size());
    EXPECT_EQ(p.edges, g.graph);
    EXPECT_NO_THROW(p.validate());
}
```

- [ ] **Step 3: Build and run**

Run: `cmake --build nomadim/build -j && ctest --test-dir nomadim/build --output-on-failure -R "Execution|Poset"`
Expected: all Execution (6) and Poset (7) tests PASS.

- [ ] **Step 4: Commit**

```bash
git add nomadim/tests/test_execution.cpp nomadim/tests/test_poset.cpp
git commit -m "test(nomadim): cover Execution/Poset edge cases and Poset::from"
```

---

## Task 8: io file round-trip tests

**Files:**
- Modify: `nomadim/tests/test_io.cpp`

- [ ] **Step 1: Add the `<filesystem>` include** at the top of `nomadim/tests/test_io.cpp`:

```cpp
#include <filesystem>
```

- [ ] **Step 2: Append the tests**:

```cpp
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
```

- [ ] **Step 3: Build and run**

Run: `cmake --build nomadim/build -j && ctest --test-dir nomadim/build --output-on-failure -R Io`
Expected: all Io tests PASS (15 total).

- [ ] **Step 4: Commit**

```bash
git add nomadim/tests/test_io.cpp
git commit -m "test(nomadim): file round-trip and nonexistent-file handling for io"
```

---

## Task 9: compare.py tests + CTest wiring

**Files:**
- Create: `nomadim/tests/test_compare.py`
- Modify: `nomadim/CMakeLists.txt`

- [ ] **Step 1: Write the test** — `nomadim/tests/test_compare.py`

```python
import json
import os
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

COMPARE = Path(__file__).resolve().parent.parent / "bench" / "compare.py"


def write_json(path, medians):
    """medians: dict name -> real_time. Writes a minimal Google Benchmark JSON."""
    data = {"benchmarks": [
        {"run_name": name, "aggregate_name": "median", "real_time": rt}
        for name, rt in medians.items()
    ]}
    with open(path, "w") as f:
        json.dump(data, f)


def run_compare(baseline, current, *extra):
    return subprocess.run(
        [sys.executable, str(COMPARE), baseline, current, *extra],
        capture_output=True, text=True)


class CompareTest(unittest.TestCase):
    def setUp(self):
        self.dir = tempfile.mkdtemp()
        self.base = os.path.join(self.dir, "base.json")
        self.cur = os.path.join(self.dir, "cur.json")

    def test_identical_passes(self):
        write_json(self.base, {"a": 100.0, "b": 200.0})
        write_json(self.cur, {"a": 100.0, "b": 200.0})
        r = run_compare(self.base, self.cur)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("OK", r.stdout)

    def test_regression_fails(self):
        write_json(self.base, {"a": 100.0})
        write_json(self.cur, {"a": 200.0})  # 2x slower
        r = run_compare(self.base, self.cur)
        self.assertEqual(r.returncode, 1)
        self.assertIn("REGRESSION", r.stdout)

    def test_within_threshold_passes(self):
        write_json(self.base, {"a": 100.0})
        write_json(self.cur, {"a": 110.0})  # +10%, under default 25%
        r = run_compare(self.base, self.cur)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)

    def test_missing_benchmark_fails(self):
        write_json(self.base, {"a": 100.0, "b": 200.0})
        write_json(self.cur, {"a": 100.0})  # b missing from current
        r = run_compare(self.base, self.cur)
        self.assertEqual(r.returncode, 1)
        self.assertIn("MISSING", r.stdout)


if __name__ == "__main__":
    unittest.main()
```

- [ ] **Step 2: Wire it into CTest** — append to `nomadim/CMakeLists.txt`:

```cmake
# ---- compare.py regression-gate tests ----
find_package(Python3 COMPONENTS Interpreter)
if(Python3_Interpreter_FOUND)
  add_test(NAME compare_py
    COMMAND ${Python3_EXECUTABLE} -m unittest discover
            -s ${CMAKE_CURRENT_SOURCE_DIR}/tests -p "test_compare.py")
endif()
```

- [ ] **Step 3: Verify the Python test standalone first**

Run: `python3 -m unittest discover -s nomadim/tests -p "test_compare.py" -v`
Expected: 4 tests, all OK.

- [ ] **Step 4: Reconfigure (to register the new CTest) and run it**

Run:
```bash
cmake -S nomadim -B nomadim/build -DCMAKE_BUILD_TYPE=Release
ctest --test-dir nomadim/build --output-on-failure -R compare_py
```
Expected: `compare_py` test PASSES.

- [ ] **Step 5: Commit**

```bash
git add nomadim/tests/test_compare.py nomadim/CMakeLists.txt
git commit -m "test(nomadim): unit tests for compare.py regression gate (via CTest)"
```

---

## Task 10: Final whole-suite verification

**Files:** none (verification only)

- [ ] **Step 1: Full configure + build + test**

Run:
```bash
cmake -S nomadim -B nomadim/build -DCMAKE_BUILD_TYPE=Release
cmake --build nomadim/build -j
ctest --test-dir nomadim/build --output-on-failure
```
Expected: `100% tests passed` with the new total (38 prior + ~25 new C++ tests + `compare_py` ≈ 64 tests; the exact number is whatever the suite reports, with **0 failures**).

- [ ] **Step 2: (no commit — verification only)** If anything fails, fix the offending test in its own task before declaring done.

---

## Self-Review Notes

- **Spec coverage:** floyd incl. `floyd_advance_vertex` (T2); ProcessGraph bookkeeping + `build` (T3); `have_cycle`/`is_bipartite`/`check_if_critical`/`find_critical_pairs`/`check_critical_pairs_graph` (T4); `canonical_sync_name`/`generate_all_isomorphic`/`is_isomorphic` (T5); `is_full_synchronized` + enumerate invariants (T6); Execution/Poset edge cases + `Poset::from` (T7); `load_file`/`save_file` round-trip + nonexistent (T8); `compare.py` 4 cases wired into CTest (T9); dead `add_vertex_to_proc` removed (T1). All spec sections mapped.
- **Placeholder scan:** none — every test step has complete code; every command has an expected result.
- **Value/type consistency:** pinned counts (canonical=25, S₃=3, chain=0, antichain-3=6; enumerate 12/1) verified against the library/oracle; `check_if_critical(m,3,1,0)=true`, `(m,3,0,1)=false` verified empirically; APIs (`make_graph_matrix`, `floyd`, `floyd_advance_vertex`, `find_critical_pairs(int*,int)`, `check_if_critical(const int*,int,int,int)`, `canonical_sync_name`, `is_full_synchronized`, `Poset::from`, `load_file`/`save_file`/`dump_*`) match the headers. `Label` compared field-wise (no `operator==`). `std::vector` and `std::pair` have `operator==`; `EnumerateResult.count` is `int` so `results.size()` is cast to `int` for comparison.
