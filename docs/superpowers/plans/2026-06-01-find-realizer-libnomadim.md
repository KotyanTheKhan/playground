# find_realizer in libnomadim — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a first-class `find_realizer()` algorithm to libnomadim that returns a 2-realizer (two linear extensions whose intersection is exactly the partial order) for any poset of order dimension ≤ 2, or reports dimension > 2 — covered by exhaustive tests.

**Architecture:** New, self-contained translation unit (`include/nomadim/realizer.hpp` + `src/realizer.cpp`), independent of `dimension.cpp` (which is left untouched, preserving the golden enumeration counts). The algorithm is a backtracking search for a transitive orientation of the incomparability graph: it maintains two transitively-closed strict relations R₁ (seeded from the poset) and R₂, orients each incomparable pair oppositely in the two relations, and rejects any branch that creates a cycle. When all pairs are oriented, R₁ and R₂ are complementary total orders, so R₁ ∩ R₂ = P by construction. Correctness is re-verified at runtime by the tests (`l1 ∩ l2 == P`, both are linear extensions) and cross-checked against `is_dim2` over all small DAGs.

**Tech Stack:** C++17, CMake (existing `nomadim/CMakeLists.txt`), GoogleTest, mise (`mise run nomadim-test`). This is the nomadim C++ subproject — the Coq `timed-build.sh` wrapper does **not** apply.

**Branch:** `nomadim-editor` (already created off `dev`; this plan is phase 1 of the editor spec).

---

## File structure

| File | Responsibility |
|------|----------------|
| `nomadim/include/nomadim/realizer.hpp` | Public API: `struct Realizer` + `find_realizer()`. |
| `nomadim/src/realizer.cpp` | The backtracking transitive-orientation algorithm + helpers (internal linkage). |
| `nomadim/tests/test_realizer.cpp` | Exhaustive GoogleTest suite + a reusable `expect_valid_realizer` verifier. |
| `nomadim/CMakeLists.txt` | Add `src/realizer.cpp` to `nomadim_core`; add `tests/test_realizer.cpp` to `nomadim_tests`. |
| `docs/INDEX.md` | Document the new algorithm under the nomadim section. |

---

### Task 1: Scaffold the API, build wiring, and a failing test (RED)

**Files:**
- Create: `nomadim/include/nomadim/realizer.hpp`
- Create: `nomadim/src/realizer.cpp`
- Create: `nomadim/tests/test_realizer.cpp`
- Modify: `nomadim/CMakeLists.txt:42` (add source) and `nomadim/CMakeLists.txt:56` (add test)

- [ ] **Step 1: Write the header**

Create `nomadim/include/nomadim/realizer.hpp`:

```cpp
#ifndef NOMADIM_REALIZER_HPP
#define NOMADIM_REALIZER_HPP

#include "nomadim/types.hpp"
#include <vector>

namespace nomadim {

// A 2-realizer of a poset: two linear extensions whose intersection is exactly
// the partial order. When the poset has order dimension > 2, dim_le_2 is false
// and l1/l2 are empty.
struct Realizer {
    bool dim_le_2 = false;
    std::vector<int> l1;   // permutation of 0..n-1, least element first
    std::vector<int> l2;
};

// Find a 2-realizer of the poset whose order is the reachability closure of the
// adjacency list `g` (edge u->v means u < v). Precondition: `g` is acyclic
// (callers validate with Poset::validate first).
Realizer find_realizer(const adjacency_list& g);

} // namespace nomadim

#endif // NOMADIM_REALIZER_HPP
```

- [ ] **Step 2: Write a stub implementation**

Create `nomadim/src/realizer.cpp` (deliberately wrong so the test fails first):

```cpp
#include "nomadim/realizer.hpp"

namespace nomadim {

Realizer find_realizer(const adjacency_list& /*g*/) {
    return Realizer{false, {}, {}};   // stub — replaced in Task 2
}

} // namespace nomadim
```

- [ ] **Step 3: Wire both files into CMake**

In `nomadim/CMakeLists.txt`, add `src/realizer.cpp` to the `nomadim_core` source list (the `add_library(nomadim_core ...)` block, after `src/poset.cpp`):

```cmake
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
```

And add `tests/test_realizer.cpp` to the `nomadim_tests` source list (the `add_executable(nomadim_tests ...)` line):

```cmake
add_executable(nomadim_tests tests/test_smoke.cpp tests/test_execution.cpp tests/test_process_graph.cpp tests/test_floyd.cpp tests/test_dimension.cpp tests/test_realizer.cpp tests/test_poset.cpp tests/test_isomorphism.cpp tests/test_enumerate.cpp tests/test_io.cpp)
```

- [ ] **Step 4: Write the test file with the verifier helper and the first test**

Create `nomadim/tests/test_realizer.cpp`:

```cpp
#include <gtest/gtest.h>
#include "nomadim/realizer.hpp"
#include "nomadim/dimension.hpp"
#include "nomadim/process_graph.hpp"
#include "nomadim/execution.hpp"
#include "nomadim/types.hpp"
#include <vector>

using namespace nomadim;

namespace {

// Strict reachability of g: base[a*n+b] == 1 iff a < b in the partial order.
std::vector<char> reach(const adjacency_list& g) {
    int n = (int)g.size();
    std::vector<char> r((size_t)n * n, 0);
    for (int u = 0; u < n; ++u)
        for (int v : g[u]) r[(size_t)u * n + v] = 1;
    for (int k = 0; k < n; ++k)
        for (int i = 0; i < n; ++i)
            for (int j = 0; j < n; ++j)
                if (r[(size_t)i * n + k] && r[(size_t)k * n + j])
                    r[(size_t)i * n + j] = 1;
    return r;
}

// pos[e] = index of element e in the linear order `order`.
std::vector<int> positions(const std::vector<int>& order) {
    std::vector<int> pos(order.size());
    for (int i = 0; i < (int)order.size(); ++i) pos[order[i]] = i;
    return pos;
}

// Assert r is a valid 2-realizer of g: l1/l2 are permutations, both are linear
// extensions of the partial order, and their intersection is exactly the order.
void expect_valid_realizer(const adjacency_list& g, const Realizer& r) {
    int n = (int)g.size();
    ASSERT_EQ((int)r.l1.size(), n);
    ASSERT_EQ((int)r.l2.size(), n);
    std::vector<char> seen1(n, 0), seen2(n, 0);
    for (int x : r.l1) { ASSERT_GE(x, 0); ASSERT_LT(x, n); ASSERT_FALSE(seen1[x]); seen1[x] = 1; }
    for (int x : r.l2) { ASSERT_GE(x, 0); ASSERT_LT(x, n); ASSERT_FALSE(seen2[x]); seen2[x] = 1; }
    auto base = reach(g);
    auto p1 = positions(r.l1), p2 = positions(r.l2);
    for (int a = 0; a < n; ++a)
        for (int b = 0; b < n; ++b) {
            if (a == b) continue;
            if (base[(size_t)a * n + b]) {
                EXPECT_LT(p1[a], p1[b]);   // both orders extend the partial order
                EXPECT_LT(p2[a], p2[b]);
            }
            bool in_both = (p1[a] < p1[b]) && (p2[a] < p2[b]);
            EXPECT_EQ(in_both, (bool)base[(size_t)a * n + b]);  // intersection == order
        }
}

} // namespace

// A 4-chain has dimension 1, so it has a 2-realizer (both extensions = 0<1<2<3).
TEST(Realizer, ChainHasRealizer) {
    adjacency_list chain = {{1}, {2}, {3}, {}};
    Realizer r = find_realizer(chain);
    EXPECT_TRUE(r.dim_le_2);
    expect_valid_realizer(chain, r);
}
```

- [ ] **Step 5: Configure, build, and run — expect failure**

Run: `mise run nomadim-test`
Expected: builds successfully, `Realizer.ChainHasRealizer` **FAILS** (`r.dim_le_2` is false from the stub; `expect_valid_realizer` size asserts fail). Do **not** commit.

---

### Task 2: Implement the algorithm (GREEN)

**Files:**
- Modify: `nomadim/src/realizer.cpp` (replace the stub)

- [ ] **Step 1: Replace the stub with the full implementation**

Overwrite `nomadim/src/realizer.cpp`:

```cpp
#include "nomadim/realizer.hpp"
#include <utility>
#include <vector>

namespace nomadim {
namespace {

// Dense strict partial order on n elements: lt[a*n+b] == 1 means a < b.
struct StrictRel {
    int n;
    std::vector<char> lt;
    explicit StrictRel(int n_) : n(n_), lt((size_t)n_ * n_, 0) {}
    bool less(int a, int b) const { return lt[(size_t)a * n + b] != 0; }

    // Add a<b and re-close transitively. Returns false if this creates a cycle
    // (b<a already held, or the closure forces some element below itself).
    bool add_and_close(int a, int b) {
        if (less(a, b)) return true;
        if (less(b, a)) return false;
        lt[(size_t)a * n + b] = 1;
        bool changed = true;
        while (changed) {
            changed = false;
            for (int i = 0; i < n; ++i)
                for (int j = 0; j < n; ++j) {
                    if (!lt[(size_t)i * n + j]) continue;
                    for (int k = 0; k < n; ++k)
                        if (lt[(size_t)j * n + k] && !lt[(size_t)i * n + k]) {
                            if (i == k) return false;   // i < ... < i : cycle
                            lt[(size_t)i * n + k] = 1;
                            changed = true;
                        }
                }
        }
        return true;
    }
};

// Linearize a total strict order into a permutation, least element first.
// In a total order each element has a distinct number of elements below it.
std::vector<int> linearize(const StrictRel& r) {
    int n = r.n;
    std::vector<int> below(n, 0), order(n);
    for (int a = 0; a < n; ++a)
        for (int b = 0; b < n; ++b)
            if (r.less(a, b)) below[b]++;
    for (int e = 0; e < n; ++e) order[below[e]] = e;
    return order;
}

struct Solver {
    std::vector<std::pair<int, int>> pairs;   // incomparable pairs (u < v by index)
    Realizer result;

    bool solve(int idx, StrictRel r1, StrictRel r2) {
        if (idx == (int)pairs.size()) {
            result.dim_le_2 = true;
            result.l1 = linearize(r1);
            result.l2 = linearize(r2);
            return true;
        }
        int u = pairs[idx].first, v = pairs[idx].second;
        // Branch A: u<v in L1, v<u in L2.
        {
            StrictRel a1 = r1, a2 = r2;
            if (a1.add_and_close(u, v) && a2.add_and_close(v, u) &&
                solve(idx + 1, std::move(a1), std::move(a2)))
                return true;
        }
        // Branch B: v<u in L1, u<v in L2.
        {
            StrictRel b1 = r1, b2 = r2;
            if (b1.add_and_close(v, u) && b2.add_and_close(u, v) &&
                solve(idx + 1, std::move(b1), std::move(b2)))
                return true;
        }
        return false;
    }
};

} // namespace

Realizer find_realizer(const adjacency_list& g) {
    int n = (int)g.size();
    StrictRel base(n);
    for (int u = 0; u < n; ++u)
        for (int v : g[u])
            base.add_and_close(u, v);   // seed direct edges, close to full order

    Solver s;
    for (int u = 0; u < n; ++u)
        for (int v = u + 1; v < n; ++v)
            if (!base.less(u, v) && !base.less(v, u))
                s.pairs.push_back({u, v});

    if (s.solve(0, base, base)) return s.result;
    return Realizer{false, {}, {}};
}

} // namespace nomadim
```

- [ ] **Step 2: Build and run — expect the chain test to pass**

Run: `mise run nomadim-test`
Expected: `Realizer.ChainHasRealizer` PASSES; all pre-existing tests still pass.

- [ ] **Step 3: Commit**

```bash
git add nomadim/include/nomadim/realizer.hpp nomadim/src/realizer.cpp nomadim/tests/test_realizer.cpp nomadim/CMakeLists.txt
git commit -m "feat(nomadim): add find_realizer (2-realizer via transitive orientation)"
```

---

### Task 3: Antichain, empty, and singleton tests

**Files:**
- Modify: `nomadim/tests/test_realizer.cpp` (append tests)

- [ ] **Step 1: Add the tests**

Append to `nomadim/tests/test_realizer.cpp`:

```cpp
// A 3-element antichain has dimension 2: the realizer is any order and its
// reverse, so the intersection is empty (all pairs incomparable).
TEST(Realizer, AntichainHasRealizer) {
    adjacency_list a3(3);   // no edges
    Realizer r = find_realizer(a3);
    EXPECT_TRUE(r.dim_le_2);
    expect_valid_realizer(a3, r);
}

// Degenerate sizes: the empty poset and a single element both trivially realize.
TEST(Realizer, EmptyAndSingleton) {
    Realizer r0 = find_realizer(adjacency_list{});
    EXPECT_TRUE(r0.dim_le_2);
    EXPECT_TRUE(r0.l1.empty());
    EXPECT_TRUE(r0.l2.empty());

    adjacency_list one(1);
    Realizer r1 = find_realizer(one);
    EXPECT_TRUE(r1.dim_le_2);
    expect_valid_realizer(one, r1);
}
```

- [ ] **Step 2: Build and run**

Run: `mise run nomadim-test`
Expected: `Realizer.AntichainHasRealizer` and `Realizer.EmptyAndSingleton` PASS.

- [ ] **Step 3: Commit**

```bash
git add nomadim/tests/test_realizer.cpp
git commit -m "test(nomadim): realizer for antichain, empty, and singleton posets"
```

---

### Task 4: Dimension-2 vs dimension-3 fixtures (S₃, canonical execution, single-sync, N-poset)

**Files:**
- Modify: `nomadim/tests/test_realizer.cpp` (append tests)

- [ ] **Step 1: Add the tests**

Append to `nomadim/tests/test_realizer.cpp`:

```cpp
// The standard example S_3 has order dimension 3 — no 2-realizer exists.
TEST(Realizer, StandardExampleS3HasNoRealizer) {
    adjacency_list s3(6);
    s3[0] = {4, 5}; s3[1] = {3, 5}; s3[2] = {3, 4};
    Realizer r = find_realizer(s3);
    EXPECT_FALSE(r.dim_le_2);
    EXPECT_TRUE(r.l1.empty());
    EXPECT_TRUE(r.l2.empty());
    EXPECT_EQ(r.dim_le_2, is_dim2(s3));   // agrees with the existing checker
}

// The canonical 4-process execution is NOT 2-dimensional (25 critical pairs).
TEST(Realizer, CanonicalExecutionHasNoRealizer) {
    ProcessGraph g = ProcessGraph::build(Execution{4, {{0,1},{1,2},{2,3},{0,2}}});
    Realizer r = find_realizer(g.graph);
    EXPECT_FALSE(r.dim_le_2);
    EXPECT_EQ(r.dim_le_2, is_dim2(g.graph));
}

// A single synchronization between two processes expands to a 2-dimensional poset.
TEST(Realizer, SingleSyncExecutionHasRealizer) {
    ProcessGraph g = ProcessGraph::build(Execution{2, {{0,1}}});
    Realizer r = find_realizer(g.graph);
    EXPECT_TRUE(r.dim_le_2);
    EXPECT_EQ(r.dim_le_2, is_dim2(g.graph));
    expect_valid_realizer(g.graph, r);
}

// The "N" poset (0<2, 1<2, 1<3) has dimension 2.
TEST(Realizer, NPosetHasRealizer) {
    adjacency_list n_poset = {{2}, {2, 3}, {}, {}};
    Realizer r = find_realizer(n_poset);
    EXPECT_TRUE(r.dim_le_2);
    EXPECT_EQ(r.dim_le_2, is_dim2(n_poset));
    expect_valid_realizer(n_poset, r);
}
```

- [ ] **Step 2: Build and run**

Run: `mise run nomadim-test`
Expected: all four new tests PASS (S₃ and canonical report no realizer; single-sync and N-poset produce verified realizers).

- [ ] **Step 3: Commit**

```bash
git add nomadim/tests/test_realizer.cpp
git commit -m "test(nomadim): realizer on S3, canonical exec, single-sync, N-poset"
```

---

### Task 5: Exhaustive cross-check against is_dim2 over all small DAGs

**Files:**
- Modify: `nomadim/tests/test_realizer.cpp` (append test)

- [ ] **Step 1: Add the brute-force cross-check**

Append to `nomadim/tests/test_realizer.cpp`:

```cpp
// For every acyclic directed graph on up to 4 vertices, find_realizer must agree
// with is_dim2, and whenever it claims dim <= 2 it must produce a verified
// realizer. This exercises thousands of distinct posets (including ones with
// redundant transitive edges).
TEST(Realizer, MatchesIsDim2OnAllSmallDags) {
    for (int n = 1; n <= 4; ++n) {
        std::vector<std::pair<int,int>> slots;
        for (int i = 0; i < n; ++i)
            for (int j = 0; j < n; ++j)
                if (i != j) slots.push_back({i, j});
        int E = (int)slots.size();
        for (long mask = 0; mask < (1L << E); ++mask) {
            adjacency_list g(n);
            for (int b = 0; b < E; ++b)
                if (mask & (1L << b))
                    g[slots[b].first].push_back(slots[b].second);
            if (have_cycle(g)) continue;
            Realizer r = find_realizer(g);
            ASSERT_EQ(r.dim_le_2, is_dim2(g)) << "n=" << n << " mask=" << mask;
            if (r.dim_le_2) {
                SCOPED_TRACE("n=" + std::to_string(n) + " mask=" + std::to_string(mask));
                expect_valid_realizer(g, r);
            }
        }
    }
}
```

- [ ] **Step 2: Build and run**

Run: `mise run nomadim-test`
Expected: `Realizer.MatchesIsDim2OnAllSmallDags` PASSES (completes in a few seconds). If any `ASSERT_EQ` fires, the printed `n`/`mask` identifies the offending poset — debug with superpowers:systematic-debugging before proceeding.

- [ ] **Step 3: Commit**

```bash
git add nomadim/tests/test_realizer.cpp
git commit -m "test(nomadim): exhaustive realizer/is_dim2 cross-check on all DAGs <=4 vertices"
```

---

### Task 6: Document the algorithm and run the full suite

**Files:**
- Modify: `docs/INDEX.md` (nomadim section)

- [ ] **Step 1: Add an INDEX entry**

Open `docs/INDEX.md`, find the nomadim C++ tool section, and add a bullet describing the new algorithm, e.g.:

```markdown
- `find_realizer(adjacency_list)` (`nomadim/include/nomadim/realizer.hpp`) — returns a 2-realizer (two linear extensions whose intersection is the partial order) when the poset has order dimension ≤ 2, else reports dim > 2. Backtracking transitive orientation of the incomparability graph; independent of `dimension.cpp`.
```

- [ ] **Step 2: Run the full default test tier**

Run: `mise run nomadim-test`
Expected: every test passes, including all pre-existing dimension/enumerate/io tests (confirming `dimension.cpp` and the golden counts are unaffected).

- [ ] **Step 3: Commit**

```bash
git add docs/INDEX.md
git commit -m "docs(INDEX): document nomadim find_realizer algorithm"
```

---

## Self-review notes (already reconciled)

- **Spec coverage:** Implements §2 of the design spec in full (API, algorithm, exhaustive tests). The editor (§1, §3–7) is a separate follow-up plan.
- **`dimension.cpp` untouched:** realizer lives in its own translation unit; Task 6 step 2 re-runs the existing suite to confirm the golden enumeration counts are unaffected.
- **Type consistency:** `Realizer{dim_le_2, l1, l2}`, `find_realizer`, `StrictRel::add_and_close`, `linearize`, and `expect_valid_realizer` are used with identical names/signatures across all tasks.
- **No placeholders:** every code and command step is complete and runnable.
