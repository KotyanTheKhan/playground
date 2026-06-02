# nomadim General Dimension, Realizers & Meta Fields — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Extend the `nomadim/` C++ project to compute general poset dimension (including > 2) by coloring the hypergraph of critical pairs, find one realizer and all minimum realizers, and persist `notes`/`dimension`/`realizers` meta fields — exposed across library, CLI, and the web editor.

**Architecture:** A shared dense strict-order helper (`order_relation.hpp`) underpins a new `hypergraph` module (reversible sets, minimal alternating-cycle hyperedges, chromatic-number coloring). `analyze_dimension` ties critical pairs + hyperedges + minimum colorings into a `DimensionResult`; realizers are the linear extensions induced by each coloring's reversible classes. A test-only `oracle` (brute-force linear-extension enumeration) independently validates dimension and realizer correctness. IO gains a `meta` block (cached, with a `source_hash`), a new `dimension` CLI subcommand, WASM bindings, and an editor panel.

**Tech Stack:** C++17, CMake + FetchContent (yaml-cpp, CLI11, GoogleTest), Emscripten/Embind (WASM), ES modules + `node:test` + Playwright (editor).

**Branch:** `feat/nomadim-dimension` (already created).

---

## Conventions for every task

- **Configure once** (Task 0). Thereafter build the test binary with:
  `cmake --build nomadim/build -j --target nomadim_tests`
- **Run a focused suite:** `./nomadim/build/nomadim_tests --gtest_filter='Suite.*'`
- nomadim is **not** under the Coq `timed-build.sh` wrapper. Use CMake/CTest directly (or `mise run nomadim-test` for the full tier).
- Commit messages: imperative, `feat(nomadim):` / `test(nomadim):` / `docs(nomadim):`. **No AI watermark / Co-Authored-By** (per CLAUDE.md).
- Math reference (in code comments where relevant): dim(P) = χ of the critical-pair hypergraph; a color class is a *reversible* set (poset + its reversed pairs stays acyclic); the linear extensions induced by the classes of a minimum coloring form a realizer (Felsner–Trotter).

---

## Task 0: Configure the build

**Files:** none (build dir only)

- [ ] **Step 1: Configure CMake**

Run:
```bash
cmake -S nomadim -B nomadim/build -DCMAKE_BUILD_TYPE=Release
```
Expected: configures successfully, ends with `-- Build files have been written to: .../nomadim/build`.

- [ ] **Step 2: Baseline build + test**

Run:
```bash
cmake --build nomadim/build -j --target nomadim_tests && ./nomadim/build/nomadim_tests
```
Expected: all existing tests PASS (green). This is the clean baseline before changes.

---

## Task 1: Extract `order_relation.hpp` (shared strict-order helper)

Pull the dense `StrictRel` + `linearize` out of `realizer.cpp` into a shared header and add a `topo_order` (deterministic linear extension of a *partial* order, smallest index first) and `base_order` (build from adjacency).

**Files:**
- Create: `nomadim/include/nomadim/order_relation.hpp`
- Modify: `nomadim/src/realizer.cpp` (use the shared header)
- Test: `nomadim/tests/test_order_relation.cpp`
- Modify: `nomadim/CMakeLists.txt` (add test file)

- [ ] **Step 1: Write the failing test**

Create `nomadim/tests/test_order_relation.cpp`:
```cpp
#include <gtest/gtest.h>
#include "nomadim/order_relation.hpp"
#include <vector>

using namespace nomadim;

TEST(OrderRelation, AddAndCloseDetectsCycle) {
    StrictRel r(3);
    EXPECT_TRUE(r.add_and_close(0, 1));
    EXPECT_TRUE(r.add_and_close(1, 2));
    EXPECT_TRUE(r.less(0, 2));          // transitivity closed
    EXPECT_FALSE(r.add_and_close(2, 0)); // would create 0<...<0
}

TEST(OrderRelation, BaseOrderFromAdjacency) {
    adjacency_list g = {{1}, {2}, {}};   // 0<1<2
    StrictRel r = base_order(g);
    EXPECT_TRUE(r.less(0, 2));
    EXPECT_FALSE(r.less(2, 0));
}

TEST(OrderRelation, TopoOrderRespectsPartialOrderSmallestFirst) {
    // 0<2, 1<2 ; 0 and 1 incomparable -> smallest-first gives [0,1,2].
    StrictRel r(3);
    r.add_and_close(0, 2);
    r.add_and_close(1, 2);
    std::vector<int> ord = topo_order(r);
    EXPECT_EQ(ord, (std::vector<int>{0, 1, 2}));
}

TEST(OrderRelation, LinearizeTotalOrder) {
    StrictRel r(3);
    r.add_and_close(2, 0);
    r.add_and_close(0, 1);   // total: 2<0<1
    EXPECT_EQ(linearize(r), (std::vector<int>{2, 0, 1}));
}
```

- [ ] **Step 2: Register the test, build, verify it fails**

In `nomadim/CMakeLists.txt`, add `tests/test_order_relation.cpp` to the `nomadim_tests` `add_executable(...)` source list (line ~84).

Run:
```bash
cmake -S nomadim -B nomadim/build -DCMAKE_BUILD_TYPE=Release && cmake --build nomadim/build -j --target nomadim_tests
```
Expected: FAIL to compile — `nomadim/order_relation.hpp` not found.

- [ ] **Step 3: Create the header**

Create `nomadim/include/nomadim/order_relation.hpp`:
```cpp
#ifndef NOMADIM_ORDER_RELATION_HPP
#define NOMADIM_ORDER_RELATION_HPP

#include "nomadim/types.hpp"
#include <vector>

namespace nomadim {

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

// Build the closed strict order of adjacency `g` (edge u->v means u < v).
inline StrictRel base_order(const adjacency_list& g) {
    StrictRel r((int)g.size());
    for (int u = 0; u < (int)g.size(); ++u)
        for (int v : g[u]) r.add_and_close(u, v);
    return r;
}

// Linearize a TOTAL strict order into a permutation, least element first.
// In a total order each element has a distinct number of elements below it.
inline std::vector<int> linearize(const StrictRel& r) {
    int n = r.n;
    std::vector<int> below(n, 0), order(n);
    for (int a = 0; a < n; ++a)
        for (int b = 0; b < n; ++b)
            if (r.less(a, b)) below[b]++;
    for (int e = 0; e < n; ++e) order[below[e]] = e;
    return order;
}

// Deterministic linear extension of the (possibly partial) order r: repeatedly
// emit the smallest-indexed not-yet-placed element with no unplaced predecessor.
inline std::vector<int> topo_order(const StrictRel& r) {
    int n = r.n;
    std::vector<char> placed(n, 0);
    std::vector<int> order;
    order.reserve(n);
    for (int step = 0; step < n; ++step)
        for (int c = 0; c < n; ++c) {
            if (placed[c]) continue;
            bool minimal = true;
            for (int d = 0; d < n; ++d)
                if (!placed[d] && d != c && r.less(d, c)) { minimal = false; break; }
            if (minimal) { placed[c] = 1; order.push_back(c); break; }
        }
    return order;
}

} // namespace nomadim

#endif // NOMADIM_ORDER_RELATION_HPP
```

- [ ] **Step 4: Refactor `realizer.cpp` to use the header**

In `nomadim/src/realizer.cpp`, replace the local `StrictRel` struct and `linearize` function (lines ~9-49) with an include. The file top becomes:
```cpp
#include "nomadim/realizer.hpp"
#include "nomadim/order_relation.hpp"
#include <utility>
#include <vector>

namespace nomadim {
namespace {
```
Delete the in-file `struct StrictRel { ... };` and the in-file `std::vector<int> linearize(const StrictRel& r) { ... }` (now provided by the header). Keep `struct Solver { ... }` and `find_realizer` unchanged — they call `linearize`/`StrictRel` which now resolve to the header's `nomadim::` versions.

- [ ] **Step 5: Build + run both suites**

Run:
```bash
cmake --build nomadim/build -j --target nomadim_tests && ./nomadim/build/nomadim_tests --gtest_filter='OrderRelation.*:Realizer.*'
```
Expected: PASS. The pre-existing `Realizer.*` tests still pass (refactor is behavior-preserving).

- [ ] **Step 6: Commit**

```bash
git add nomadim/include/nomadim/order_relation.hpp nomadim/src/realizer.cpp nomadim/tests/test_order_relation.cpp nomadim/CMakeLists.txt
git commit -m "refactor(nomadim): extract shared StrictRel/order helpers into order_relation.hpp"
```

---

## Task 2: Reversibility primitives (`hypergraph` module foundation)

`Caps` config + `is_reversible` / `reverse_set` over critical pairs.

**Files:**
- Create: `nomadim/include/nomadim/hypergraph.hpp`
- Create: `nomadim/src/hypergraph.cpp`
- Test: `nomadim/tests/test_hypergraph.cpp`
- Modify: `nomadim/CMakeLists.txt` (add src to `nomadim_core` + `nomadim_wasm`; add test file)

- [ ] **Step 1: Write the failing test**

Create `nomadim/tests/test_hypergraph.cpp`:
```cpp
#include <gtest/gtest.h>
#include "nomadim/hypergraph.hpp"
#include "nomadim/dimension.hpp"
#include "nomadim/floyd.hpp"
#include "nomadim/order_relation.hpp"
#include <vector>

using namespace nomadim;

namespace {
std::vector<critical_pair> cps_of(const adjacency_list& g) {
    std::vector<int> m = make_graph_matrix(g);
    return find_critical_pairs(m.data(), (int)g.size());
}
} // namespace

TEST(Hypergraph, SingletonAlwaysReversible) {
    adjacency_list a3(3);                 // 3-antichain
    auto cps = cps_of(a3);
    StrictRel base = base_order(a3);
    ASSERT_FALSE(cps.empty());
    EXPECT_TRUE(is_reversible(base, cps, {0}));
}

TEST(Hypergraph, OppositePairIsNotReversible) {
    // In a 3-antichain (a,b) and (b,a) are both critical and conflict.
    adjacency_list a3(3);
    auto cps = cps_of(a3);
    StrictRel base = base_order(a3);
    // Find indices of a mutually-reversed pair (x,y) and (y,x).
    int i = -1, j = -1;
    for (size_t p = 0; p < cps.size() && i < 0; ++p)
        for (size_t q = 0; q < cps.size(); ++q)
            if (cps[p].x == cps[q].y && cps[p].y == cps[q].x) { i = (int)p; j = (int)q; break; }
    ASSERT_GE(i, 0);
    EXPECT_TRUE(is_reversible(base, cps, {i}));
    EXPECT_FALSE(is_reversible(base, cps, {i, j}));
}
```

- [ ] **Step 2: Register + verify failure**

In `nomadim/CMakeLists.txt`:
- add `src/hypergraph.cpp` to the `add_library(nomadim_core ...)` list (line ~64) AND to the `add_executable(nomadim_wasm ...)` list (line ~26).
- add `tests/test_hypergraph.cpp` to the `nomadim_tests` sources.

Run:
```bash
cmake -S nomadim -B nomadim/build -DCMAKE_BUILD_TYPE=Release && cmake --build nomadim/build -j --target nomadim_tests
```
Expected: FAIL — `nomadim/hypergraph.hpp` not found.

- [ ] **Step 3: Create the header**

Create `nomadim/include/nomadim/hypergraph.hpp`:
```cpp
#ifndef NOMADIM_HYPERGRAPH_HPP
#define NOMADIM_HYPERGRAPH_HPP

#include "nomadim/types.hpp"
#include "nomadim/order_relation.hpp"
#include <vector>

namespace nomadim {

// Resource caps for the (worst-case exponential) dimension/realizer routines.
// Exceeding any cap makes the analysis routines throw std::runtime_error.
struct Caps {
    int max_vertices = 16;
    int max_critical_pairs = 64;
    int max_results = 1000;   // colorings / realizers / hyperedges
};

// Reverse every critical pair in `idxs` on top of `base` (reversing (x,y) adds
// y<x). Returns true iff the result stays acyclic; if so, `out` holds the closed
// order (a witness from which a linear extension can be read off).
bool reverse_set(const StrictRel& base, const std::vector<critical_pair>& cps,
                 const std::vector<int>& idxs, StrictRel& out);

// Convenience: just the reversibility verdict.
bool is_reversible(const StrictRel& base, const std::vector<critical_pair>& cps,
                   const std::vector<int>& idxs);

} // namespace nomadim

#endif // NOMADIM_HYPERGRAPH_HPP
```

- [ ] **Step 4: Create the implementation**

Create `nomadim/src/hypergraph.cpp`:
```cpp
#include "nomadim/hypergraph.hpp"

namespace nomadim {

bool reverse_set(const StrictRel& base, const std::vector<critical_pair>& cps,
                 const std::vector<int>& idxs, StrictRel& out) {
    out = base;
    for (int i : idxs)
        if (!out.add_and_close(cps[i].y, cps[i].x))   // reverse (x,y) => y<x
            return false;
    return true;
}

bool is_reversible(const StrictRel& base, const std::vector<critical_pair>& cps,
                   const std::vector<int>& idxs) {
    StrictRel out(base.n);
    return reverse_set(base, cps, idxs, out);
}

} // namespace nomadim
```

- [ ] **Step 5: Build + run**

Run:
```bash
cmake --build nomadim/build -j --target nomadim_tests && ./nomadim/build/nomadim_tests --gtest_filter='Hypergraph.*'
```
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add nomadim/include/nomadim/hypergraph.hpp nomadim/src/hypergraph.cpp nomadim/tests/test_hypergraph.cpp nomadim/CMakeLists.txt
git commit -m "feat(nomadim): reversibility primitives and Caps for the critical-pair hypergraph"
```

---

## Task 3: Minimal alternating-cycle hyperedges

Enumerate minimal non-reversible subsets of critical pairs (the hypergraph edges), capped by `Caps`.

**Files:**
- Modify: `nomadim/include/nomadim/hypergraph.hpp`
- Modify: `nomadim/src/hypergraph.cpp`
- Test: `nomadim/tests/test_hypergraph.cpp`

- [ ] **Step 1: Write the failing test**

Append to `nomadim/tests/test_hypergraph.cpp`:
```cpp
TEST(Hypergraph, AntichainHasSizeTwoHyperedges) {
    // 3-antichain: each {(a,b),(b,a)} mutually-reversed pair is a size-2 edge;
    // there are 3 such opposite pairs. No larger minimal edges.
    adjacency_list a3(3);
    auto cps = cps_of(a3);
    StrictRel base = base_order(a3);
    auto edges = enumerate_hyperedges(base, cps, Caps{});
    ASSERT_FALSE(edges.empty());
    for (const auto& e : edges) EXPECT_EQ(e.size(), 2u);
    EXPECT_EQ(edges.size(), 3u);
}

TEST(Hypergraph, StandardExampleS3HasOneSizeThreeHyperedge) {
    // S_3 has exactly 3 critical pairs; together they are non-reversible, but
    // every pair of them is reversible -> a single size-3 minimal hyperedge.
    adjacency_list s3(6); s3[0] = {4,5}; s3[1] = {3,5}; s3[2] = {3,4};
    auto cps = cps_of(s3);
    ASSERT_EQ(cps.size(), 3u);
    StrictRel base = base_order(s3);
    auto edges = enumerate_hyperedges(base, cps, Caps{});
    ASSERT_EQ(edges.size(), 1u);
    EXPECT_EQ(edges[0].size(), 3u);
}
```

- [ ] **Step 2: Build, verify failure**

Run:
```bash
cmake --build nomadim/build -j --target nomadim_tests
```
Expected: FAIL — `enumerate_hyperedges` not declared.

- [ ] **Step 3: Declare in header**

Add to `nomadim/include/nomadim/hypergraph.hpp` before the closing namespace:
```cpp
// Minimal non-reversible subsets of the critical pairs (alternating cycles):
// the edges of the dimension hypergraph. Each edge is a sorted list of indices
// into `cps`. Enumerated by increasing size; a set is an edge iff it is
// non-reversible but every proper subset is reversible. Throws
// std::runtime_error if cps.size() exceeds caps.max_critical_pairs, and stops
// after caps.max_results edges.
std::vector<std::vector<int>>
enumerate_hyperedges(const StrictRel& base, const std::vector<critical_pair>& cps,
                     const Caps& caps);
```

- [ ] **Step 4: Implement**

Add to `nomadim/src/hypergraph.cpp` (add `#include <stdexcept>` and `#include <algorithm>` at the top):
```cpp
namespace {

// Is `sub` reversible AND every immediate (one-element-smaller) subset of it
// also reversible? Used to confirm minimality while enumerating by size.
bool all_proper_subsets_reversible(const StrictRel& base,
                                   const std::vector<critical_pair>& cps,
                                   const std::vector<int>& sub) {
    for (size_t drop = 0; drop < sub.size(); ++drop) {
        std::vector<int> s;
        s.reserve(sub.size() - 1);
        for (size_t i = 0; i < sub.size(); ++i)
            if (i != drop) s.push_back(sub[i]);
        if (!is_reversible(base, cps, s)) return false;  // a smaller edge exists
    }
    return true;
}

} // namespace

std::vector<std::vector<int>>
enumerate_hyperedges(const StrictRel& base, const std::vector<critical_pair>& cps,
                     const Caps& caps) {
    int m = (int)cps.size();
    if (m > caps.max_critical_pairs)
        throw std::runtime_error("hypergraph too large: critical pairs (" +
            std::to_string(m) + ") exceed cap (" +
            std::to_string(caps.max_critical_pairs) + ")");

    std::vector<std::vector<int>> edges;
    std::vector<int> sub;
    // Enumerate subsets by increasing size; record minimal non-reversible ones.
    // Singletons are always reversible, so the smallest possible edge is size 2.
    std::function<void(int, int, int)> rec = [&](int start, int size, int remaining) {
        if ((int)edges.size() >= caps.max_results) return;
        if (remaining == 0) {
            if (!is_reversible(base, cps, sub) &&
                all_proper_subsets_reversible(base, cps, sub))
                edges.push_back(sub);
            return;
        }
        for (int i = start; i <= m - remaining; ++i) {
            sub.push_back(i);
            rec(i + 1, size, remaining - 1);
            sub.pop_back();
            if ((int)edges.size() >= caps.max_results) return;
        }
    };
    for (int size = 2; size <= m && (int)edges.size() < caps.max_results; ++size)
        rec(0, size, size);
    return edges;
}
```
Add `#include <functional>` to the includes as well.

- [ ] **Step 5: Build + run**

Run:
```bash
cmake --build nomadim/build -j --target nomadim_tests && ./nomadim/build/nomadim_tests --gtest_filter='Hypergraph.*'
```
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add nomadim/include/nomadim/hypergraph.hpp nomadim/src/hypergraph.cpp nomadim/tests/test_hypergraph.cpp
git commit -m "feat(nomadim): enumerate minimal alternating-cycle hyperedges"
```

---

## Task 4: Chromatic-number coloring + minimum-coloring enumeration

`chromatic_number` (= dimension once chains are handled) and `enumerate_min_colorings`, where each color class must be a reversible set.

**Files:**
- Modify: `nomadim/include/nomadim/hypergraph.hpp`
- Modify: `nomadim/src/hypergraph.cpp`
- Test: `nomadim/tests/test_hypergraph.cpp`

- [ ] **Step 1: Write the failing test**

Append to `nomadim/tests/test_hypergraph.cpp`:
```cpp
TEST(Hypergraph, ChromaticNumberAntichainIsTwo) {
    adjacency_list a3(3);
    auto cps = cps_of(a3);
    StrictRel base = base_order(a3);
    EXPECT_EQ(chromatic_number(base, cps, Caps{}), 2);
}

TEST(Hypergraph, ChromaticNumberS3IsThree) {
    adjacency_list s3(6); s3[0] = {4,5}; s3[1] = {3,5}; s3[2] = {3,4};
    auto cps = cps_of(s3);
    StrictRel base = base_order(s3);
    EXPECT_EQ(chromatic_number(base, cps, Caps{}), 3);
}

TEST(Hypergraph, MinColoringsAreProperAndCover) {
    adjacency_list s3(6); s3[0] = {4,5}; s3[1] = {3,5}; s3[2] = {3,4};
    auto cps = cps_of(s3);
    StrictRel base = base_order(s3);
    auto colorings = enumerate_min_colorings(base, cps, 3, Caps{});
    ASSERT_FALSE(colorings.empty());
    for (const auto& col : colorings) {
        ASSERT_EQ(col.size(), cps.size());
        // exactly 3 colors used
        std::vector<int> seen(3, 0);
        for (int c : col) { ASSERT_GE(c, 0); ASSERT_LT(c, 3); seen[c] = 1; }
        EXPECT_EQ(seen[0] + seen[1] + seen[2], 3);
        // each color class reversible
        for (int c = 0; c < 3; ++c) {
            std::vector<int> idxs;
            for (size_t i = 0; i < col.size(); ++i) if (col[i] == c) idxs.push_back((int)i);
            EXPECT_TRUE(is_reversible(base, cps, idxs));
        }
        // canonical: first pair is color 0
        EXPECT_EQ(col[0], 0);
    }
}
```

- [ ] **Step 2: Build, verify failure**

Run: `cmake --build nomadim/build -j --target nomadim_tests`
Expected: FAIL — `chromatic_number` / `enumerate_min_colorings` not declared.

- [ ] **Step 3: Declare in header**

Add to `nomadim/include/nomadim/hypergraph.hpp` before the closing namespace:
```cpp
// Smallest k>=2 for which the critical pairs admit a proper coloring (each color
// class reversible). Precondition: cps non-empty (callers handle the chain case
// dim<=1 separately). Throws if cps exceed caps.max_critical_pairs.
int chromatic_number(const StrictRel& base, const std::vector<critical_pair>& cps,
                     const Caps& caps);

// All distinct proper k-colorings using exactly k colors, each as a color-per-
// critical-pair vector, canonicalized (colors numbered by first appearance) so
// permutation-equivalent colorings are reported once. Capped at caps.max_results.
std::vector<std::vector<int>>
enumerate_min_colorings(const StrictRel& base, const std::vector<critical_pair>& cps,
                        int k, const Caps& caps);
```

- [ ] **Step 4: Implement**

Add to `nomadim/src/hypergraph.cpp`:
```cpp
namespace {

// Backtracking proper coloring. `colors[i]` in [0,k). A partial assignment is
// valid iff every color class is reversible. `collect_all` switches between
// "find one" (chromatic test) and "enumerate all canonical colorings".
struct Colorer {
    const StrictRel& base;
    const std::vector<critical_pair>& cps;
    int k, m, max_results;
    std::vector<int> colors;
    std::vector<std::vector<int>> all;   // collected colorings (canonical)
    bool want_all;

    bool class_reversible(int c, int upto) {
        std::vector<int> idxs;
        for (int j = 0; j <= upto; ++j) if (colors[j] == c) idxs.push_back(j);
        return is_reversible(base, cps, idxs);
    }

    bool rec(int i, int used) {           // `used` = number of colors used so far
        if (i == m) {
            if (want_all) {
                if (used == k) { all.push_back(colors); }
                return (int)all.size() >= max_results;  // signal: stop if full
            }
            return true;                  // found one
        }
        // Canonical symmetry break: a new color must be the next unused index.
        int limit = std::min(k, used + 1);
        for (int c = 0; c < limit; ++c) {
            colors[i] = c;
            if (class_reversible(c, i)) {
                bool stop = rec(i + 1, c == used ? used + 1 : used);
                if (stop && !want_all) return true;            // first solution
                if (stop && want_all && (int)all.size() >= max_results) return true;
            }
        }
        colors[i] = -1;
        return false;
    }
};

} // namespace

int chromatic_number(const StrictRel& base, const std::vector<critical_pair>& cps,
                     const Caps& caps) {
    int m = (int)cps.size();
    if (m > caps.max_critical_pairs)
        throw std::runtime_error("hypergraph too large: critical pairs (" +
            std::to_string(m) + ") exceed cap (" +
            std::to_string(caps.max_critical_pairs) + ")");
    for (int k = 2; k <= m; ++k) {
        Colorer col{base, cps, k, m, caps.max_results, std::vector<int>(m, -1), {}, false};
        if (col.rec(0, 0)) return k;
    }
    return m;   // every singleton its own color (unreachable for valid posets)
}

std::vector<std::vector<int>>
enumerate_min_colorings(const StrictRel& base, const std::vector<critical_pair>& cps,
                        int k, const Caps& caps) {
    int m = (int)cps.size();
    if (m > caps.max_critical_pairs)
        throw std::runtime_error("hypergraph too large: critical pairs (" +
            std::to_string(m) + ") exceed cap (" +
            std::to_string(caps.max_critical_pairs) + ")");
    Colorer col{base, cps, k, m, caps.max_results, std::vector<int>(m, -1), {}, true};
    col.rec(0, 0);
    return col.all;
}
```

- [ ] **Step 5: Build + run**

Run:
```bash
cmake --build nomadim/build -j --target nomadim_tests && ./nomadim/build/nomadim_tests --gtest_filter='Hypergraph.*'
```
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add nomadim/include/nomadim/hypergraph.hpp nomadim/src/hypergraph.cpp nomadim/tests/test_hypergraph.cpp
git commit -m "feat(nomadim): chromatic-number coloring and minimum-coloring enumeration"
```

---

## Task 5: `analyze_dimension` — DimensionResult (dimension + cps + hyperedges + colorings + realizers)

The public entry point in the dimension module.

**Files:**
- Modify: `nomadim/include/nomadim/dimension.hpp`
- Modify: `nomadim/src/dimension.cpp`
- Test: `nomadim/tests/test_dimension.cpp`

- [ ] **Step 1: Write the failing test**

Append to `nomadim/tests/test_dimension.cpp` (add `#include "nomadim/order_relation.hpp"` and `#include <set>` at top):
```cpp
// Helper: intersection of the realizer's linear extensions equals the order.
static bool realizer_intersects_to_order(const adjacency_list& g,
                                         const std::vector<std::vector<int>>& realizer) {
    int n = (int)g.size();
    StrictRel base = base_order(g);
    std::vector<std::vector<int>> pos(realizer.size(), std::vector<int>(n));
    for (size_t r = 0; r < realizer.size(); ++r)
        for (int i = 0; i < n; ++i) pos[r][realizer[r][i]] = i;
    for (int a = 0; a < n; ++a)
        for (int b = 0; b < n; ++b) {
            if (a == b) continue;
            bool in_all = true;
            for (size_t r = 0; r < realizer.size(); ++r)
                if (!(pos[r][a] < pos[r][b])) { in_all = false; break; }
            if (in_all != base.less(a, b)) return false;
        }
    return true;
}

TEST(Dimension, ChainHasDimensionOne) {
    adjacency_list chain = {{1}, {2}, {3}, {}};
    DimensionResult dr = analyze_dimension(chain, Caps{});
    EXPECT_EQ(dr.dimension, 1);
    ASSERT_EQ(dr.colorings.size(), 1u);                 // the trivial realizer
    EXPECT_EQ(dr.colorings[0].realizer.size(), 1u);
}

TEST(Dimension, AntichainHasDimensionTwo) {
    adjacency_list a3(3);
    DimensionResult dr = analyze_dimension(a3, Caps{});
    EXPECT_EQ(dr.dimension, 2);
}

TEST(Dimension, StandardExampleS3HasDimensionThree) {
    adjacency_list s3(6); s3[0] = {4,5}; s3[1] = {3,5}; s3[2] = {3,4};
    DimensionResult dr = analyze_dimension(s3, Caps{});
    EXPECT_EQ(dr.dimension, 3);
    ASSERT_FALSE(dr.colorings.empty());
    for (const auto& col : dr.colorings) {
        EXPECT_EQ((int)col.realizer.size(), 3);
        EXPECT_TRUE(realizer_intersects_to_order(s3, col.realizer));
    }
}

TEST(Dimension, StandardExampleS4HasDimensionFour) {
    // S_4: minimals 0..3, maximals 4..7; a_i < b_j iff i != j.
    adjacency_list s4(8);
    for (int i = 0; i < 4; ++i)
        for (int j = 0; j < 4; ++j)
            if (i != j) s4[i].push_back(4 + j);
    EXPECT_EQ(analyze_dimension(s4, Caps{}).dimension, 4);
}

TEST(Dimension, AgreesWithIsDim2) {
    adjacency_list n_poset = {{2}, {2, 3}, {}, {}};
    EXPECT_EQ(analyze_dimension(n_poset, Caps{}).dimension == 2, is_dim2(n_poset));
    adjacency_list s3(6); s3[0] = {4,5}; s3[1] = {3,5}; s3[2] = {3,4};
    EXPECT_EQ(analyze_dimension(s3, Caps{}).dimension == 2, is_dim2(s3));
}

TEST(Dimension, CapsThrowOnTooManyVertices) {
    adjacency_list big(20);
    Caps caps; caps.max_vertices = 8;
    EXPECT_THROW(analyze_dimension(big, caps), std::runtime_error);
}
```

- [ ] **Step 2: Build, verify failure**

Run: `cmake --build nomadim/build -j --target nomadim_tests`
Expected: FAIL — `DimensionResult` / `analyze_dimension` not declared.

- [ ] **Step 3: Declare in `dimension.hpp`**

Add to `nomadim/include/nomadim/dimension.hpp` (add `#include "nomadim/hypergraph.hpp"` near the top), before the closing namespace:
```cpp
// One minimum proper coloring of the critical-pair hypergraph, plus the realizer
// (one linear extension per reversible color class) it induces.
struct Coloring {
    std::vector<std::vector<critical_pair>> classes;   // dimension reversible classes
    std::vector<std::vector<int>> realizer;            // dimension linear extensions
};

// Full analysis of a poset's order dimension.
struct DimensionResult {
    int dimension = 0;
    std::vector<critical_pair> critical_pairs;
    std::vector<std::vector<int>> hyperedges;          // indices into critical_pairs
    std::vector<Coloring> colorings;                   // minimum colorings (capped)
};

// Compute the dimension, critical pairs, hyperedges, and all minimum colorings
// (each with its induced realizer) of the poset given by adjacency `g`.
// Precondition: `g` is acyclic. Throws std::runtime_error if `g` exceeds the caps.
DimensionResult analyze_dimension(const adjacency_list& g, const Caps& caps = Caps{});

// Convenience: just the dimension number.
int dimension(const adjacency_list& g, const Caps& caps = Caps{});
```

- [ ] **Step 4: Implement in `dimension.cpp`**

Add to `nomadim/src/dimension.cpp` (add `#include "nomadim/hypergraph.hpp"`, `#include "nomadim/order_relation.hpp"`, `#include <stdexcept>`):
```cpp
namespace {

// Build the realizer induced by a coloring: for each color class, reverse its
// pairs on top of the base order and read off a deterministic linear extension.
Coloring make_coloring(const StrictRel& base, const std::vector<critical_pair>& cps,
                       const std::vector<int>& colors, int k) {
    Coloring out;
    out.classes.assign(k, {});
    for (size_t i = 0; i < cps.size(); ++i) out.classes[colors[i]].push_back(cps[i]);
    for (int c = 0; c < k; ++c) {
        std::vector<int> idxs;
        for (size_t i = 0; i < cps.size(); ++i) if (colors[i] == c) idxs.push_back((int)i);
        StrictRel cls(base.n);
        reverse_set(base, cps, idxs, cls);     // valid coloring => always succeeds
        out.realizer.push_back(topo_order(cls));
    }
    return out;
}

} // namespace

DimensionResult analyze_dimension(const adjacency_list& g, const Caps& caps) {
    int n = (int)g.size();
    if (n > caps.max_vertices)
        throw std::runtime_error("poset too large: vertices (" + std::to_string(n) +
            ") exceed cap (" + std::to_string(caps.max_vertices) + ")");

    DimensionResult dr;
    std::vector<int> matrix = make_graph_matrix(g);
    dr.critical_pairs = find_critical_pairs(matrix.data(), n);   // closes matrix
    StrictRel base = base_order(g);

    if (dr.critical_pairs.empty()) {
        // No incomparable pairs -> a chain. dim 1 (or 0 for the empty poset).
        dr.dimension = (n == 0) ? 0 : 1;
        if (n > 0) {
            Coloring c; c.realizer.push_back(topo_order(base));
            dr.colorings.push_back(std::move(c));
        }
        return dr;
    }

    dr.hyperedges = enumerate_hyperedges(base, dr.critical_pairs, caps);
    dr.dimension = chromatic_number(base, dr.critical_pairs, caps);
    auto colorings = enumerate_min_colorings(base, dr.critical_pairs, dr.dimension, caps);
    for (const auto& colors : colorings)
        dr.colorings.push_back(make_coloring(base, dr.critical_pairs, colors, dr.dimension));
    return dr;
}

int dimension(const adjacency_list& g, const Caps& caps) {
    return analyze_dimension(g, caps).dimension;
}
```

- [ ] **Step 5: Build + run**

Run:
```bash
cmake --build nomadim/build -j --target nomadim_tests && ./nomadim/build/nomadim_tests --gtest_filter='Dimension.*'
```
Expected: PASS (including `StandardExampleS4HasDimensionFour`, which may take a few seconds).

- [ ] **Step 6: Commit**

```bash
git add nomadim/include/nomadim/dimension.hpp nomadim/src/dimension.cpp nomadim/tests/test_dimension.cpp
git commit -m "feat(nomadim): analyze_dimension via critical-pair hypergraph coloring"
```

---

## Task 6: Brute-force oracle (test-only) + cross-validation

An independent dimension/realizer oracle (enumerate linear extensions, minimum realizing subset) linked only into tests, used to validate `analyze_dimension` on all small DAGs.

**Files:**
- Create: `nomadim/include/nomadim/oracle.hpp`
- Create: `nomadim/src/oracle.cpp`
- Test: `nomadim/tests/test_oracle.cpp`
- Modify: `nomadim/CMakeLists.txt` (compile `src/oracle.cpp` into `nomadim_tests` only — NOT `nomadim_core`/`nomadim_wasm`; add test file)

- [ ] **Step 1: Write the failing test**

Create `nomadim/tests/test_oracle.cpp`:
```cpp
#include <gtest/gtest.h>
#include "nomadim/oracle.hpp"
#include "nomadim/dimension.hpp"
#include <vector>

using namespace nomadim;

TEST(Oracle, MatchesAnalyzeOnAllSmallDags) {
    for (int n = 1; n <= 4; ++n) {
        std::vector<std::pair<int,int>> slots;
        for (int i = 0; i < n; ++i)
            for (int j = 0; j < n; ++j)
                if (i != j) slots.push_back({i, j});
        int E = (int)slots.size();
        for (long mask = 0; mask < (1L << E); ++mask) {
            adjacency_list g(n);
            for (int b = 0; b < E; ++b)
                if (mask & (1L << b)) g[slots[b].first].push_back(slots[b].second);
            if (have_cycle(g)) continue;
            int oracle = oracle_dimension(g);
            int got = analyze_dimension(g, Caps{}).dimension;
            ASSERT_EQ(got, oracle) << "n=" << n << " mask=" << mask;
        }
    }
}

TEST(Oracle, S3DimensionIsThree) {
    adjacency_list s3(6); s3[0] = {4,5}; s3[1] = {3,5}; s3[2] = {3,4};
    EXPECT_EQ(oracle_dimension(s3), 3);
}
```

- [ ] **Step 2: Register + verify failure**

In `nomadim/CMakeLists.txt`: add `tests/test_oracle.cpp` AND `src/oracle.cpp` to the `add_executable(nomadim_tests ...)` source list (oracle compiled straight into the test binary; keep it out of `nomadim_core` and `nomadim_wasm`).

Run: `cmake -S nomadim -B nomadim/build -DCMAKE_BUILD_TYPE=Release && cmake --build nomadim/build -j --target nomadim_tests`
Expected: FAIL — `nomadim/oracle.hpp` not found.

- [ ] **Step 3: Create header**

Create `nomadim/include/nomadim/oracle.hpp`:
```cpp
#ifndef NOMADIM_ORACLE_HPP
#define NOMADIM_ORACLE_HPP

// Test-only brute-force dimension oracle. Enumerates linear extensions of the
// poset and finds the smallest set whose intersection is exactly the order.
// Exponential; intended only for validating analyze_dimension on small posets.
// NOT linked into the library, CLI, or WASM.
#include "nomadim/types.hpp"

namespace nomadim {

int oracle_dimension(const adjacency_list& g);

} // namespace nomadim

#endif // NOMADIM_ORACLE_HPP
```

- [ ] **Step 4: Implement**

Create `nomadim/src/oracle.cpp`:
```cpp
#include "nomadim/oracle.hpp"
#include "nomadim/order_relation.hpp"
#include <vector>
#include <functional>

namespace nomadim {
namespace {

// All linear extensions of the partial order `base`, as position vectors:
// pos[e] = rank of e. Backtracking over all topological orders.
std::vector<std::vector<int>> all_extensions(const StrictRel& base) {
    int n = base.n;
    std::vector<std::vector<int>> exts;
    std::vector<int> order;
    std::vector<char> placed(n, 0);
    std::function<void()> rec = [&]() {
        if ((int)order.size() == n) {
            std::vector<int> pos(n);
            for (int i = 0; i < n; ++i) pos[order[i]] = i;
            exts.push_back(std::move(pos));
            return;
        }
        for (int c = 0; c < n; ++c) {
            if (placed[c]) continue;
            bool minimal = true;
            for (int d = 0; d < n; ++d)
                if (!placed[d] && d != c && base.less(d, c)) { minimal = false; break; }
            if (!minimal) continue;
            placed[c] = 1; order.push_back(c);
            rec();
            order.pop_back(); placed[c] = 0;
        }
    };
    rec();
    return exts;
}

// Does the chosen subset of extensions intersect to exactly `base`?
bool realizes(const StrictRel& base, const std::vector<std::vector<int>>& exts,
              const std::vector<int>& chosen) {
    int n = base.n;
    for (int a = 0; a < n; ++a)
        for (int b = 0; b < n; ++b) {
            if (a == b) continue;
            bool in_all = true;
            for (int idx : chosen)
                if (!(exts[idx][a] < exts[idx][b])) { in_all = false; break; }
            if (in_all != base.less(a, b)) return false;
        }
    return true;
}

} // namespace

int oracle_dimension(const adjacency_list& g) {
    int n = (int)g.size();
    if (n <= 1) return n == 0 ? 0 : 1;
    StrictRel base = base_order(g);
    auto exts = all_extensions(base);
    int E = (int)exts.size();
    if (E == 1) return 1;   // total order
    // Smallest subset of extensions whose intersection is the order.
    for (int k = 1; k <= E; ++k) {
        std::vector<int> chosen(k);
        std::function<bool(int,int)> pick = [&](int start, int depth) -> bool {
            if (depth == k) return realizes(base, exts, chosen);
            for (int i = start; i <= E - (k - depth); ++i) {
                chosen[depth] = i;
                if (pick(i + 1, depth + 1)) return true;
            }
            return false;
        };
        if (pick(0, 0)) return k;
    }
    return E;
}

} // namespace nomadim
```

- [ ] **Step 5: Build + run**

Run:
```bash
cmake --build nomadim/build -j --target nomadim_tests && ./nomadim/build/nomadim_tests --gtest_filter='Oracle.*'
```
Expected: PASS. (`MatchesAnalyzeOnAllSmallDags` is the key cross-validation.)

- [ ] **Step 6: Commit**

```bash
git add nomadim/include/nomadim/oracle.hpp nomadim/src/oracle.cpp nomadim/tests/test_oracle.cpp nomadim/CMakeLists.txt
git commit -m "test(nomadim): brute-force dimension oracle cross-validates analyze_dimension"
```

---

## Task 7: `find_one_realizer` / `find_all_realizers`

Thin public realizer API over `analyze_dimension`.

**Files:**
- Modify: `nomadim/include/nomadim/realizer.hpp`
- Modify: `nomadim/src/realizer.cpp`
- Test: `nomadim/tests/test_realizer.cpp`

- [ ] **Step 1: Write the failing test**

Append to `nomadim/tests/test_realizer.cpp`:
```cpp
// Validate a general realizer: each extension is a permutation extending the
// order, and the intersection of all of them is exactly the order.
static void expect_valid_general_realizer(const adjacency_list& g,
                                          const std::vector<std::vector<int>>& realizer) {
    int n = (int)g.size();
    ASSERT_FALSE(realizer.empty());
    auto base = reach(g);
    std::vector<std::vector<int>> pos;
    for (const auto& le : realizer) {
        ASSERT_EQ((int)le.size(), n);
        std::vector<char> seen(n, 0);
        for (int x : le) { ASSERT_GE(x, 0); ASSERT_LT(x, n); ASSERT_FALSE(seen[x]); seen[x] = 1; }
        pos.push_back(positions(le));
    }
    for (int a = 0; a < n; ++a)
        for (int b = 0; b < n; ++b) {
            if (a == b) continue;
            bool in_all = true;
            for (auto& p : pos) if (!(p[a] < p[b])) { in_all = false; break; }
            EXPECT_EQ(in_all, (bool)base[(size_t)a * n + b]);
        }
}

TEST(Realizer, FindOneRealizerS3HasThreeExtensions) {
    adjacency_list s3(6); s3[0] = {4,5}; s3[1] = {3,5}; s3[2] = {3,4};
    auto r = find_one_realizer(s3, Caps{});
    EXPECT_EQ((int)r.size(), 3);
    expect_valid_general_realizer(s3, r);
}

TEST(Realizer, FindAllRealizersAreValidAndDistinct) {
    adjacency_list a3(3);   // dimension 2 antichain
    auto all = find_all_realizers(a3, Caps{});
    ASSERT_FALSE(all.empty());
    for (const auto& col : all) {
        EXPECT_EQ((int)col.realizer.size(), 2);
        expect_valid_general_realizer(a3, col.realizer);
    }
}

TEST(Realizer, FindOneRealizerChainIsSingleExtension) {
    adjacency_list chain = {{1}, {2}, {3}, {}};
    auto r = find_one_realizer(chain, Caps{});
    ASSERT_EQ((int)r.size(), 1);
    expect_valid_general_realizer(chain, r);
}
```

- [ ] **Step 2: Build, verify failure**

Run: `cmake --build nomadim/build -j --target nomadim_tests`
Expected: FAIL — `find_one_realizer` / `find_all_realizers` not declared.

- [ ] **Step 3: Declare in `realizer.hpp`**

Add to `nomadim/include/nomadim/realizer.hpp` (add `#include "nomadim/dimension.hpp"`), before the closing namespace:
```cpp
// A general realizer: `dimension` linear extensions whose intersection is the
// order. For a chain this is a single extension; for the empty poset, empty.
using GeneralRealizer = std::vector<std::vector<int>>;

// One minimum realizer (the first minimum coloring's induced extensions).
GeneralRealizer find_one_realizer(const adjacency_list& g, const Caps& caps = Caps{});

// Every minimum coloring with its induced realizer ("both, labeled"). Capped by
// caps.max_results.
std::vector<Coloring> find_all_realizers(const adjacency_list& g, const Caps& caps = Caps{});
```

- [ ] **Step 4: Implement in `realizer.cpp`**

Append to `nomadim/src/realizer.cpp` (inside `namespace nomadim`, after `find_realizer`):
```cpp
GeneralRealizer find_one_realizer(const adjacency_list& g, const Caps& caps) {
    DimensionResult dr = analyze_dimension(g, caps);
    if (dr.colorings.empty()) return {};
    return dr.colorings.front().realizer;
}

std::vector<Coloring> find_all_realizers(const adjacency_list& g, const Caps& caps) {
    return analyze_dimension(g, caps).colorings;
}
```

- [ ] **Step 5: Build + run**

Run:
```bash
cmake --build nomadim/build -j --target nomadim_tests && ./nomadim/build/nomadim_tests --gtest_filter='Realizer.*'
```
Expected: PASS (the original dim-2 `Realizer.*` tests still pass too).

- [ ] **Step 6: Commit**

```bash
git add nomadim/include/nomadim/realizer.hpp nomadim/src/realizer.cpp nomadim/tests/test_realizer.cpp
git commit -m "feat(nomadim): general find_one_realizer and find_all_realizers"
```

---

## Task 8: `meta` file format (notes / dimension / realizers + source_hash)

Extend the YAML `Document` with a cached `meta` block and a stable poset hash.

**Files:**
- Modify: `nomadim/include/nomadim/io.hpp`
- Modify: `nomadim/src/io.cpp`
- Test: `nomadim/tests/test_io.cpp`

- [ ] **Step 1: Write the failing test**

Append to `nomadim/tests/test_io.cpp` (check existing includes; ensure `#include "nomadim/io.hpp"`):
```cpp
TEST(Io, PosetHashIsStableAndOrderInsensitive) {
    adjacency_list a = {{2}, {2}, {}};
    adjacency_list b = {{2}, {2}, {}};
    EXPECT_EQ(poset_hash(a), poset_hash(b));
    adjacency_list c = {{1}, {2}, {}};
    EXPECT_NE(poset_hash(a), poset_hash(c));
}

TEST(Io, MetaRoundTrips) {
    Document d;
    Poset p; p.n_vertices = 3; p.edges = {{2}, {2}, {}};
    p.validate();
    d.poset = p;
    Meta meta;
    meta.notes = "hello world";
    meta.dimension = 2;
    meta.realizers = std::vector<std::vector<std::vector<int>>>{{{0,1,2},{1,0,2}}};
    meta.source_hash = poset_hash(p.edges);
    d.meta = meta;

    std::string text = dump_document(d);
    Document d2 = parse_document(text);
    ASSERT_TRUE(d2.meta.has_value());
    EXPECT_EQ(d2.meta->notes.value_or(""), "hello world");
    EXPECT_EQ(d2.meta->dimension.value_or(-1), 2);
    ASSERT_TRUE(d2.meta->realizers.has_value());
    EXPECT_EQ((*d2.meta->realizers)[0][1], (std::vector<int>{1,0,2}));
    EXPECT_EQ(d2.meta->source_hash.value_or(""), poset_hash(p.edges));
}

TEST(Io, NotesOnlyDocumentParses) {
    Document d = parse_document(
        "poset:\n  n_vertices: 2\n  edges:\n    - [0, 1]\n"
        "meta:\n  notes: just a note\n");
    ASSERT_TRUE(d.meta.has_value());
    EXPECT_EQ(d.meta->notes.value_or(""), "just a note");
    EXPECT_FALSE(d.meta->dimension.has_value());
}
```

- [ ] **Step 2: Build, verify failure**

Run: `cmake --build nomadim/build -j --target nomadim_tests`
Expected: FAIL — `Meta` / `poset_hash` / `dump_document` not declared.

- [ ] **Step 3: Extend `io.hpp`**

In `nomadim/include/nomadim/io.hpp`, add `#include <vector>` and inside `namespace nomadim`, before `struct Document`:
```cpp
// Cached annotations carried alongside a document. `notes` is user-authored;
// `dimension`/`realizers` are computed results, valid only while `source_hash`
// matches the current poset (else they are stale and should be recomputed).
struct Meta {
    std::optional<std::string> notes;
    std::optional<int> dimension;
    std::optional<std::vector<std::vector<std::vector<int>>>> realizers; // [realizer][extension][vertex]
    std::optional<std::string> source_hash;
};
```
Add `std::optional<Meta> meta;` as a field of `struct Document`. Then add these declarations before the closing namespace:
```cpp
// Stable order-insensitive hash (hex) of a poset's adjacency, for meta staleness.
std::string poset_hash(const adjacency_list& edges);

// Serialize a whole document (execution + poset + meta), omitting absent parts.
std::string dump_document(const Document& d);
```

- [ ] **Step 4: Implement in `io.cpp`**

In `nomadim/src/io.cpp`, add `#include <cstdint>` and `#include <set>`. Implement the hash and meta parse/emit. Add to `parse_document`, after the `poset` block and before the `if (!doc.execution && !doc.poset)` check:
```cpp
    if (root["meta"]) {
        const YAML::Node& mn = root["meta"];
        Meta meta;
        if (mn["notes"])      meta.notes = mn["notes"].as<std::string>();
        if (mn["dimension"])  meta.dimension = mn["dimension"].as<int>();
        if (mn["source_hash"]) meta.source_hash = mn["source_hash"].as<std::string>();
        if (mn["realizers"]) {
            std::vector<std::vector<std::vector<int>>> rs;
            for (const auto& r : mn["realizers"]) {
                std::vector<std::vector<int>> realizer;
                for (const auto& ext : r) {
                    std::vector<int> e;
                    for (const auto& v : ext) e.push_back(v.as<int>());
                    realizer.push_back(std::move(e));
                }
                rs.push_back(std::move(realizer));
            }
            meta.realizers = std::move(rs);
        }
        doc.meta = std::move(meta);
    }
```
And add these functions near the dump helpers:
```cpp
std::string poset_hash(const adjacency_list& edges) {
    // FNV-1a over a canonical "u>v;" edge list (each adjacency sorted), so the
    // hash depends only on the relation, not on edge ordering.
    uint64_t h = 1469598103934665603ULL;
    auto mix = [&](uint64_t x) {
        for (int b = 0; b < 8; ++b) { h ^= (x & 0xff); h *= 1099511628211ULL; x >>= 8; }
    };
    for (int u = 0; u < (int)edges.size(); ++u) {
        std::set<int> sorted(edges[u].begin(), edges[u].end());
        for (int v : sorted) { mix((uint64_t)u); mix((uint64_t)v); mix('|'); }
    }
    static const char* hex = "0123456789abcdef";
    std::string out;
    for (int s = 60; s >= 0; s -= 4) out.push_back(hex[(h >> s) & 0xf]);
    return out;
}

static void emit_meta(YAML::Emitter& out, const Meta& m) {
    out << YAML::Key << "meta" << YAML::Value << YAML::BeginMap;
    if (m.notes)       out << YAML::Key << "notes" << YAML::Value << *m.notes;
    if (m.dimension)   out << YAML::Key << "dimension" << YAML::Value << *m.dimension;
    if (m.source_hash) out << YAML::Key << "source_hash" << YAML::Value << *m.source_hash;
    if (m.realizers) {
        out << YAML::Key << "realizers" << YAML::Value << YAML::BeginSeq;
        for (const auto& realizer : *m.realizers) {
            out << YAML::BeginSeq;
            for (const auto& ext : realizer) {
                out << YAML::Flow << YAML::BeginSeq;
                for (int v : ext) out << v;
                out << YAML::EndSeq;
            }
            out << YAML::EndSeq;
        }
        out << YAML::EndSeq;
    }
    out << YAML::EndMap;
}

std::string dump_document(const Document& d) {
    YAML::Emitter out;
    out << YAML::BeginMap;
    if (d.execution) {
        out << YAML::Key << "execution" << YAML::Value << YAML::BeginMap;
        out << YAML::Key << "n_procs" << YAML::Value << d.execution->n_procs;
        out << YAML::Key << "syncs" << YAML::Value << YAML::BeginSeq;
        for (auto const& s : d.execution->syncs)
            out << YAML::Flow << YAML::BeginSeq << s.first << s.second << YAML::EndSeq;
        out << YAML::EndSeq << YAML::EndMap;
    }
    if (d.poset) {
        out << YAML::Key << "poset" << YAML::Value << YAML::BeginMap;
        out << YAML::Key << "n_vertices" << YAML::Value << d.poset->n_vertices;
        out << YAML::Key << "edges" << YAML::Value << YAML::BeginSeq;
        for (int u = 0; u < d.poset->n_vertices; ++u)
            for (int v : d.poset->edges[u])
                out << YAML::Flow << YAML::BeginSeq << u << v << YAML::EndSeq;
        out << YAML::EndSeq << YAML::EndMap;
    }
    if (d.meta) emit_meta(out, *d.meta);
    out << YAML::EndMap;
    return out.c_str();
}
```

- [ ] **Step 5: Build + run**

Run:
```bash
cmake --build nomadim/build -j --target nomadim_tests && ./nomadim/build/nomadim_tests --gtest_filter='Io.*'
```
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add nomadim/include/nomadim/io.hpp nomadim/src/io.cpp nomadim/tests/test_io.cpp
git commit -m "feat(nomadim): meta block (notes/dimension/realizers) with source_hash in YAML IO"
```

---

## Task 9: `nomadim dimension` CLI subcommand

**Files:**
- Create: `nomadim/app/cmd_dimension.hpp`
- Create: `nomadim/app/cmd_dimension.cpp`
- Modify: `nomadim/app/main.cpp`
- Modify: `nomadim/CMakeLists.txt` (add `app/cmd_dimension.cpp` to `add_executable(nomadim ...)`; add CTest cases)
- Create: `nomadim/data/poset_s4.yaml` (fixture for the CLI test)

- [ ] **Step 1: Write the failing CLI tests (CTest)**

In `nomadim/CMakeLists.txt`, after the existing `cli_check_*` tests, add:
```cmake
  add_test(NAME cli_dimension_s3
    COMMAND nomadim dimension ${CMAKE_CURRENT_SOURCE_DIR}/data/poset_s3.yaml)
  set_tests_properties(cli_dimension_s3 PROPERTIES
    PASS_REGULAR_EXPRESSION "Dimension: 3")

  add_test(NAME cli_dimension_s4_realizers
    COMMAND nomadim dimension ${CMAKE_CURRENT_SOURCE_DIR}/data/poset_s4.yaml --realizers)
  set_tests_properties(cli_dimension_s4_realizers PROPERTIES
    PASS_REGULAR_EXPRESSION "Dimension: 4")
```

Create `nomadim/data/poset_s4.yaml`:
```yaml
poset:
  n_vertices: 8
  edges:
    - [0, 5]
    - [0, 6]
    - [0, 7]
    - [1, 4]
    - [1, 6]
    - [1, 7]
    - [2, 4]
    - [2, 5]
    - [2, 7]
    - [3, 4]
    - [3, 5]
    - [3, 6]
```

- [ ] **Step 2: Build, verify failure**

Run:
```bash
cmake -S nomadim -B nomadim/build -DCMAKE_BUILD_TYPE=Release && cmake --build nomadim/build -j --target nomadim
```
Expected: FAIL — `cmd_dimension.hpp` not found / subcommand unknown.

- [ ] **Step 3: Create the command header + impl**

Create `nomadim/app/cmd_dimension.hpp`:
```cpp
#ifndef NOMADIM_CMD_DIMENSION_HPP
#define NOMADIM_CMD_DIMENSION_HPP

#include <string>

namespace nomadim {

// `nomadim dimension <file>`: report order dimension. With show_realizers, print
// one realizer; with show_all, print every minimum coloring + realizer. If
// out_path is non-empty, write the document with meta (dimension, realizers,
// source_hash) filled in, preserving any existing notes.
int cmd_dimension(const std::string& path, bool show_realizers, bool show_all,
                  int max_vertices, const std::string& out_path);

} // namespace nomadim

#endif // NOMADIM_CMD_DIMENSION_HPP
```

Create `nomadim/app/cmd_dimension.cpp`:
```cpp
#include "cmd_dimension.hpp"
#include "nomadim/io.hpp"
#include "nomadim/process_graph.hpp"
#include "nomadim/dimension.hpp"
#include "nomadim/realizer.hpp"
#include <iostream>

namespace nomadim {

namespace {
void print_realizer(const std::vector<std::vector<int>>& realizer) {
    for (size_t i = 0; i < realizer.size(); ++i) {
        std::cout << "    L" << (i + 1) << ": [";
        for (size_t j = 0; j < realizer[i].size(); ++j)
            std::cout << (j ? ", " : "") << realizer[i][j];
        std::cout << "]\n";
    }
}
} // namespace

int cmd_dimension(const std::string& path, bool show_realizers, bool show_all,
                  int max_vertices, const std::string& out_path) {
    Document d = load_file(path);
    adjacency_list adj;
    if (d.poset) adj = d.poset->edges;
    else         adj = ProcessGraph::build(*d.execution).graph;

    Caps caps; caps.max_vertices = max_vertices;
    DimensionResult dr = analyze_dimension(adj, caps);

    std::cout << "Vertices: " << adj.size() << "\n";
    std::cout << "Critical pairs: " << dr.critical_pairs.size() << "\n";
    std::cout << "Hyperedges: " << dr.hyperedges.size() << "\n";
    std::cout << "Dimension: " << dr.dimension << "\n";

    if (show_all) {
        std::cout << "Minimum colorings: " << dr.colorings.size() << "\n";
        for (size_t c = 0; c < dr.colorings.size(); ++c) {
            std::cout << "  coloring " << c << ":\n";
            print_realizer(dr.colorings[c].realizer);
        }
    } else if (show_realizers && !dr.colorings.empty()) {
        std::cout << "Realizer:\n";
        print_realizer(dr.colorings.front().realizer);
    }

    if (!out_path.empty()) {
        Document outd;
        outd.poset = d.poset;
        outd.execution = d.execution;
        Meta meta = d.meta.value_or(Meta{});      // keep existing notes
        meta.dimension = dr.dimension;
        std::vector<std::vector<std::vector<int>>> rs;
        for (const auto& col : dr.colorings) rs.push_back(col.realizer);
        meta.realizers = std::move(rs);
        meta.source_hash = poset_hash(adj);
        outd.meta = std::move(meta);
        save_file(out_path, dump_document(outd));
    }
    return 0;
}

} // namespace nomadim
```

- [ ] **Step 4: Wire into `main.cpp`**

In `nomadim/app/main.cpp`: add `#include "cmd_dimension.hpp"`. After the `convert` subcommand block, add:
```cpp
    std::string dim_path, dim_out;
    bool dim_realizers = false, dim_all = false;
    int dim_max_vertices = 16;
    auto* dim = app.add_subcommand("dimension", "Report order dimension (any >= 1), with optional realizers");
    dim->add_option("file", dim_path, "YAML poset/execution file")->required();
    dim->add_flag("--realizers", dim_realizers, "Print one realizer");
    dim->add_flag("--all", dim_all, "Print all minimum colorings + realizers");
    dim->add_option("--max-vertices", dim_max_vertices, "Vertex cap (default 16)");
    dim->add_option("-o,--out", dim_out, "Write document with computed meta to this file");
```
And in the dispatch `try { ... }` block, after the `convert` line:
```cpp
        if (*dim)
            return nomadim::cmd_dimension(dim_path, dim_realizers, dim_all,
                                          dim_max_vertices, dim_out);
```

- [ ] **Step 5: Register source, build, run CLI tests**

In `nomadim/CMakeLists.txt`, add `app/cmd_dimension.cpp` to `add_executable(nomadim app/main.cpp ...)`.

Run:
```bash
cmake -S nomadim -B nomadim/build -DCMAKE_BUILD_TYPE=Release && cmake --build nomadim/build -j --target nomadim && ctest --test-dir nomadim/build -R cli_dimension --output-on-failure
```
Expected: both `cli_dimension_s3` and `cli_dimension_s4_realizers` PASS.

- [ ] **Step 6: Commit**

```bash
git add nomadim/app/cmd_dimension.hpp nomadim/app/cmd_dimension.cpp nomadim/app/main.cpp nomadim/CMakeLists.txt nomadim/data/poset_s4.yaml
git commit -m "feat(nomadim): nomadim dimension CLI subcommand with realizers and meta output"
```

---

## Task 10: WASM bindings (dimension / realizers / hyperedges / document meta)

**Files:**
- Modify: `nomadim/src/wasm_bindings.cpp`
- Test: extend `nomadim/editor/test/wasm-client.test.mjs` (after Task 11 wires the client; here just add the C++ bindings)

> The `nomadim_wasm` target already lists `src/hypergraph.cpp` (Task 2). The WASM build is exercised end-to-end in Task 11.

- [ ] **Step 1: Add bindings**

In `nomadim/src/wasm_bindings.cpp`, add `#include "nomadim/oracle.hpp"`? No — oracle is test-only; do NOT include it. Add these helpers in the anonymous namespace (before `lib_version`):
```cpp
Caps parse_caps(const std::string& json) {
    Caps caps;
    if (json.empty()) return caps;
    YAML::Node n = YAML::Load(json);
    if (n["max_vertices"])       caps.max_vertices = n["max_vertices"].as<int>();
    if (n["max_critical_pairs"]) caps.max_critical_pairs = n["max_critical_pairs"].as<int>();
    if (n["max_results"])        caps.max_results = n["max_results"].as<int>();
    return caps;
}

std::string realizer_to_json(const std::vector<std::vector<int>>& realizer) {
    std::ostringstream os; os << '[';
    for (size_t i = 0; i < realizer.size(); ++i) { if (i) os << ','; os << ints_to_json(realizer[i]); }
    os << ']'; return os.str();
}

std::string dimension_json(const std::string& adj_json, const std::string& caps_json) {
    try {
        adjacency_list g = parse_validated_adjacency(adj_json);
        DimensionResult dr = analyze_dimension(g, parse_caps(caps_json));
        std::ostringstream os;
        os << "{\"dimension\":" << dr.dimension
           << ",\"criticalPairs\":[";
        for (size_t i = 0; i < dr.critical_pairs.size(); ++i)
            os << (i ? "," : "") << '[' << dr.critical_pairs[i].x << ',' << dr.critical_pairs[i].y << ']';
        os << "],\"hyperedges\":[";
        for (size_t i = 0; i < dr.hyperedges.size(); ++i)
            os << (i ? "," : "") << ints_to_json(dr.hyperedges[i]);
        os << "]}";
        return os.str();
    } catch (const std::exception& e) {
        return std::string("{\"error\":\"") + e.what() + "\"}";
    }
}

std::string find_one_realizer_json(const std::string& adj_json, const std::string& caps_json) {
    try {
        adjacency_list g = parse_validated_adjacency(adj_json);
        Caps caps = parse_caps(caps_json);
        DimensionResult dr = analyze_dimension(g, caps);
        std::ostringstream os;
        os << "{\"dimension\":" << dr.dimension << ",\"realizer\":"
           << (dr.colorings.empty() ? "[]" : realizer_to_json(dr.colorings.front().realizer)) << "}";
        return os.str();
    } catch (const std::exception& e) {
        return std::string("{\"error\":\"") + e.what() + "\"}";
    }
}

std::string all_realizers_json(const std::string& adj_json, const std::string& caps_json) {
    try {
        adjacency_list g = parse_validated_adjacency(adj_json);
        DimensionResult dr = analyze_dimension(g, parse_caps(caps_json));
        std::ostringstream os;
        os << "{\"dimension\":" << dr.dimension << ",\"colorings\":[";
        for (size_t c = 0; c < dr.colorings.size(); ++c) {
            if (c) os << ',';
            os << "{\"classes\":[";
            for (size_t k = 0; k < dr.colorings[c].classes.size(); ++k) {
                if (k) os << ',';
                os << '[';
                const auto& cls = dr.colorings[c].classes[k];
                for (size_t i = 0; i < cls.size(); ++i)
                    os << (i ? "," : "") << '[' << cls[i].x << ',' << cls[i].y << ']';
                os << ']';
            }
            os << "],\"realizer\":" << realizer_to_json(dr.colorings[c].realizer) << "}";
        }
        os << "]}";
        return os.str();
    } catch (const std::exception& e) {
        return std::string("{\"error\":\"") + e.what() + "\"}";
    }
}
```
Then register them in `EMSCRIPTEN_BINDINGS(nomadim_module)`:
```cpp
    emscripten::function("dimension", &dimension_json);
    emscripten::function("findOneRealizer", &find_one_realizer_json);
    emscripten::function("allRealizers", &all_realizers_json);
```
Add `#include "nomadim/hypergraph.hpp"` to the includes if not present.

- [ ] **Step 2: Document meta in `parse_document_json` / add `dump_document_json`**

Still in `nomadim/src/wasm_bindings.cpp`, extend `parse_document_json` to emit meta when present. After the `poset` block inside it, before `os << '}'`:
```cpp
    if (d.meta) {
        // parse_document guarantees execution and/or poset is present, so meta is
        // never first — always separate it with a comma.
        os << ",\"meta\":{";
        bool mfirst = true;
        auto comma = [&]{ if (!mfirst) os << ','; mfirst = false; };
        if (d.meta->notes)      { comma(); os << "\"notes\":\"" << *d.meta->notes << "\""; }
        if (d.meta->dimension)  { comma(); os << "\"dimension\":" << *d.meta->dimension; }
        if (d.meta->source_hash){ comma(); os << "\"source_hash\":\"" << *d.meta->source_hash << "\""; }
        if (d.meta->realizers) {
            comma(); os << "\"realizers\":[";
            for (size_t r = 0; r < d.meta->realizers->size(); ++r)
                os << (r ? "," : "") << realizer_to_json((*d.meta->realizers)[r]);
            os << ']';
        }
        os << '}';
    }
```
(Move the `realizer_to_json` helper above `parse_document_json` if needed.) Note: `notes` JSON-escaping is minimal here; the editor only stores plain notes — acceptable for this surface.

Add a `dump_document_json` that takes `{poset?, meta?}` JSON and returns YAML, and register `emscripten::function("dumpDocument", &dump_document_json);`:
```cpp
std::string dump_document_json(const std::string& doc_json) {
    YAML::Node n = YAML::Load(doc_json);
    Document d;
    if (n["poset"]) {
        Poset p; p.n_vertices = n["poset"]["n_vertices"].as<int>();
        p.edges.assign(p.n_vertices, {});
        const YAML::Node& edges = n["poset"]["edges"];
        for (int u = 0; u < (int)edges.size() && u < p.n_vertices; ++u)
            for (const auto& v : edges[u]) p.edges[u].push_back(v.as<int>());
        p.validate();
        d.poset = std::move(p);
    }
    if (n["meta"]) {
        Meta m;
        const YAML::Node& mn = n["meta"];
        if (mn["notes"])       m.notes = mn["notes"].as<std::string>();
        if (mn["dimension"])   m.dimension = mn["dimension"].as<int>();
        if (mn["source_hash"]) m.source_hash = mn["source_hash"].as<std::string>();
        if (mn["realizers"]) {
            std::vector<std::vector<std::vector<int>>> rs;
            for (const auto& r : mn["realizers"]) {
                std::vector<std::vector<int>> realizer;
                for (const auto& ext : r) {
                    std::vector<int> e;
                    for (const auto& v : ext) e.push_back(v.as<int>());
                    realizer.push_back(std::move(e));
                }
                rs.push_back(std::move(realizer));
            }
            m.realizers = std::move(rs);
        }
        d.meta = std::move(m);
    }
    return dump_document(d);
}
```

- [ ] **Step 3: Build the WASM module**

Run:
```bash
mise run nomadim-editor-build
```
Expected: ends with `✅ wrote .../editor/public/nomadim.js + nomadim.wasm`. (Requires the `emsdk` mise tool + network on first run.)

- [ ] **Step 4: Commit**

```bash
git add nomadim/src/wasm_bindings.cpp
git commit -m "feat(nomadim): WASM bindings for dimension, realizers, hyperedges, and document meta"
```

---

## Task 11: Editor client wrappers + WASM cross-check test

**Files:**
- Modify: `nomadim/editor/src/wasm-client.mjs`
- Modify: `nomadim/editor/test/wasm-client.test.mjs`

- [ ] **Step 1: Add the failing client test**

Append to `nomadim/editor/test/wasm-client.test.mjs` inside the existing test (or a new `test(...)` block):
```cpp
test('client exposes general dimension, realizers, and document meta', async () => {
  const c = await makeClient(factory);
  // S_3: dimension 3.
  const s3 = [[4,5],[3,5],[3,4],[],[],[]];
  const dim = c.dimension(s3);
  assert.strictEqual(dim.dimension, 3);
  assert.ok(Array.isArray(dim.hyperedges));

  const one = c.findOneRealizer(s3);
  assert.strictEqual(one.dimension, 3);
  assert.strictEqual(one.realizer.length, 3);

  const all = c.allRealizers(s3);
  assert.ok(all.colorings.length >= 1);
  assert.strictEqual(all.colorings[0].realizer.length, 3);

  // Round-trip a document with meta through dumpDocument + parseDocument.
  const yaml = c.dumpDocument({ poset: { n_vertices: 3, edges: [[2],[2],[]] },
                                meta: { notes: 'hi', dimension: 2 } });
  const parsed = c.parseDocument(yaml);
  assert.strictEqual(parsed.meta.notes, 'hi');
  assert.strictEqual(parsed.meta.dimension, 2);
});
```
(Note: the file uses `.mjs`; the `cpp` fence above is just for display — write it as JavaScript.)

- [ ] **Step 2: Extend the client**

In `nomadim/editor/src/wasm-client.mjs`, add inside the returned object:
```javascript
    dimension: (adjacency, caps) => JSON.parse(m.dimension(JSON.stringify(adjacency), caps ? JSON.stringify(caps) : '')),
    findOneRealizer: (adjacency, caps) => JSON.parse(m.findOneRealizer(JSON.stringify(adjacency), caps ? JSON.stringify(caps) : '')),
    allRealizers: (adjacency, caps) => JSON.parse(m.allRealizers(JSON.stringify(adjacency), caps ? JSON.stringify(caps) : '')),
    dumpDocument: (doc) => m.dumpDocument(JSON.stringify(doc)),
```

- [ ] **Step 3: Build WASM + run the node test**

Run:
```bash
mise run nomadim-editor-build && node --test nomadim/editor/test/wasm-client.test.mjs
```
Expected: PASS.

- [ ] **Step 4: Commit**

```bash
git add nomadim/editor/src/wasm-client.mjs nomadim/editor/test/wasm-client.test.mjs
git commit -m "feat(nomadim): editor client wrappers for dimension, realizers, and document meta"
```

---

## Task 12: Editor model + dimension shaping module

Pure JS shaping (no WASM) so it unit-tests fast, plus `meta` carried in the model.

**Files:**
- Create: `nomadim/editor/src/dimension.mjs`
- Modify: `nomadim/editor/src/model.mjs`
- Create: `nomadim/editor/test/dimension.test.mjs`
- Modify: `nomadim/editor/test/model.test.mjs`

- [ ] **Step 1: Write failing tests**

Create `nomadim/editor/test/dimension.test.mjs`:
```javascript
import test from 'node:test';
import assert from 'node:assert';
import { dimensionText, realizerLines, isMetaStale } from '../src/dimension.mjs';

test('dimensionText summarises a result', () => {
  assert.strictEqual(dimensionText({ dimension: 3, hyperedges: [[0,1,2]] }),
                     'Dimension: 3 (1 hyperedge)');
  assert.strictEqual(dimensionText({ dimension: 2, hyperedges: [[0,1],[2,3]] }),
                     'Dimension: 2 (2 hyperedges)');
  assert.strictEqual(dimensionText({ error: 'too large' }), 'Dimension: too large');
});

test('realizerLines formats extensions', () => {
  assert.deepStrictEqual(realizerLines([[0,1,2],[2,1,0]]),
                         ['L1: [0, 1, 2]', 'L2: [2, 1, 0]']);
});

test('isMetaStale compares source hashes', () => {
  assert.strictEqual(isMetaStale({ source_hash: 'abc' }, 'abc'), false);
  assert.strictEqual(isMetaStale({ source_hash: 'abc' }, 'xyz'), true);
  assert.strictEqual(isMetaStale(null, 'abc'), true);     // no meta -> stale
  assert.strictEqual(isMetaStale({}, 'abc'), true);       // no hash -> stale
});
```

Append to `nomadim/editor/test/model.test.mjs`:
```javascript
import { loadFromDocument, getMeta, setNotes } from '../src/model.mjs';

test('model carries meta from a document and updates notes', () => {
  const m = loadFromDocument({ poset: { n_vertices: 2, edges: [[1], []] },
                               meta: { notes: 'hi', dimension: 1 } });
  assert.strictEqual(getMeta(m).notes, 'hi');
  const m2 = setNotes(m, 'bye');
  assert.strictEqual(getMeta(m2).notes, 'bye');
  assert.strictEqual(getMeta(m).notes, 'hi');   // immutable update
});
```

- [ ] **Step 2: Run, verify failure**

Run:
```bash
node --test nomadim/editor/test/dimension.test.mjs nomadim/editor/test/model.test.mjs
```
Expected: FAIL — modules/exports missing.

- [ ] **Step 3: Create `dimension.mjs`**

Create `nomadim/editor/src/dimension.mjs`:
```javascript
// Pure shaping over the WASM dimension/realizer results — no WASM here.

export function dimensionText(result) {
  if (result && result.error) return `Dimension: ${result.error}`;
  const h = (result.hyperedges || []).length;
  const plural = h === 1 ? 'hyperedge' : 'hyperedges';
  return `Dimension: ${result.dimension} (${h} ${plural})`;
}

export function realizerLines(realizer) {
  return (realizer || []).map((ext, i) => `L${i + 1}: [${ext.join(', ')}]`);
}

// A cached meta block is stale unless its source_hash matches the current poset.
export function isMetaStale(meta, currentHash) {
  return !meta || !meta.source_hash || meta.source_hash !== currentHash;
}
```

- [ ] **Step 4: Extend `model.mjs`**

Replace the body of `nomadim/editor/src/model.mjs` `emptyModel`/`loadFromDocument` and add helpers:
```javascript
export function emptyModel() {
  return { poset: null, execution: null, meta: null };
}

// doc: parseDocument output { execution?, poset?, meta? }
export function loadFromDocument(doc) {
  return { poset: doc.poset ?? null, execution: doc.execution ?? null, meta: doc.meta ?? null };
}

export function getMeta(model) {
  return model.meta ?? {};
}

// Immutable note update (preserves other meta fields).
export function setNotes(model, notes) {
  return { ...model, meta: { ...(model.meta ?? {}), notes } };
}
```
Keep the existing `posetAdjacency` and `hasPoset` functions unchanged.

- [ ] **Step 5: Run tests**

Run:
```bash
node --test nomadim/editor/test/dimension.test.mjs nomadim/editor/test/model.test.mjs
```
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add nomadim/editor/src/dimension.mjs nomadim/editor/src/model.mjs nomadim/editor/test/dimension.test.mjs nomadim/editor/test/model.test.mjs
git commit -m "feat(nomadim): editor dimension shaping module and model meta support"
```

---

## Task 13: Editor UI — dimension panel, realizers list, notes; persist meta on save

**Files:**
- Modify: `nomadim/editor/index.html`
- Modify: `nomadim/editor/src/app.mjs`
- Modify: `nomadim/editor/src/yaml-sync.mjs`
- Create: `nomadim/editor/e2e/dimension.spec.mjs`

- [ ] **Step 1: Write the failing e2e test**

Create `nomadim/editor/e2e/dimension.spec.mjs` (follow the pattern of `e2e/app.spec.mjs` — inspect it for the base URL / server fixture and mirror it):
```javascript
import { test, expect } from '@playwright/test';

test('shows dimension 3 and a 3-extension realizer for S_3', async ({ page }) => {
  await page.goto('/index.html');
  await page.waitForFunction(() => window.__editor !== undefined);
  await page.evaluate(() => window.__editor.loadText(
    'poset:\n  n_vertices: 6\n  edges:\n' +
    '    - [0, 4]\n    - [0, 5]\n    - [1, 3]\n    - [1, 5]\n    - [2, 3]\n    - [2, 4]\n'));
  await expect.poll(() => page.evaluate(() => window.__editor.dimensionText()))
    .toContain('Dimension: 3');
  const lines = await page.evaluate(() => window.__editor.realizerLineCount());
  expect(lines).toBe(3);
});

test('notes round-trip into saved YAML', async ({ page }) => {
  await page.goto('/index.html');
  await page.waitForFunction(() => window.__editor !== undefined);
  await page.evaluate(() => window.__editor.newPoset());
  await page.evaluate(() => window.__editor.setNotes('my note'));
  const yaml = await page.evaluate(() => window.__editor.currentYaml());
  expect(yaml).toContain('my note');
});
```

- [ ] **Step 2: Run, verify failure**

Run:
```bash
mise run nomadim-editor-e2e -- dimension.spec.mjs
```
Expected: FAIL — `window.__editor.dimensionText` not defined / panel missing.

- [ ] **Step 3: Add HTML elements**

In `nomadim/editor/index.html`, replace the `<div id="realizer"></div>` line with:
```html
  <div id="dimension"></div>
  <div id="realizer"></div>
  <div id="realizers-all"></div>
  <div id="notes-bar"><label>Notes <input id="notes" type="text" placeholder="notes / comments" size="40" /></label></div>
```

- [ ] **Step 4: Wire the panel in `app.mjs`**

In `nomadim/editor/src/app.mjs`:
- Update imports:
```javascript
import { emptyModel, hasPoset, posetAdjacency, getMeta, setNotes } from './model.mjs';
import { dimensionText, realizerLines, isMetaStale } from './dimension.mjs';
```
- Add `'dimension'`, `'realizers-all'`, `'notes'` to the `ids` array.
- Replace `renderRealizer(adj)` with a general renderer:
```javascript
  function renderDimension(adj) {
    const result = client.dimension(adj);
    els.dimension.textContent = dimensionText(result);
    if (result.error) { els.realizer.textContent = ''; els['realizers-all'].textContent = ''; return; }
    const one = client.findOneRealizer(adj);
    els.realizer.textContent = one.error ? '' : 'realizer  ' + realizerLines(one.realizer).join('   ');
    const all = client.allRealizers(adj);
    els['realizers-all'].textContent = all.error ? ''
      : `${all.colorings.length} minimum realizer(s)`;
  }
```
- In `refresh()`, in the `v === 'poset' && model.poset` branch, replace the `renderRealizer(adj);` call with `renderDimension(adj);` and set the notes input: `els.notes.value = getMeta(model).notes ?? '';`.
- Add a notes change handler near the other listeners:
```javascript
  els.notes.addEventListener('input', () => { model = setNotes(model, els.notes.value); });
```
- Expose test hooks in `window.__editor`:
```javascript
    dimensionText: () => els.dimension.textContent,
    realizerLineCount: () => (els.realizer.textContent.match(/L\d+:/g) || []).length,
    setNotes: (s) => { els.notes.value = s; els.notes.dispatchEvent(new Event('input')); },
```

- [ ] **Step 5: Persist meta on save via `yaml-sync.mjs`**

In `nomadim/editor/src/yaml-sync.mjs`, change `modelToYaml` so a poset model serializes through `dumpDocument` with meta:
```javascript
export function modelToYaml(client, model) {
  if (model.poset) {
    const meta = { ...(model.meta ?? {}) };
    return client.dumpDocument({ poset: model.poset, meta });
  }
  if (model.execution) return client.dumpExecution(model.execution);
  return '';
}
```
Then in `app.mjs`, make `currentYaml()` use `modelToYaml(client, model)` for the poset case so saved/displayed YAML includes notes. (Import `modelToYaml` from `./yaml-sync.mjs` and replace the poset branch of `currentYaml()` with `return modelToYaml(client, model);` when `model.poset` is set.)

- [ ] **Step 6: Build + run e2e + full editor test suite**

Run:
```bash
mise run nomadim-editor-e2e -- dimension.spec.mjs
node --test nomadim/editor/test/*.test.mjs
```
Expected: the two new e2e tests PASS; existing editor unit tests still PASS.

- [ ] **Step 7: Commit**

```bash
git add nomadim/editor/index.html nomadim/editor/src/app.mjs nomadim/editor/src/yaml-sync.mjs nomadim/editor/e2e/dimension.spec.mjs
git commit -m "feat(nomadim): editor dimension panel, realizers list, and notes persistence"
```

---

## Task 14: Full regression + docs

**Files:**
- Modify: `nomadim/README.md`
- Modify: `docs/INDEX.md` (if it indexes nomadim; otherwise skip)

- [ ] **Step 1: Run the full native suite**

Run:
```bash
mise run nomadim-test
```
Expected: all CTest cases PASS (unit + CLI + golden default tier).

- [ ] **Step 2: Run the editor suites**

Run:
```bash
mise run nomadim-editor-test
```
Expected: WASM builds; node faithfulness + unit tests PASS.

- [ ] **Step 3: Update the README**

In `nomadim/README.md`:
- Update the opening summary to mention general dimension (not just ≤ 2), realizers, and the editor.
- Under "Usage", add:
```bash
# Report order dimension (any >= 1); optionally print realizers, write meta.
nomadim dimension poset.yaml [--realizers] [--all] [--max-vertices N] [-o out.yaml]
```
- Under "File format (YAML)", document the `meta` block:
```yaml
meta:
  notes: "free text"
  dimension: 3
  source_hash: "…"        # cache key; results are recomputed if it no longer matches
  realizers:
    - - [0, 1, 2, 3]
      - [3, 2, 1, 0]
      - [2, 0, 3, 1]
```

- [ ] **Step 4: Commit**

```bash
git add nomadim/README.md docs/INDEX.md
git commit -m "docs(nomadim): document general dimension, realizers, and the meta file format"
```

- [ ] **Step 5: Request code review**

Use the superpowers:requesting-code-review skill (or `/code-review`) on the branch before merge.

---

## Self-review notes (for the executor)

- **Performance:** `StandardExampleS4` (8 vertices, 12 critical pairs) and the all-DAGs oracle test (n ≤ 4) are the heaviest. If `enumerate_min_colorings` is slow on S4, it is bounded by `Caps.max_results`; the dimension number itself comes from `chromatic_number` (first solution only) and is fast.
- **Correctness anchor:** Task 6's oracle cross-check is the ground truth. If `analyze_dimension` ever disagrees, treat it as a real bug (use superpowers:systematic-debugging) — do not weaken the oracle.
- **Caps consistency:** every cap breach throws `std::runtime_error`; WASM wrappers convert it to `{error}`; the editor surfaces it via `dimensionText`.
- **Back-compat:** the dim-2 `find_realizer`, `isDim2`, `criticalPairs`, and `dumpPoset` bindings are untouched, so existing tests/UI keep working.
