# nomadim: Comprehensive Per-Function Unit Tests — Design

**Date:** 2026-06-01
**Status:** Approved (design)
**Builds on:** the `nomadim/` C++ port and its existing GoogleTest suite.

## 1. Purpose

Raise unit-test coverage so that **every public function** of the `nomadim`
library is directly verified — normal cases, edge cases, and error paths — rather
than only exercised transitively. Add file-I/O round-trip tests and tests for the
`bench/compare.py` regression gate. Remove one piece of dead code that cannot be
meaningfully tested.

## 2. Decisions (from brainstorming)

| Decision | Choice |
|----------|--------|
| Coverage depth | Exhaustive public API + file I/O + `compare.py` |
| Internals (private/static helpers) | Test indirectly via the public API; do not expose internals |
| Dead code | Remove the unused private `ProcessGraph::add_vertex_to_proc` |
| Expected values | Pin dimension/enumeration numbers to the upstream-oracle-verified values already established |
| Organization | Extend the existing per-module `tests/test_*.cpp`; add `tests/test_compare.py` wired into CTest |

## 3. Approach

- One `TEST(Suite, Behavior)` per behavior, GoogleTest, deterministic (no timing
  assertions; heavy enumerations stay in the gated golden tier).
- Reuse known fixtures: the canonical 4-process execution
  (`{0,1},{1,2},{2,3},{0,2}}`), the standard example S₃, chains, antichains.
- Dimension internals use oracle-verified counts: canonical execution → 25
  critical pairs and NOT dim-2; S₃ → 3 critical pairs and NOT dim-2; chain → 0
  critical pairs and dim-2; antichain of 3 → 6 critical pairs and dim-2.
- File I/O tests use `<filesystem>` temp paths and clean up after themselves.

## 4. Per-module coverage

### floyd (`tests/test_floyd.cpp`)
- `make_graph_matrix`: diagonal 0, each edge 1, all other entries `INF`, row-major
  layout, for a small fixed adjacency list.
- `floyd`: chain (cumulative distances), disconnected components (stay `INF`),
  self-loop tolerated, single vertex, and a diamond (shortest of two paths).
- `floyd_advance_vertex`: on an un-closed matrix with a manually added edge,
  relaxing through one vertex updates exactly the paths through it (direct test —
  previously untested).

### process_graph (`tests/test_process_graph.cpp`)
- After `init(n)`: `proc_num`, one vertex per process, `labels[i] == {i,0}`,
  `proc_verteces[i] == {i}`, `proc_last_vertex[i] == i`, empty `network`,
  `proc_sync_name` sized `n`.
- After one `sync(a,b)`: vertex count +3; the meet vertex has the two successors;
  `proc_last_vertex` updated; `labels` of the new per-process vertices increment
  `num`; `network[a]` contains `b` and vice-versa; `proc_sync_name[a]` and
  `[b]` each gain one char; `syncs` records the pair.
- `build(e)` produces the same `graph`, `labels`, and `syncs` as a manual
  `init`+`sync` replay.

### dimension (`tests/test_dimension.cpp`)
- `have_cycle`: empty graph (false), single node no edge (false), self-loop
  (true), disconnected with one cyclic component (true), DAG (false).
- `is_bipartite`: empty (true), single node (true), even cycle (true), odd cycle
  / triangle (false), disconnected mixed.
- `check_if_critical`: on the canonical execution's closed matrix, assert a known
  critical pair returns true and a non-critical incomparable pair returns false
  (values taken from the oracle).
- `find_critical_pairs`: counts pinned — canonical execution → 25, S₃ → 3,
  chain(4) → 0, antichain(3) → 6.
- `check_critical_pairs_graph`: bipartite incompatibility graph → true; the S₃
  case → false.
- `is_dim2`: keep existing positive/negative cases.

### isomorphism (`tests/test_isomorphism.cpp`)
- `canonical_sync_name`: equal for two executions related by a process
  permutation; sorted (non-decreasing); differs for path vs star (direct test —
  previously untested).
- `generate_all_isomorphic`: size `== n!` for n=3 and n=4.
- `is_isomorphic`: reflexive; false for differing `proc_num`; false for differing
  graph sizes; keep existing path-vs-star negative.

### enumerate (`tests/test_enumerate.cpp`)
- `is_full_synchronized`: a single-sync 2-process execution → true; a 4-process
  graph with an isolated process → false (direct test — previously untested).
- `enumerate` extras: `results.size() == count`; `isomorphic_hits >= 0`;
  `enumerate(2,1,1).count == 1`; thread-invariance on a second config
  (`enumerate(3,5,1).count == enumerate(3,5,4).count`).
- Keep the existing golden default tier and the gated slow tier.

### execution (`tests/test_execution.cpp`)
- Empty `syncs` with `n_procs >= 1` validates.
- Negative endpoint rejected (in addition to the existing out-of-range/self-sync).

### poset (`tests/test_poset.cpp`)
- Empty poset (`n_vertices == 0`, no edges) validates.
- `edges.size() != n_vertices` rejected.
- A self-loop edge (`[v, v]`) is rejected (it is a 1-cycle).
- `from(ProcessGraph)`: `n_vertices` and `edges` equal the source graph.

### io (`tests/test_io.cpp`)
- `save_file` then `load_file` round-trips an execution document and a poset
  document through a real temporary file (`<filesystem>`), then deletes it.
- `load_file` on a nonexistent path throws `std::runtime_error`.

### types
- `version()` non-empty — already covered by the smoke test.

## 5. compare.py tests (`tests/test_compare.py`)

A stdlib `unittest` module that writes tiny Google-Benchmark-shaped JSON files
(only the fields `compare.py` reads: `benchmarks[]` with `run_name`,
`aggregate_name == "median"`, `real_time`) to temp files and invokes
`compare.py` as a subprocess, asserting:

1. Identical baseline/current → exit 0, prints `OK`.
2. A benchmark 2× slower → exit 1, prints `REGRESSION`.
3. A benchmark within threshold (e.g. +10% at default 25%) → exit 0.
4. A baseline benchmark absent from current → exit 1 (`MISSING`).

Wired into CTest:

```cmake
find_package(Python3 COMPONENTS Interpreter)
if(Python3_Interpreter_FOUND)
  add_test(NAME compare_py
    COMMAND ${Python3_EXECUTABLE} -m unittest discover -s
            ${CMAKE_CURRENT_SOURCE_DIR}/tests -p "test_compare.py")
endif()
```

The test locates the script deterministically relative to its own file:
`Path(__file__).resolve().parent.parent / "bench" / "compare.py"` (tests/ →
nomadim/ → bench/compare.py), so it needs no env var and works regardless of the
CTest working directory.

## 6. Dead code removal

`ProcessGraph::add_vertex_to_proc` (private) is never called (the port's `sync`
builds the meet structure directly). Remove the declaration
(`include/nomadim/process_graph.hpp`) and definition (`src/process_graph.cpp`).
The full suite must still pass after removal.

## 7. Files

```
nomadim/tests/test_floyd.cpp           # MODIFY (+ make_graph_matrix, floyd cases, floyd_advance_vertex)
nomadim/tests/test_process_graph.cpp   # MODIFY (+ bookkeeping assertions)
nomadim/tests/test_dimension.cpp       # MODIFY (+ helpers edge cases, check_if_critical, find_critical_pairs)
nomadim/tests/test_isomorphism.cpp     # MODIFY (+ canonical_sync_name, cardinality, negatives)
nomadim/tests/test_enumerate.cpp       # MODIFY (+ is_full_synchronized, enumerate invariants)
nomadim/tests/test_execution.cpp       # MODIFY (+ empty/negative cases)
nomadim/tests/test_poset.cpp           # MODIFY (+ empty/mismatch/self-loop/from)
nomadim/tests/test_io.cpp              # MODIFY (+ file round-trip, nonexistent file)
nomadim/tests/test_compare.py          # CREATE (compare.py gate tests)
nomadim/CMakeLists.txt                 # MODIFY (+ compare_py CTest via Python3)
nomadim/include/nomadim/process_graph.hpp  # MODIFY (remove add_vertex_to_proc decl)
nomadim/src/process_graph.cpp          # MODIFY (remove add_vertex_to_proc def)
```

## 8. Out of scope

- No production-code behavior changes beyond removing the dead helper.
- No performance/timing assertions (covered by the benchmark gate).
- The heavy enumeration counts (4,9 / 6,9) remain documented reference values,
  not run.
