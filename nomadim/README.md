# nomadim

C++ port of the [NomaDimension](https://github.com/DePizzottri/NomaDimension)
poset dimension tooling: a `libnomadim` core plus a `nomadim` CLI that
reads/writes posets as YAML, checks whether a poset has order dimension ≤ 2,
computes the **general order dimension** (any ≥ 1) by coloring the hypergraph of
critical pairs, finds **realizers** (one or all minimum realizers), and
enumerates non-isomorphic dimension-2 executions of *N* processes. A browser
editor (`editor/`, WASM core) visualizes posets, dimension, and realizers.

This project builds with CMake and is **independent of the repository's Coq/dune
build** (the `.claude/scripts/timed-build.sh` wrapper does not apply here).

## Background

An *execution* is `N` processes plus an ordered list of synchronization events,
each a pair of process indices. It expands into an event-structure DAG (each
process is a chain of events; each sync joins the current last events of two
processes), whose reachability relation is the happened-before poset. A poset has
order dimension ≤ 2 **iff** the incompatibility graph of its critical pairs is
bipartite — the test implemented here (Floyd transitive closure → critical pairs
→ bipartiteness).

## Prerequisites

- CMake ≥ 3.16 and a C++17 compiler.
- Network access at configure time (CMake fetches the dependencies below).

Dependencies are fetched automatically via CMake `FetchContent` — **nothing to
install manually**:

- [yaml-cpp](https://github.com/jbeder/yaml-cpp) — YAML I/O
- [CLI11](https://github.com/CLIUtils/CLI11) — argument parsing
- [GoogleTest](https://github.com/google/googletest) — tests

There is **no Boost dependency**.

## Build & test

With mise (recommended — provides a pinned CMake):

```bash
mise run nomadim-test          # configure + build + run tests
mise run nomadim-build         # configure + build only
mise run nomadim-test-slow     # include the heavy golden-count tier
mise run nomadim-clean         # remove build dirs
mise run nomadim-deps          # show toolchain versions
```

(`mise install` provisions the pinned CMake on first use; it needs network
access. If it is unavailable, the tasks fall back to the system `cmake`.)

Or directly with CMake:

```bash
cmake -S nomadim -B nomadim/build -DCMAKE_BUILD_TYPE=Release
cmake --build nomadim/build -j
ctest --test-dir nomadim/build --output-on-failure
```

Heavier golden-count enumerations are off by default; enable with
`-DNOMADIM_SLOW_TESTS=ON` (re-configure and rebuild).

## Benchmarks

Performance benchmarks (Google Benchmark) guard against regressions:

```bash
mise run nomadim-bench            # build + run benchmarks, fail if slower than baseline
mise run nomadim-bench-baseline   # regenerate nomadim/bench/baseline.json
```

`nomadim-bench` compares the median `real_time` of each benchmark against the
committed `nomadim/bench/baseline.json` and exits nonzero if any is more than 25%
slower (`python3 nomadim/bench/compare.py --threshold` to adjust). Benchmarks
cover `is_dim2` (micro, stable) and `enumerate` at several N/K (single-threaded
and parallel). **Run on an idle machine** — background load skews absolute
timings. Regenerate the baseline after an intentional performance change.

## Usage

```bash
# Report whether a poset/execution has dimension <= 2 (exit 0 = yes, 2 = no).
nomadim check poset.yaml

# Report order dimension (any >= 1); optionally print realizers, write meta.
nomadim dimension poset.yaml [--realizers] [--all] [--max-vertices N] [-o out.yaml]

# Enumerate non-isomorphic, fully-synchronized, dimension-2 executions of N
# processes using up to K syncs, on J worker threads (default: all cores).
nomadim enumerate -n 4 -k 5 [-j 8] [-o results.yaml]

# Expand an execution document into the equivalent poset document.
nomadim convert exec.yaml poset.yaml
```

## File format (YAML)

A document contains an `execution` table, a `poset` table, or both.

Execution document:
```yaml
execution:
  n_procs: 4
  syncs:
    - [0, 1]
    - [1, 2]
    - [2, 3]
    - [0, 2]
```

General poset document (edge `[u, v]` means `u` is below `v`; the reachability
closure is the partial order):
```yaml
poset:
  n_vertices: 5
  edges:
    - [0, 2]
    - [1, 2]
    - [2, 4]
```

A document may also carry a `meta` block. `notes` is free user-authored text;
`dimension`/`realizers` are cached computed results keyed by `source_hash` (a
hash of the poset edges) — they are recomputed if the hash no longer matches the
poset, so they are never trusted blindly:
```yaml
meta:
  notes: "free text"
  dimension: 3
  source_hash: "…"
  realizers:
    - - [0, 1, 2, 3]
      - [3, 2, 1, 0]
      - [2, 0, 3, 1]
```

## Concurrency

`enumerate` uses a fine-grained `std::thread` work-pool: a shared task deque of
search nodes; workers pop tasks and queue shallow children / inline deep ones,
with duplicates pruned via a sharded canonical-sync-name cache before queuing so
distinct subtrees spread across cores. Results are deduplicated by isomorphism
(bucketed by a cheap invariant). The reported count is deterministic regardless
of `-j`.

> The original used `boost::fiber` work-stealing. That was tried and dropped:
> its work-stealing scheduler crashes (SIGBUS) when created/destroyed across
> repeated calls on this platform, and a per-branch round-robin fallback gets no
> speedup because the problem's symmetry collapses the first level. The
> `std::thread` pool gives real multicore speedup with no extra dependency.

## Layout

```
nomadim/
  CMakeLists.txt
  include/nomadim/   public library headers
  src/               libnomadim implementation
  app/               the nomadim CLI (main + cmd_check/enumerate/convert)
  tests/             GoogleTest unit + golden-count tests
  data/              sample YAML fixtures
```

## Golden reference counts

Number of non-isomorphic, fully-synchronized, dimension-2 executions (from the
upstream project), asserted by the tests:

| N | K | count | tier |
|---|---|-------|------|
| 2 | 2–8 | 1 | default |
| 3 | 3 / 4 / 5 / 6 | 2 / 6 / 12 / 20 | default |
| 4 | 5 / 6 / 7 | 10 / 102 / 634 | default |
| 5 | 7 | 40 | default |
| 4 | 8 | 3058 | slow |
| 5 | 8 | 704 | slow |
| 4 | 9 | 12784 | reference only (too heavy to run automatically) |
| 6 | 9 | 1036 | reference only (too heavy to run automatically) |
