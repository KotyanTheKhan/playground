# nomadim

C++ port of the [NomaDimension](https://github.com/DePizzottri/NomaDimension)
poset dimension-2 tooling: a `libnomadim` core plus a `nomadim` CLI that
reads/writes posets as YAML, checks whether a poset has order dimension ≤ 2, and
enumerates non-isomorphic dimension-2 executions of *N* processes.

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

```bash
cmake -S nomadim -B nomadim/build -DCMAKE_BUILD_TYPE=Release
cmake --build nomadim/build -j
ctest --test-dir nomadim/build --output-on-failure
```

Heavier golden-count enumerations are off by default; enable with
`-DNOMADIM_SLOW_TESTS=ON` (re-configure and rebuild).

## Usage

```bash
# Report whether a poset/execution has dimension <= 2 (exit 0 = yes, 2 = no).
nomadim check poset.yaml

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
