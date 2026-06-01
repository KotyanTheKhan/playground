# NomaDimension C++ Port — Design

**Date:** 2026-06-01
**Status:** Approved (design)

## 1. Purpose

Port the [NomaDimension](https://github.com/DePizzottri/NomaDimension) program
complex into this repository as a refactored, restructured set of C++ utilities
and libraries. The original enumerates distributed executions of *N* processes
of a special shape and checks whether the resulting happened-before poset has
dimension ≤ 2.

The ported program is a single multi-command CLI plus a reusable core library
that can:

- **read/write posets from file** (YAML),
- **check** an offered poset/execution for dimension 2, and
- **run enumeration** of dimension-2 executions parametrized by *N* (number of
  processes).

The faithful C++ port keeps the original algorithms; restructuring is limited to
clean module boundaries, a real file format, tests, and a reproducible build.
Out of scope (cut from the original): the grouped generators
(`enumerate_grouped`, `generate_one_grouped`), the flat-grid generator
(`generate_flat_grid`), and the dead-code sandbox (`common.cpp`).

## 2. Background — what the original does

- **Domain model.** An *execution* is `N` processes plus an ordered list of
  synchronization pairs `(p1, p2)`. Building it produces an event-structure DAG:
  each process is a chain of event vertices; each `sync(p1, p2)` inserts a meet
  vertex joining the current last vertices of `p1` and `p2` and spawns two new
  last vertices. The DAG's reachability relation is the happened-before poset.
- **Dimension-2 test** (`is_poset_2_dimensional`):
  1. Build adjacency matrix; compute transitive closure via Floyd–Warshall.
  2. Find **critical pairs**: ordered incomparable pairs `(v, u)` (both
     directions `INF`) such that forcing the edge `v→u` does not collapse any
     *other* previously-incomparable pair (`check_if_critical`).
  3. Build the **incompatibility graph** on critical pairs: pairs `i, j` are
     adjacent iff reversing both (adding both back-edges) creates a cycle.
  4. The poset has dimension ≤ 2 **iff** that incompatibility graph is
     bipartite.
- **Enumeration** (`enumerate_isomorphic`): recursively extend an execution by
  every sync pair, pruning by a canonical *sorted sync-name* hash cache; when an
  execution is fully synchronized, test dimension 2 and collect it if it is not
  isomorphic to a previously found result. Parallelized with boost::fiber
  work-stealing over `hardware_concurrency()` threads.

## 3. Decisions (from brainstorming)

| Decision | Choice |
|----------|--------|
| Language | C++ (faithful port) |
| File format | YAML, supporting **both** an `execution` document and a general `poset` document |
| CLI shape | Single multi-command binary (`nomadim <subcommand>`) |
| Scope | **check** dimension-2 + **enumerate by N** (isomorphic). Grouped and flat-grid generators dropped. |
| Concurrency | Multithreaded **and** multifibered (boost::fiber work-stealing, as upstream) |
| Testing | GoogleTest + golden regression data |
| Location | New top-level `nomadim/` directory, independent of the Coq/dune build |
| Dependencies | CMake `FetchContent` for yaml-cpp + GoogleTest + CLI11; `find_package(Boost REQUIRED fiber context)` |

## 4. Architecture

```
nomadim/
  CMakeLists.txt
  README.md
  include/nomadim/   *.hpp   (public library headers)
  src/               *.cpp   (library impl)
  app/               main.cpp + subcommand handlers (the `nomadim` binary)
  tests/             *.cpp   (GoogleTest unit + golden regression)
  data/              *.yaml  (fixtures: sample executions/posets + golden enumerations)
```

One core static library `libnomadim`, one CLI binary `nomadim`, one test
executable. CMake build with CTest integration. The C++ build is wholly separate
from the repository's Coq/dune build (the `.claude/scripts/timed-build.sh`
wrapper applies to Coq only).

## 5. Core library components

Each component is a focused unit: a clear job, a small header interface, and
internals that can change without breaking consumers.

- **`execution`** — `Execution { int n_procs; std::vector<std::pair<int,int>> syncs; }`.
  The compact, hand-writable model and the round-trip unit of enumeration.
- **`process_graph`** — faithful port of upstream `ProcessesGraph`: builds the
  event-structure DAG from an `Execution` via `init`/`sync`, tracking `graph`
  (adjacency list), `labels`, `proc_verteces`, `proc_last_vertex`, `network`,
  and the `proc_sync_name` canonical hash (`PEHash`).
- **`poset`** — general `Poset { int n_vertices; adjacency_list edges; }`, plus
  `Poset from(const ProcessGraph&)`.
- **`floyd`** — Floyd–Warshall transitive closure and `floyd_advance_vertex`,
  plus `make_graph_matrix`. Ported verbatim.
- **`dimension`** — `find_critical_pairs`, `check_if_critical`,
  `check_critical_pairs_graph`, and the public `is_dim2(...)`; with `have_cycle`
  and `is_bipartite` helpers. The headline algorithm.
- **`isomorphism`** — `is_isomorphic`, `generate_all_isomorphic`, and sync-name
  canonicalization (sorted `proc_sync_name`).
- **`enumerate`** — the multithreaded + multifibered work-stealing enumerator
  (boost::fiber), with the sorted-sync-name cache for pruning. Returns the set of
  non-isomorphic, fully-synchronized, dim-2 executions and the isomorphic-hit
  count. Parameters: `N` (processes), optional `K` (max sync count), and
  `threads` (worker-thread count, default `hardware_concurrency()`; `1` =
  single-threaded). Results are deduplicated to be deterministic regardless of
  thread count.
- **`io`** — YAML load/save for both schemas via yaml-cpp; validation lives here
  and in the constructors it feeds.

## 6. YAML schema (both documents supported)

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

General-poset document (edge `[u, v]` means `u` is below `v`; reachability gives
the order):

```yaml
poset:
  n_vertices: 5
  edges:
    - [0, 2]
    - [1, 2]
    - [2, 4]
```

A file may contain either top-level key (or both). `check` accepts either.
`convert` reads an `execution` and emits the expanded `poset` document, and can
additionally pretty-print the verbose vertex/label adjacency listing in the
upstream style.

## 7. CLI surface (single binary)

```
nomadim check <file.yaml>                  # report dim<=2 (yes/no) + critical pairs
nomadim enumerate -n N [-k K] [-j THREADS] # non-iso fully-synced dim-2 executions; YAML + count
nomadim convert <in.yaml> <out.yaml>       # execution -> expanded poset
```

Argument parsing via CLI11. Exit codes: `0` success; nonzero for parse,
validation, or usage errors. `enumerate` writes the found executions as YAML
(execution documents) and prints the count summary; `-k` defaults to a value
matched to `N` if omitted (documented in `--help`).

`-j` / `--threads THREADS` sets the number of worker threads for the
boost::fiber work-stealing enumerator. It defaults to
`std::thread::hardware_concurrency()`; a value of `1` runs single-threaded
(useful for deterministic debugging). The value is validated to be `>= 1`.

## 8. Data flow

- **check**: `io::load` → either (`Execution` → `ProcessGraph` → adjacency) or
  (`Poset` → adjacency) → `floyd` transitive closure → `find_critical_pairs` →
  incompatibility graph → bipartite test → report verdict + critical pairs.
- **enumerate**: `(N, K)` → recursive sync expansion with sorted sync-name cache
  pruning across fibers/threads → on full synchronization, dim-2 test and
  isomorphism dedup → collect results → emit YAML + counts.
- **convert**: `io::load` execution → `ProcessGraph` → `Poset::from` → `io::save`
  poset.

## 9. Error handling & validation

The following produce a clear diagnostic and a nonzero exit code:

- YAML parse failures.
- `n_procs <= 0`, or `n_vertices < 0`.
- Sync/edge endpoints out of range or otherwise malformed (non-pair, negative).
- A sync pairing a process with itself.
- Cyclic edges in a `poset` document (the cover/adjacency relation must be a
  DAG).
- CLI misuse (unknown subcommand, missing required option) — prints usage/help.

## 10. Testing (GoogleTest + golden data)

**Unit tests**

- `floyd`: transitive closure correctness on small fixed graphs.
- `dimension`: critical-pair detection and bipartiteness on hand-checked posets;
  positive cases (a chain; a single-sync execution) and negative cases (the
  upstream hardcoded `0-1, 1-2, 2-3, 0-2` execution, which is NOT dim-2; the
  standard example S_3). Expectations verified against the upstream binary as an
  oracle.
- `isomorphism`: positive and negative isomorphism cases; `generate_all_isomorphic`
  cardinality.
- `io`: YAML round-trip (`load ∘ save == identity`) for both schemas; validation
  rejects each malformed-input class from §9.

**Golden regression** — the enumerator must reproduce these upstream counts of
non-isomorphic, fully-synchronized, dim-2 executions (full reference table):

| N | K | expected count | tier |
|---|---|----------------|------|
| 2 | 2–8 | 1 | default |
| 3 | 3 / 4 / 5 / 6 | 2 / 6 / 12 / 20 | default |
| 4 | 5 / 6 | 10 / 102 | default |
| 4 | 7 | 634 | default |
| 5 | 7 | 40 | default |
| 4 | 8 | 3058 | slow |
| 4 | 9 | 12784 | slow |
| 5 | 8 | 704 | slow |
| 6 | 9 | 1036 | slow |

The `default` tier runs in every test invocation. The `slow` tier (the
heaviest enumerations) is gated behind a `NOMADIM_SLOW_TESTS` CMake option so
the default test run stays fast. All counts are asserted exactly when their tier
is enabled.

**End-to-end** — CTest invokes the `nomadim` binary on `data/` fixtures:
`check` on a known dim-2 file (expect YES verdict), `check` on non-dim-2 files
(S_3 and the canonical execution, expect NO), and an `enumerate -n 4 -k 5` run
asserting the count line.

## 11. Out of scope / future

- Grouped and flat-grid generators (can be re-added as subcommands later).
- Any connection to the repository's Coq `posets/dimension` theory (e.g.
  extraction-based cross-checking) — noted as a possible future tie-in, not part
  of this port.
