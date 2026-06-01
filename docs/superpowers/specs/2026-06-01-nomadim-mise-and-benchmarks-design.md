# nomadim: mise Tasks + Performance Benchmarks — Design

**Date:** 2026-06-01
**Status:** Approved (design)
**Builds on:** `2026-06-01-nomadimension-cpp-port-design.md` (the C++ port itself).

## 1. Purpose

Two additions to the existing `nomadim/` C++ subproject:

1. **Drive all build and dependency tasks through mise**, matching how the rest
   of the (Coq) repo is operated, so a fresh checkout can build/test/benchmark
   nomadim entirely via `mise run …`.
2. **Add performance benchmarks** with a committed baseline and a regression
   gate, so changes can be checked for performance degradation or improvement.

No library or CLI behavior changes — this is build tooling plus benchmarks.

## 2. Decisions (from brainstorming)

| Decision | Choice |
|----------|--------|
| Benchmark framework | Google Benchmark (via CMake FetchContent) |
| Regression handling | Compare current vs committed baseline; **nonzero exit** when slower than a threshold |
| CMake provisioning | Pin `cmake` in mise `[tools]` (compiler stays system) |
| Default regression threshold | 25% slower on median `real_time` (overridable) |
| Bench build location | Dedicated `nomadim/build-bench/` (gitignored) |

## 3. CMake via mise

Add to `mise.toml` `[tools]`:

```toml
cmake = "3.31.6"
```

The C++ compiler remains the system toolchain (Apple clang / gcc); mise does not
manage it. yaml-cpp, CLI11, GoogleTest, and Google Benchmark are fetched by CMake
`FetchContent` — there is nothing else to install.

## 4. mise tasks

A `nomadim-*` task family is added to `mise.toml`. These wrap CMake/CTest so that
"all build and dependency tasks go through mise". They do **not** use the Coq
`opam exec` wrapper (the C++ build is independent of opam/dune).

| Task | Behavior |
|------|----------|
| `nomadim-deps` | Print `cmake --version` and the C++ compiler version; confirm tooling is present. C++ libraries are auto-fetched by CMake, so there is no separate install step. |
| `nomadim-configure` | `cmake -S nomadim -B nomadim/build -DCMAKE_BUILD_TYPE=Release` |
| `nomadim-build` | Configure if needed, then `cmake --build nomadim/build -j` |
| `nomadim-test` | `nomadim-build` then `ctest --test-dir nomadim/build --output-on-failure` (default tier) |
| `nomadim-test-slow` | Configure `nomadim/build` with `-DNOMADIM_SLOW_TESTS=ON`, build, `ctest` |
| `nomadim-clean` | Remove `nomadim/build` and `nomadim/build-bench` |
| `nomadim-bench` | Configure/build `nomadim/build-bench` with `-DNOMADIM_BENCH=ON`, run the benchmark binary (3 repetitions, aggregates only, JSON out), then run `compare.py` against the committed baseline. Exits nonzero on regression. |
| `nomadim-bench-baseline` | Same build+run, but writes the result to `nomadim/bench/baseline.json` (overwrites the committed baseline). |

`mise.toml` task naming follows the existing convention (kebab-case, a
`description`, a `run` script). Tasks use plain `bash` with `set -e`.

## 5. Performance benchmarks

### 5.1 Source — `nomadim/bench/bench_nomadim.cpp`

Registers the following Google Benchmark cases:

**Micro (stable, low variance — Google Benchmark auto-iterates):**
- `dim2_canonical` — `is_dim2` on the canonical 4-process execution graph
  (`{0,1},{1,2},{2,3},{0,2}` → 16 vertices).
- `dim2_s3` — `is_dim2` on the standard example S₃.

These run in microseconds, so Google Benchmark executes many iterations and
reports a stable median — ideal for catching dimension-algorithm regressions.

**Macro (realistic; explicit `->Iterations(1)->Unit(kMillisecond)->UseRealTime()` — one enumerate per measurement; the stable median comes from the 3 outer `--benchmark_repetitions`, so each macro case runs 3 times, not 9):**
- `enumerate_4_6_j1` — `enumerate(4, 6, 1)`
- `enumerate_4_7_j1` — `enumerate(4, 7, 1)`
- `enumerate_5_7_j1` — `enumerate(5, 7, 1)`
- `enumerate_4_7_par` — `enumerate(4, 7, hardware_concurrency())`

Single-threaded cases are the stable algorithm metric; the `_par` case tracks
parallel scaling. The very heavy cases (`4,9`, `6,9`) are excluded — too slow for
a routine benchmark.

Each macro case asserts the known count inside the benchmark body (e.g. via
`benchmark::DoNotOptimize` plus a `if (r.count != expected) state.SkipWithError(...)`)
so a benchmark that silently breaks correctness is flagged, not silently timed.

### 5.2 CMake integration

- New option `option(NOMADIM_BENCH "Build performance benchmarks" OFF)`.
- When `ON`: `FetchContent` Google Benchmark (pinned tag, tests disabled), and add
  an executable `nomadim_bench` from `bench/bench_nomadim.cpp` linking
  `nomadim_core` and `benchmark::benchmark`.
- Default builds (`NOMADIM_BENCH=OFF`) do not fetch Google Benchmark.

### 5.3 Baseline + comparison

- `nomadim/bench/baseline.json` — committed Google Benchmark JSON output
  (`--benchmark_report_aggregates_only=true` with `--benchmark_repetitions=3`,
  so each case has a `_median` aggregate). Generated on this machine via
  `nomadim-bench-baseline`.
- `nomadim/bench/compare.py` — a self-contained Python 3 script (standard library
  only). Inputs: baseline JSON, current JSON, optional `--threshold` (fraction,
  default `0.25`) and `--metric` (default `real_time`). It matches benchmarks by
  name using the `_median` aggregate, computes `delta = (cur - base) / base` for
  each, prints a table (name, baseline, current, %Δ, verdict), and **exits 1** if
  any benchmark's `delta > threshold`; exits 0 otherwise. Benchmarks present in
  one file but not the other are reported as warnings (not failures).

### 5.4 Caveat

Absolute timings are sensitive to machine load (background apps/games can
saturate cores). Benchmarks should be run on an otherwise-idle machine. The
generous default threshold (25%) and the inclusion of low-variance micro
benchmarks reduce false positives; `compare.py --threshold` can be raised for
noisy environments.

## 6. Files

```
mise.toml                        # + [tools] cmake; + nomadim-* tasks
nomadim/CMakeLists.txt           # + NOMADIM_BENCH option, FetchContent Benchmark, nomadim_bench target
nomadim/bench/bench_nomadim.cpp  # Google Benchmark cases
nomadim/bench/compare.py         # baseline-vs-current comparison + regression gate
nomadim/bench/baseline.json      # committed baseline (generated on this machine)
nomadim/.gitignore               # + build-bench/
nomadim/README.md                # lead with mise tasks; document benchmarks
CLAUDE.md                        # update the C++ subproject note to use mise tasks
```

## 7. Out of scope

- No changes to library/CLI behavior or algorithms.
- No CI wiring (the gate is available via `mise run nomadim-bench`; hooking it
  into any CI system is a separate task).
- mise does not manage the C++ compiler.
