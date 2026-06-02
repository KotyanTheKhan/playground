# nomadim mise Tasks + Performance Benchmarks Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Drive all nomadim build/dependency tasks through mise, and add Google Benchmark performance benchmarks with a committed baseline and a regression gate.

**Architecture:** Add `cmake` to mise `[tools]` and a `nomadim-*` task family wrapping CMake/CTest. Add an optional `NOMADIM_BENCH` CMake target (Google Benchmark via FetchContent) plus a stdlib-only Python compare script that fails when a benchmark regresses past a threshold versus a committed baseline JSON.

**Tech Stack:** mise, CMake, Google Benchmark (FetchContent), Python 3 (stdlib), C++17.

---

## File Structure

```
mise.toml                        # + [tools] cmake; + nomadim-* tasks (MODIFY)
nomadim/CMakeLists.txt           # + NOMADIM_BENCH option/target (MODIFY)
nomadim/bench/bench_nomadim.cpp  # Google Benchmark cases (CREATE)
nomadim/bench/compare.py         # baseline-vs-current regression gate (CREATE)
nomadim/bench/baseline.json      # committed baseline, generated on this machine (CREATE)
nomadim/.gitignore               # + build-bench/ (MODIFY)
nomadim/README.md                # lead with mise tasks; document benchmarks (MODIFY)
CLAUDE.md                        # C++ subproject note -> mise tasks (MODIFY)
```

These are independent of the Coq/dune build; the `nomadim-*` mise tasks do NOT use `opam exec`.

---

## Task 1: mise tasks for build/test/clean (cmake via mise)

**Files:**
- Modify: `mise.toml`

- [ ] **Step 1: Pin cmake in `[tools]`** — in `mise.toml`, add `cmake` to the existing `[tools]` table so it reads:

```toml
[tools]
opam   = "2.4.1"
ocaml  = "5.1.0"
cmake  = "3.31.12"
```

- [ ] **Step 2: Install the new tool**

Run: `mise install`
Expected: mise installs cmake 3.31.12 (downloads the cmake plugin + binary). On success, `mise exec -- cmake --version` prints `cmake version 3.31.12`.

- [ ] **Step 3: Add the build/test/clean/deps tasks** — append these tasks to `mise.toml` (after the existing tasks; the exact location does not matter):

```toml
# ============================================================================
# nomadim (C++ subproject) — independent of the Coq/dune build
# ============================================================================

[tasks.nomadim-deps]
description = "Show the C++ toolchain for the nomadim subproject"
run = '''
#!/usr/bin/env bash
set -euo pipefail
echo "cmake:    $(cmake --version | head -1)"
echo "compiler: $(c++ --version | head -1)"
echo "(yaml-cpp, CLI11, GoogleTest, Google Benchmark are fetched by CMake — nothing to install)"
'''

[tasks.nomadim-configure]
description = "Configure the nomadim CMake build (Release)"
run = "cmake -S nomadim -B nomadim/build -DCMAKE_BUILD_TYPE=Release"

[tasks.nomadim-build]
description = "Build the nomadim C++ project"
run = '''
#!/usr/bin/env bash
set -euo pipefail
cmake -S nomadim -B nomadim/build -DCMAKE_BUILD_TYPE=Release
cmake --build nomadim/build -j
'''

[tasks.nomadim-test]
description = "Build and run nomadim tests (default tier)"
run = '''
#!/usr/bin/env bash
set -euo pipefail
cmake -S nomadim -B nomadim/build -DCMAKE_BUILD_TYPE=Release
cmake --build nomadim/build -j
ctest --test-dir nomadim/build --output-on-failure
'''

[tasks.nomadim-test-slow]
description = "Build and run nomadim tests including the heavy golden-count tier"
run = '''
#!/usr/bin/env bash
set -euo pipefail
cmake -S nomadim -B nomadim/build -DCMAKE_BUILD_TYPE=Release -DNOMADIM_SLOW_TESTS=ON
cmake --build nomadim/build -j
ctest --test-dir nomadim/build --output-on-failure
'''

[tasks.nomadim-clean]
description = "Remove nomadim CMake build directories"
run = "rm -rf nomadim/build nomadim/build-bench && echo '✅ nomadim build dirs removed'"
```

- [ ] **Step 4: Verify the build task works through mise**

Run: `mise run nomadim-deps`
Expected: prints `cmake version 3.31.12` and a compiler line, exit 0.

Run: `mise run nomadim-test`
Expected: configures, builds, and ctest reports `100% tests passed` (38 tests), exit 0.

- [ ] **Step 5: Commit**

```bash
git add mise.toml
git commit -m "build(nomadim): drive build/test via mise tasks; pin cmake in [tools]"
```

---

## Task 2: Benchmark target (Google Benchmark) + benchmark source

**Files:**
- Modify: `nomadim/CMakeLists.txt`
- Create: `nomadim/bench/bench_nomadim.cpp`

- [ ] **Step 1: Add the `NOMADIM_BENCH` option** — in `nomadim/CMakeLists.txt`, directly after the existing `option(NOMADIM_SLOW_TESTS ...)` line, add:

```cmake
option(NOMADIM_BENCH "Build performance benchmarks (fetches Google Benchmark)" OFF)
```

- [ ] **Step 2: Add the benchmark target** — append to the END of `nomadim/CMakeLists.txt`:

```cmake
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
```

- [ ] **Step 3: Write the benchmark source** — `nomadim/bench/bench_nomadim.cpp`

```cpp
#include <benchmark/benchmark.h>

#include "nomadim/enumerate.hpp"
#include "nomadim/process_graph.hpp"
#include "nomadim/execution.hpp"
#include "nomadim/dimension.hpp"
#include "nomadim/types.hpp"

#include <thread>
#include <algorithm>

using namespace nomadim;

static adjacency_list canonical_graph() {
    return ProcessGraph::build(Execution{4, {{0,1},{1,2},{2,3},{0,2}}}).graph;
}

static adjacency_list s3_graph() {
    adjacency_list s3(6);
    s3[0] = {4, 5};
    s3[1] = {3, 5};
    s3[2] = {3, 4};
    return s3;
}

// --- Micro: is_dim2 (stable, auto-iterated) ---

static void dim2_canonical(benchmark::State& state) {
    adjacency_list g = canonical_graph();
    for (auto _ : state) {
        bool r = is_dim2(g);
        benchmark::DoNotOptimize(r);
    }
}
BENCHMARK(dim2_canonical);

static void dim2_s3(benchmark::State& state) {
    adjacency_list g = s3_graph();
    for (auto _ : state) {
        bool r = is_dim2(g);
        benchmark::DoNotOptimize(r);
    }
}
BENCHMARK(dim2_s3);

// --- Macro: enumerate (one run per measurement; median from --benchmark_repetitions) ---

static void run_enum(benchmark::State& state, int n, int k, unsigned j, int expected) {
    for (auto _ : state) {
        EnumerateResult r = enumerate(n, k, j);
        benchmark::DoNotOptimize(r.count);
        if (r.count != expected)
            state.SkipWithError("unexpected enumerate count");
    }
}

static void enumerate_4_6_j1(benchmark::State& s) { run_enum(s, 4, 6, 1, 102); }
BENCHMARK(enumerate_4_6_j1)->Iterations(1)->Unit(benchmark::kMillisecond)->UseRealTime();

static void enumerate_4_7_j1(benchmark::State& s) { run_enum(s, 4, 7, 1, 634); }
BENCHMARK(enumerate_4_7_j1)->Iterations(1)->Unit(benchmark::kMillisecond)->UseRealTime();

static void enumerate_5_7_j1(benchmark::State& s) { run_enum(s, 5, 7, 1, 40); }
BENCHMARK(enumerate_5_7_j1)->Iterations(1)->Unit(benchmark::kMillisecond)->UseRealTime();

static void enumerate_4_7_par(benchmark::State& s) {
    unsigned j = std::max(2u, std::thread::hardware_concurrency());
    run_enum(s, 4, 7, j, 634);
}
BENCHMARK(enumerate_4_7_par)->Iterations(1)->Unit(benchmark::kMillisecond)->UseRealTime();

BENCHMARK_MAIN();
```

- [ ] **Step 4: Build the benchmark target and run it once**

Run:
```bash
cmake -S nomadim -B nomadim/build-bench -DCMAKE_BUILD_TYPE=Release -DNOMADIM_BENCH=ON
cmake --build nomadim/build-bench -j --target nomadim_bench
./nomadim/build-bench/nomadim_bench --benchmark_min_time=1x
```
Expected: configures (fetches Google Benchmark v1.9.1), builds `nomadim_bench`, and runs printing a table with rows `dim2_canonical`, `dim2_s3`, `enumerate_4_6_j1`, `enumerate_4_7_j1`, `enumerate_5_7_j1`, `enumerate_4_7_par`. No `unexpected enumerate count` errors. (Run on an idle machine; the enumerate rows take a few seconds each.)

- [ ] **Step 5: Commit**

```bash
git add nomadim/CMakeLists.txt nomadim/bench/bench_nomadim.cpp
git commit -m "feat(nomadim): Google Benchmark performance benchmarks (opt-in NOMADIM_BENCH)"
```

---

## Task 3: Comparison script, baseline, and bench mise tasks

**Files:**
- Create: `nomadim/bench/compare.py`
- Create: `nomadim/bench/baseline.json` (generated)
- Modify: `mise.toml`

- [ ] **Step 1: Write the comparison script** — `nomadim/bench/compare.py`

```python
#!/usr/bin/env python3
"""Compare two Google Benchmark JSON outputs and gate on regression.

Usage: compare.py BASELINE.json CURRENT.json [--threshold 0.25] [--metric real_time]

Matches benchmarks by run_name using the median aggregate (produced by
--benchmark_repetitions=N --benchmark_report_aggregates_only=true). Exits 1 if any
benchmark's current metric exceeds baseline by more than the threshold fraction.
"""
import sys
import json
import argparse


def load_medians(path, metric):
    with open(path) as f:
        data = json.load(f)
    out = {}
    for b in data.get("benchmarks", []):
        if b.get("aggregate_name") == "median":
            out[b["run_name"]] = float(b[metric])
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("baseline")
    ap.add_argument("current")
    ap.add_argument("--threshold", type=float, default=0.25,
                    help="max allowed slowdown as a fraction (default 0.25 = 25%%)")
    ap.add_argument("--metric", default="real_time")
    args = ap.parse_args()

    base = load_medians(args.baseline, args.metric)
    cur = load_medians(args.current, args.metric)
    names = sorted(set(base) | set(cur))

    print("{:<28} {:>14} {:>14} {:>9}  {}".format(
        "benchmark", "baseline", "current", "delta", "verdict"))
    regressions = []
    for n in names:
        if n not in base:
            print("{:<28} {:>14} {:>14.1f} {:>9}  warn".format(n, "-", cur[n], "NEW"))
            continue
        if n not in cur:
            print("{:<28} {:>14.1f} {:>14} {:>9}  warn".format(n, base[n], "-", "MISSING"))
            continue
        b, c = base[n], cur[n]
        delta = (c - b) / b if b else 0.0
        verdict = "ok"
        if delta > args.threshold:
            verdict = "REGRESSION"
            regressions.append(n)
        elif delta < -args.threshold:
            verdict = "faster"
        print("{:<28} {:>14.1f} {:>14.1f} {:>+8.1f}%  {}".format(n, b, c, delta * 100, verdict))

    if regressions:
        print("\nFAIL: {} regression(s) over {:.0f}%: {}".format(
            len(regressions), args.threshold * 100, ", ".join(regressions)))
        return 1
    print("\nOK: no regression over {:.0f}% threshold".format(args.threshold * 100))
    return 0


if __name__ == "__main__":
    sys.exit(main())
```

- [ ] **Step 2: Generate the baseline** (the `nomadim_bench` binary from Task 2 exists)

Run:
```bash
./nomadim/build-bench/nomadim_bench \
  --benchmark_repetitions=3 \
  --benchmark_report_aggregates_only=true \
  --benchmark_format=json \
  --benchmark_out=nomadim/bench/baseline.json \
  --benchmark_out_format=json
```
Expected: writes `nomadim/bench/baseline.json` containing a `benchmarks` array with `*_median` aggregates for all six benchmarks. (Run on an idle machine so the baseline is representative.)

- [ ] **Step 3: Verify the script passes against itself**

Run: `python3 nomadim/bench/compare.py nomadim/bench/baseline.json nomadim/bench/baseline.json`
Expected: prints the table with every verdict `ok` and a final `OK: no regression over 25% threshold`, exit 0.

- [ ] **Step 4: Verify the script fails on a synthetic regression**

Run:
```bash
python3 - <<'PY'
import json
d = json.load(open("nomadim/bench/baseline.json"))
for b in d["benchmarks"]:
    if b.get("aggregate_name") == "median":
        b["real_time"] *= 2.0   # pretend everything got 2x slower
json.dump(d, open("/tmp/bench_regressed.json", "w"))
PY
python3 nomadim/bench/compare.py nomadim/bench/baseline.json /tmp/bench_regressed.json; echo "exit=$?"
```
Expected: every row shows `+100.0%  REGRESSION`, a `FAIL: ... regression(s)` line, and `exit=1`.

- [ ] **Step 5: Add the bench mise tasks** — append to `mise.toml`:

```toml
[tasks.nomadim-bench]
description = "Run nomadim benchmarks and compare to the committed baseline (fails on regression)"
run = '''
#!/usr/bin/env bash
set -euo pipefail
cmake -S nomadim -B nomadim/build-bench -DCMAKE_BUILD_TYPE=Release -DNOMADIM_BENCH=ON
cmake --build nomadim/build-bench -j --target nomadim_bench
./nomadim/build-bench/nomadim_bench \
  --benchmark_repetitions=3 \
  --benchmark_report_aggregates_only=true \
  --benchmark_format=json \
  --benchmark_out=nomadim/build-bench/bench_current.json \
  --benchmark_out_format=json
python3 nomadim/bench/compare.py nomadim/bench/baseline.json nomadim/build-bench/bench_current.json
'''

[tasks.nomadim-bench-baseline]
description = "Regenerate the committed nomadim benchmark baseline"
run = '''
#!/usr/bin/env bash
set -euo pipefail
cmake -S nomadim -B nomadim/build-bench -DCMAKE_BUILD_TYPE=Release -DNOMADIM_BENCH=ON
cmake --build nomadim/build-bench -j --target nomadim_bench
./nomadim/build-bench/nomadim_bench \
  --benchmark_repetitions=3 \
  --benchmark_report_aggregates_only=true \
  --benchmark_format=json \
  --benchmark_out=nomadim/bench/baseline.json \
  --benchmark_out_format=json
echo "✅ baseline written to nomadim/bench/baseline.json"
'''
```

- [ ] **Step 6: Verify `mise run nomadim-bench` passes against the just-generated baseline**

Run: `mise run nomadim-bench`
Expected: builds, runs the benchmarks, prints the comparison table, ends `OK: no regression over 25% threshold`, exit 0. (Because current ≈ baseline. Minor noise stays well under 25%.)

- [ ] **Step 7: Commit**

```bash
git add nomadim/bench/compare.py nomadim/bench/baseline.json mise.toml
git commit -m "feat(nomadim): benchmark baseline + compare.py regression gate + mise bench tasks"
```

---

## Task 4: gitignore + documentation

**Files:**
- Modify: `nomadim/.gitignore`
- Modify: `nomadim/README.md`
- Modify: `CLAUDE.md`

- [ ] **Step 1: Ignore the bench build dir** — set `nomadim/.gitignore` to exactly:

```
build/
build-slow/
build-bench/
```

- [ ] **Step 2: Verify the build dirs are not tracked**

Run: `git status --porcelain nomadim | grep -E 'build(-bench|-slow)?/' || echo "clean"`
Expected: prints `clean` (no build directories staged or untracked-and-listed).

- [ ] **Step 3: Update `nomadim/README.md`** — replace the existing "## Build & test" section body so it leads with mise, and add a "## Benchmarks" section. Specifically, replace the fenced block under `## Build & test` with:

````markdown
With mise (recommended — provides a pinned CMake):

```bash
mise run nomadim-test          # configure + build + run tests
mise run nomadim-build         # configure + build only
mise run nomadim-test-slow     # include the heavy golden-count tier
mise run nomadim-clean         # remove build dirs
mise run nomadim-deps          # show toolchain versions
```

Or directly with CMake:

```bash
cmake -S nomadim -B nomadim/build -DCMAKE_BUILD_TYPE=Release
cmake --build nomadim/build -j
ctest --test-dir nomadim/build --output-on-failure
```
````

Then add this new section immediately before the `## File format (YAML)` section:

````markdown
## Benchmarks

Performance benchmarks (Google Benchmark) guard against regressions:

```bash
mise run nomadim-bench            # build + run benchmarks, fail if slower than baseline
mise run nomadim-bench-baseline   # regenerate nomadim/bench/baseline.json
```

`nomadim-bench` compares the median `real_time` of each benchmark against the
committed `nomadim/bench/baseline.json` and exits nonzero if any is more than 25%
slower (`nomadim/bench/compare.py --threshold` to adjust). Benchmarks cover
`is_dim2` (micro, stable) and `enumerate` at several N/K (single-threaded and
parallel). **Run on an idle machine** — background load skews absolute timings.
Regenerate the baseline after an intentional performance change.
````

- [ ] **Step 4: Update the C++ note in `CLAUDE.md`** — replace the fenced command block under the "### C++ subproject (`nomadim/`)" heading with:

````markdown
Build and test it through mise (which provides a pinned CMake):

```
mise run nomadim-test        # configure + build + run tests
mise run nomadim-test-slow   # include the heavy golden-count tier
mise run nomadim-bench       # run benchmarks, fail on >25% regression vs baseline
mise run nomadim-clean       # remove build dirs
```
````

- [ ] **Step 5: Final verification — tests and benches both green via mise**

Run: `mise run nomadim-test`
Expected: `100% tests passed` (38 tests), exit 0.

Run: `mise run nomadim-bench`
Expected: comparison table, `OK: no regression over 25% threshold`, exit 0.

- [ ] **Step 6: Commit**

```bash
git add nomadim/.gitignore nomadim/README.md CLAUDE.md
git commit -m "docs(nomadim): lead with mise tasks; document benchmarks; ignore build-bench/"
```

---

## Self-Review Notes

- **Spec coverage:** cmake in `[tools]` (Task 1), nomadim-deps/configure/build/test/test-slow/clean (Task 1), NOMADIM_BENCH option + Google Benchmark target + bench source with the spec's six cases (Task 2), compare.py with median/threshold/nonzero-exit + baseline.json + nomadim-bench/nomadim-bench-baseline (Task 3), build-bench gitignore + README/CLAUDE doc updates leading with mise (Task 4). Caveat about machine-load noise is in the README (Task 4 Step 3). All spec sections map to a task.
- **Placeholder scan:** none — all code (CMake, C++, Python, TOML) and commands are complete.
- **Type/name consistency:** the benchmark `run_name`s emitted by Google Benchmark (`dim2_canonical`, `dim2_s3`, `enumerate_4_6_j1`, `enumerate_4_7_j1`, `enumerate_5_7_j1`, `enumerate_4_7_par`) are matched by `compare.py` via the `median` aggregate; `enumerate(int,int,unsigned)` and `is_dim2(adjacency_list)` and `EnumerateResult.count` match the existing library API; expected counts (102/634/40) match the committed golden values.
- **Known noise risk:** absolute enumerate timings vary with machine load; mitigated by the 25% threshold, the stable `is_dim2` micro-benchmarks, and the documented "run on an idle machine" guidance. Not a correctness issue.
