# nomadim editor — WASM core (Phase 2a) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Compile libnomadim to a WebAssembly module via Emscripten with an Embind/JSON bridge exposing the editor's needed operations, and prove it stays faithful to the native CLI with a headless Node test harness.

**Architecture:** A new `src/wasm_bindings.cpp` exposes a small set of string-in/string-out functions (JSON at the boundary; YAML for documents) over the existing library. A `NOMADIM_WASM` CMake option builds a *reduced* module (no CLI/tests/bench, no `std::thread` sources) that links yaml-cpp. A shell script drives `emcmake`, and three mise tasks (build / test / clean) provision Emscripten via the pinned `emsdk` tool. A Node `node:test` harness loads the module and cross-checks `isDim2`, `expandExecution`, and YAML round-trips against the native `nomadim` CLI used as an oracle. No browser UI yet — that is Phase 2b.

**Tech Stack:** C++17, Emscripten/Embind (provisioned via mise `emsdk@4.0.23`), CMake (existing `nomadim/CMakeLists.txt`), yaml-cpp, Node ≥ 22 (`node --test`, provisioned via mise `node@22`), mise tasks.

**Branch:** `nomadim-editor` (already checked out; Phase 1 `find_realizer` already merged here).

**Spec:** `docs/superpowers/specs/2026-06-01-nomadim-poset-editor-design.md` §1 (WASM boundary table), §4–6. This plan delivers the WASM boundary + build + faithfulness tests. The Cytoscape UI, YAML panel, File System Access API, and the browser-opening `nomadim-editor` serve task are **Phase 2b** (a later plan).

---

## Important execution notes

- **First build downloads ~1 GB.** `mise run nomadim-editor-build` installs the pinned `emsdk` (LLVM/clang/binaryen) on first use and emcmake fetches+builds yaml-cpp for wasm. Allow a long timeout (≥ 1200 s) on the first build task; subsequent builds are fast.
- Build/test ONLY through the mise tasks defined here (or `build-wasm.sh`). Do NOT use the repo's `timed-build.sh` (that is for the Coq build).
- Commit messages must NOT contain any AI watermark or `Co-Authored-By` line.

---

## File structure

| File | Responsibility |
|------|----------------|
| `nomadim/src/wasm_bindings.cpp` | Embind module: JSON/YAML string bridge over io/dimension/realizer/process_graph. Compiled only under `-DNOMADIM_WASM=ON`. |
| `nomadim/CMakeLists.txt` | Add `NOMADIM_WASM` option; under it build only the reduced `nomadim_wasm` target; otherwise the existing native build (unchanged behaviour). |
| `nomadim/editor/build-wasm.sh` | Drives `emcmake cmake` + build, copies `nomadim.js`/`nomadim.wasm` to `editor/public/`. |
| `nomadim/editor/test/faithfulness.test.cjs` | Node `node:test` harness cross-checking the WASM module vs the native CLI on the `data/` fixtures + known cases. |
| `nomadim/editor/README.md` | How to build/test the editor WASM core; notes the UI is Phase 2b. |
| `nomadim/.gitignore` | Ignore the generated `editor/public/nomadim.{js,wasm}` and `build-wasm/`. |
| `mise.toml` | Add `nomadim-editor-build`, `nomadim-editor-test`, `nomadim-editor-clean` tasks (with task-scoped `emsdk`/`node` tools). |
| `docs/INDEX.md` | One line noting the WASM module + its JS API. |

### WASM JS API (what `wasm_bindings.cpp` exposes)

All functions take/return `std::string`. Adjacency is JSON array-of-arrays in **adjacency form** (`edges[u]` = list of `v` with `u < v`), identical to `Poset::edges`. Documents cross the boundary as JSON; YAML only appears in `parseDocument` input and `dump*` output.

| JS call | Input | Output |
|---------|-------|--------|
| `isDim2(adjJson)` | `"[[1],[2],[]]"` | `bool` |
| `findRealizer(adjJson)` | adjacency JSON | `{"dim_le_2":bool,"l1":[int],"l2":[int]}` JSON |
| `criticalPairs(adjJson)` | adjacency JSON | `[[x,y],...]` JSON |
| `expandExecution(execJson)` | `{"n_procs":n,"syncs":[[a,b],...]}` | `{"n_vertices":n,"edges":[[...]]}` JSON |
| `parseDocument(yamlText)` | YAML text | `{"execution":{...}?,"poset":{...}?}` JSON |
| `dumpPoset(posetJson)` | `{"n_vertices":n,"edges":[[...]]}` | YAML text |
| `dumpExecution(execJson)` | `{"n_procs":n,"syncs":[[a,b],...]}` | YAML text |
| `version()` | — | library version string |

---

### Task 1: WASM bindings + CMake `NOMADIM_WASM` build

**Files:**
- Create: `nomadim/src/wasm_bindings.cpp`
- Modify: `nomadim/CMakeLists.txt` (full replacement given below)
- Create: `nomadim/editor/build-wasm.sh`

- [ ] **Step 1: Write the Embind bindings**

Create `nomadim/src/wasm_bindings.cpp`:

```cpp
// WebAssembly bindings for libnomadim (compiled only under -DNOMADIM_WASM=ON).
// String-in/string-out bridge: JSON at the boundary, YAML for documents. yaml-cpp
// parses JSON (a YAML subset) for inputs; outputs are emitted by hand.
#include <emscripten/bind.h>
#include "nomadim/io.hpp"
#include "nomadim/poset.hpp"
#include "nomadim/execution.hpp"
#include "nomadim/process_graph.hpp"
#include "nomadim/dimension.hpp"
#include "nomadim/realizer.hpp"
#include "nomadim/floyd.hpp"
#include "nomadim/types.hpp"
#include <yaml-cpp/yaml.h>
#include <sstream>
#include <string>
#include <vector>

using namespace nomadim;

namespace {

adjacency_list parse_adjacency(const std::string& json) {
    YAML::Node n = YAML::Load(json);
    adjacency_list g;
    for (const auto& row : n) {
        std::vector<int> succ;
        for (const auto& v : row) succ.push_back(v.as<int>());
        g.push_back(std::move(succ));
    }
    return g;
}

std::string ints_to_json(const std::vector<int>& xs) {
    std::ostringstream os;
    os << '[';
    for (size_t i = 0; i < xs.size(); ++i) { if (i) os << ','; os << xs[i]; }
    os << ']';
    return os.str();
}

std::string adjacency_to_json(const adjacency_list& g) {
    std::ostringstream os;
    os << '[';
    for (size_t i = 0; i < g.size(); ++i) { if (i) os << ','; os << ints_to_json(g[i]); }
    os << ']';
    return os.str();
}

Execution parse_execution(const YAML::Node& n) {
    Execution e;
    e.n_procs = n["n_procs"].as<int>();
    if (n["syncs"])
        for (const auto& s : n["syncs"]) e.syncs.push_back({s[0].as<int>(), s[1].as<int>()});
    e.validate();
    return e;
}

std::string syncs_to_json(const std::vector<std::pair<int,int>>& syncs) {
    std::ostringstream os;
    os << '[';
    for (size_t i = 0; i < syncs.size(); ++i) {
        if (i) os << ',';
        os << '[' << syncs[i].first << ',' << syncs[i].second << ']';
    }
    os << ']';
    return os.str();
}

bool is_dim2_json(const std::string& adj_json) {
    return is_dim2(parse_adjacency(adj_json));
}

std::string find_realizer_json(const std::string& adj_json) {
    Realizer r = find_realizer(parse_adjacency(adj_json));
    std::ostringstream os;
    os << "{\"dim_le_2\":" << (r.dim_le_2 ? "true" : "false")
       << ",\"l1\":" << ints_to_json(r.l1)
       << ",\"l2\":" << ints_to_json(r.l2) << "}";
    return os.str();
}

std::string critical_pairs_json(const std::string& adj_json) {
    adjacency_list g = parse_adjacency(adj_json);
    int n = (int)g.size();
    std::vector<int> m = make_graph_matrix(g);
    auto cps = find_critical_pairs(m.data(), n);
    std::ostringstream os;
    os << '[';
    for (size_t i = 0; i < cps.size(); ++i) {
        if (i) os << ',';
        os << '[' << cps[i].x << ',' << cps[i].y << ']';
    }
    os << ']';
    return os.str();
}

std::string expand_execution_json(const std::string& exec_json) {
    Execution e = parse_execution(YAML::Load(exec_json));
    ProcessGraph g = ProcessGraph::build(e);
    Poset p = Poset::from(g);
    std::ostringstream os;
    os << "{\"n_vertices\":" << p.n_vertices
       << ",\"edges\":" << adjacency_to_json(p.edges) << "}";
    return os.str();
}

std::string parse_document_json(const std::string& text) {
    Document d = parse_document(text);
    std::ostringstream os;
    os << '{';
    bool first = true;
    if (d.execution) {
        os << "\"execution\":{\"n_procs\":" << d.execution->n_procs
           << ",\"syncs\":" << syncs_to_json(d.execution->syncs) << "}";
        first = false;
    }
    if (d.poset) {
        if (!first) os << ',';
        os << "\"poset\":{\"n_vertices\":" << d.poset->n_vertices
           << ",\"edges\":" << adjacency_to_json(d.poset->edges) << "}";
    }
    os << '}';
    return os.str();
}

std::string dump_poset_json(const std::string& poset_json) {
    YAML::Node n = YAML::Load(poset_json);
    Poset p;
    p.n_vertices = n["n_vertices"].as<int>();
    p.edges.assign(p.n_vertices, {});
    const YAML::Node& edges = n["edges"];
    for (int u = 0; u < (int)edges.size() && u < p.n_vertices; ++u)
        for (const auto& v : edges[u]) p.edges[u].push_back(v.as<int>());
    p.validate();
    return dump_poset(p);
}

std::string dump_execution_json(const std::string& exec_json) {
    Execution e = parse_execution(YAML::Load(exec_json));
    return dump_execution(e);
}

std::string lib_version() { return std::string(version()); }

} // namespace

EMSCRIPTEN_BINDINGS(nomadim_module) {
    emscripten::function("isDim2", &is_dim2_json);
    emscripten::function("findRealizer", &find_realizer_json);
    emscripten::function("criticalPairs", &critical_pairs_json);
    emscripten::function("expandExecution", &expand_execution_json);
    emscripten::function("parseDocument", &parse_document_json);
    emscripten::function("dumpPoset", &dump_poset_json);
    emscripten::function("dumpExecution", &dump_execution_json);
    emscripten::function("version", &lib_version);
}
```

- [ ] **Step 2: Replace `nomadim/CMakeLists.txt`**

Overwrite `nomadim/CMakeLists.txt` with the following. The native build (CLI/tests/bench) is moved verbatim under `else()`; the only new behaviour is the `NOMADIM_WASM` branch that builds just the reduced module. `src/realizer.cpp` stays in both branches.

```cmake
cmake_minimum_required(VERSION 3.16)
project(nomadim LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release)
endif()

option(NOMADIM_SLOW_TESTS "Enable heavy golden-count enumeration tests" OFF)
option(NOMADIM_BENCH "Build performance benchmarks (fetches Google Benchmark)" OFF)
option(NOMADIM_WASM "Build the WebAssembly module via Emscripten (no CLI/tests/bench)" OFF)

include(FetchContent)

FetchContent_Declare(yaml-cpp
  GIT_REPOSITORY https://github.com/jbeder/yaml-cpp.git
  GIT_TAG 0.8.0)
set(YAML_CPP_BUILD_TESTS OFF CACHE BOOL "" FORCE)
FetchContent_MakeAvailable(yaml-cpp)

if(NOMADIM_WASM)
  # ---- WebAssembly module (Emscripten) ----
  # Reduced source set: omits enumerate.cpp/isomorphism.cpp (std::thread) and the
  # CLI/tests. Everything the editor bindings need, nothing that needs pthreads.
  add_executable(nomadim_wasm
    src/version.cpp
    src/execution.cpp
    src/process_graph.cpp
    src/floyd.cpp
    src/dimension.cpp
    src/poset.cpp
    src/realizer.cpp
    src/io.cpp
    src/wasm_bindings.cpp
  )
  target_include_directories(nomadim_wasm PRIVATE include)
  target_link_libraries(nomadim_wasm PRIVATE yaml-cpp)
  target_compile_options(nomadim_wasm PRIVATE -fexceptions)
  target_link_options(nomadim_wasm PRIVATE
    -fexceptions
    --bind
    "-sMODULARIZE=1"
    "-sEXPORT_NAME=createNomadim"
    "-sENVIRONMENT=web,worker,node"
    "-sALLOW_MEMORY_GROWTH=1"
  )
  set_target_properties(nomadim_wasm PROPERTIES OUTPUT_NAME nomadim)
else()
  # ---- native build: core library + CLI + tests + benchmarks ----
  FetchContent_Declare(cli11
    GIT_REPOSITORY https://github.com/CLIUtils/CLI11.git
    GIT_TAG v2.4.2)
  FetchContent_MakeAvailable(cli11)

  FetchContent_Declare(googletest
    GIT_REPOSITORY https://github.com/google/googletest.git
    GIT_TAG v1.15.2)
  set(gtest_force_shared_crt ON CACHE BOOL "" FORCE)
  FetchContent_MakeAvailable(googletest)

  find_package(Threads REQUIRED)

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
  target_include_directories(nomadim_core PUBLIC include)
  target_link_libraries(nomadim_core PUBLIC yaml-cpp Threads::Threads)

  add_executable(nomadim app/main.cpp app/cmd_check.cpp app/cmd_enumerate.cpp app/cmd_convert.cpp)
  target_link_libraries(nomadim PRIVATE nomadim_core CLI11::CLI11)

  enable_testing()
  include(GoogleTest)
  add_executable(nomadim_tests tests/test_smoke.cpp tests/test_execution.cpp tests/test_process_graph.cpp tests/test_floyd.cpp tests/test_dimension.cpp tests/test_realizer.cpp tests/test_poset.cpp tests/test_isomorphism.cpp tests/test_enumerate.cpp tests/test_io.cpp)
  target_link_libraries(nomadim_tests PRIVATE nomadim_core GTest::gtest_main)
  if(NOMADIM_SLOW_TESTS)
    target_compile_definitions(nomadim_tests PRIVATE NOMADIM_SLOW_TESTS=1)
  endif()
  gtest_discover_tests(nomadim_tests)

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

  # ---- compare.py regression-gate tests ----
  find_package(Python3 COMPONENTS Interpreter)
  if(Python3_Interpreter_FOUND)
    add_test(NAME compare_py
      COMMAND ${Python3_EXECUTABLE} -m unittest discover
              -s ${CMAKE_CURRENT_SOURCE_DIR}/tests -p "test_compare.py")
  endif()
endif()
```

- [ ] **Step 3: Write the build script**

Create `nomadim/editor/build-wasm.sh`:

```bash
#!/usr/bin/env bash
# Build the libnomadim WebAssembly module via Emscripten.
# Requires emcc on PATH (provided by the mise emsdk tool — run via
# `mise run nomadim-editor-build`). Output: nomadim/editor/public/nomadim.{js,wasm}
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
SRC="$ROOT/nomadim"
BUILD="$ROOT/nomadim/build-wasm"
OUT="$ROOT/nomadim/editor/public"

mkdir -p "$OUT"
emcmake cmake -S "$SRC" -B "$BUILD" -DCMAKE_BUILD_TYPE=Release -DNOMADIM_WASM=ON
cmake --build "$BUILD" -j --target nomadim_wasm
cp "$BUILD/nomadim.js" "$BUILD/nomadim.wasm" "$OUT/"
echo "✅ wrote $OUT/nomadim.js + nomadim.wasm"
```

Make it executable: `chmod +x nomadim/editor/build-wasm.sh`.

- [ ] **Step 4: Build the module (provisions Emscripten on first run — slow)**

Run: `mise x emsdk@4.0.23 -- bash nomadim/editor/build-wasm.sh`
(Use a generous timeout ≥ 1200 s; first run installs emsdk ~1 GB and builds yaml-cpp for wasm.)
Expected: ends with `✅ wrote .../nomadim.js + nomadim.wasm`, and both files exist:
`ls -la nomadim/editor/public/nomadim.js nomadim/editor/public/nomadim.wasm`

If `mise x emsdk@4.0.23` is unavailable in this shell, the mise tasks added in Task 2 are the canonical entry point — but Task 2 depends on this building, so resolve any emcc/emcmake errors here first. If the build fails on a missing symbol from `enumerate`/`isomorphism`, confirm those two sources are NOT in the `nomadim_wasm` target.

- [ ] **Step 5: Smoke-test the module from Node**

Run:
```bash
node -e 'require("./nomadim/editor/public/nomadim.js")().then(m=>{console.log("version",m.version());console.log("chain dim2",m.isDim2("[[1],[2],[3],[]]"));console.log("S3 dim2",m.isDim2("[[4,5],[3,5],[3,4],[],[],[]]"));})'
```
Expected output: a version string, `chain dim2 true`, `S3 dim2 false`.

- [ ] **Step 6: Commit**

```bash
git add nomadim/src/wasm_bindings.cpp nomadim/CMakeLists.txt nomadim/editor/build-wasm.sh
git commit -m "feat(nomadim): WebAssembly module + Embind JSON bridge for the editor"
```

---

### Task 2: mise tasks + gitignore

**Files:**
- Modify: `mise.toml` (append three tasks)
- Modify: `nomadim/.gitignore`

- [ ] **Step 1: Add the gitignore entries**

Append to `nomadim/.gitignore`:

```
build-wasm/
editor/public/nomadim.js
editor/public/nomadim.wasm
editor/node_modules/
```

- [ ] **Step 2: Add the mise tasks**

Append to `mise.toml` (after the existing `nomadim-*` tasks). The `tools` key scopes `emsdk`/`node` to these tasks only, so unrelated Coq work never triggers the emsdk install:

```toml
[tasks.nomadim-editor-build]
description = "Build the libnomadim WebAssembly module (Emscripten via mise emsdk)"
tools = { emsdk = "4.0.23" }
run = "bash nomadim/editor/build-wasm.sh"

[tasks.nomadim-editor-test]
description = "Build the WASM module + native CLI, run the Node faithfulness harness"
tools = { emsdk = "4.0.23", node = "22" }
run = '''
#!/usr/bin/env bash
set -euo pipefail
# Native CLI is the faithfulness oracle.
cmake -S nomadim -B nomadim/build -DCMAKE_BUILD_TYPE=Release
cmake --build nomadim/build -j --target nomadim
# WASM module under test.
bash nomadim/editor/build-wasm.sh
# Headless cross-check.
node --test nomadim/editor/test/
'''

[tasks.nomadim-editor-clean]
description = "Remove the editor WASM build dir and generated module"
run = "rm -rf nomadim/build-wasm nomadim/editor/public/nomadim.js nomadim/editor/public/nomadim.wasm && echo '✅ editor wasm artifacts removed'"
```

- [ ] **Step 3: Verify the build task works end-to-end**

Run: `mise run nomadim-editor-build`
Expected: ends with `✅ wrote .../nomadim.js + nomadim.wasm` (fast now that emsdk is installed and the wasm build dir is warm).

- [ ] **Step 4: Commit**

```bash
git add mise.toml nomadim/.gitignore
git commit -m "build(nomadim): mise tasks for the editor WASM build/test/clean"
```

---

### Task 3: Node faithfulness harness

**Files:**
- Create: `nomadim/editor/test/faithfulness.test.cjs`

- [ ] **Step 1: Write the harness**

Create `nomadim/editor/test/faithfulness.test.cjs`:

```js
// Cross-checks the WASM module against the native nomadim CLI (the oracle) on the
// repo's data fixtures plus known cases. Run via `mise run nomadim-editor-test`,
// which builds both the CLI and the module first. Requires Node >= 22.
const test = require('node:test');
const assert = require('node:assert');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const { execFileSync } = require('node:child_process');
const createNomadim = require('../public/nomadim.js');

const ROOT = path.resolve(__dirname, '../../..');     // repo root
const DATA = path.join(ROOT, 'nomadim/data');
const CLI = path.join(ROOT, 'nomadim/build/nomadim');

function cliCheck(file) {
  const out = execFileSync(CLI, ['check', file], { encoding: 'utf8' });
  if (/Dimension <= 2: YES/.test(out)) return true;
  if (/Dimension <= 2: NO/.test(out)) return false;
  throw new Error('unexpected CLI output: ' + out);
}

function adjacencyOf(Nm, text) {
  const doc = JSON.parse(Nm.parseDocument(text));
  if (doc.poset) return doc.poset.edges;
  if (doc.execution) return JSON.parse(Nm.expandExecution(JSON.stringify(doc.execution))).edges;
  throw new Error('document has neither poset nor execution');
}

// Strict reachability of an adjacency list (Warshall), as a Set of "a<b" keys.
function reachKeys(adj) {
  const n = adj.length;
  const lt = Array.from({ length: n }, () => new Array(n).fill(false));
  for (let u = 0; u < n; u++) for (const v of adj[u]) lt[u][v] = true;
  for (let k = 0; k < n; k++)
    for (let i = 0; i < n; i++)
      for (let j = 0; j < n; j++)
        if (lt[i][k] && lt[k][j]) lt[i][j] = true;
  const keys = new Set();
  for (let a = 0; a < n; a++) for (let b = 0; b < n; b++) if (a !== b && lt[a][b]) keys.add(a + '<' + b);
  return keys;
}

function isPermutation(arr, n) {
  if (arr.length !== n) return false;
  const seen = new Array(n).fill(false);
  for (const x of arr) { if (x < 0 || x >= n || seen[x]) return false; seen[x] = true; }
  return true;
}

test('wasm isDim2 matches native CLI on all data fixtures', async () => {
  const Nm = await createNomadim();
  const files = fs.readdirSync(DATA).filter((f) => f.endsWith('.yaml'));
  assert.ok(files.length >= 3, 'expected the data fixtures to be present');
  for (const f of files) {
    const file = path.join(DATA, f);
    const adj = adjacencyOf(Nm, fs.readFileSync(file, 'utf8'));
    assert.strictEqual(Nm.isDim2(JSON.stringify(adj)), cliCheck(file), `isDim2 mismatch on ${f}`);
  }
});

test('parseDocument/dump round-trips the poset and execution fixtures', async () => {
  const Nm = await createNomadim();
  const pdoc = JSON.parse(Nm.parseDocument(fs.readFileSync(path.join(DATA, 'poset_s3.yaml'), 'utf8')));
  const reposet = JSON.parse(Nm.parseDocument(Nm.dumpPoset(JSON.stringify(pdoc.poset))));
  assert.deepStrictEqual(reposet.poset, pdoc.poset);

  const edoc = JSON.parse(Nm.parseDocument(fs.readFileSync(path.join(DATA, 'exec_dim2.yaml'), 'utf8')));
  const reexec = JSON.parse(Nm.parseDocument(Nm.dumpExecution(JSON.stringify(edoc.execution))));
  assert.deepStrictEqual(reexec.execution, edoc.execution);
});

test('expandExecution matches native `nomadim convert`', async () => {
  const Nm = await createNomadim();
  const src = path.join(DATA, 'exec_dim2.yaml');
  const edoc = JSON.parse(Nm.parseDocument(fs.readFileSync(src, 'utf8')));
  const wasmPoset = JSON.parse(Nm.expandExecution(JSON.stringify(edoc.execution)));
  const tmp = path.join(os.tmpdir(), 'nm_convert_' + process.pid + '.yaml');
  execFileSync(CLI, ['convert', src, tmp]);
  const nativePoset = JSON.parse(Nm.parseDocument(fs.readFileSync(tmp, 'utf8'))).poset;
  assert.deepStrictEqual(wasmPoset, nativePoset);
});

test('findRealizer: dim-2 yields a verified realizer; S3 yields none', async () => {
  const Nm = await createNomadim();

  const chain = '[[1],[2],[3],[]]';
  const r = JSON.parse(Nm.findRealizer(chain));
  assert.strictEqual(r.dim_le_2, true);
  const n = 4;
  assert.ok(isPermutation(r.l1, n) && isPermutation(r.l2, n), 'l1/l2 must be permutations');
  const base = reachKeys(JSON.parse(chain));
  const pos1 = []; r.l1.forEach((e, i) => (pos1[e] = i));
  const pos2 = []; r.l2.forEach((e, i) => (pos2[e] = i));
  const inter = new Set();
  for (let a = 0; a < n; a++) for (let b = 0; b < n; b++)
    if (a !== b && pos1[a] < pos1[b] && pos2[a] < pos2[b]) inter.add(a + '<' + b);
  assert.deepStrictEqual([...inter].sort(), [...base].sort(), 'l1 ∩ l2 must equal the order');

  const s3 = JSON.parse(Nm.findRealizer('[[4,5],[3,5],[3,4],[],[],[]]'));
  assert.strictEqual(s3.dim_le_2, false);
  assert.deepStrictEqual(s3.l1, []);
  assert.deepStrictEqual(s3.l2, []);
});

test('criticalPairs agrees with isDim2 (empty critical set => dim2)', async () => {
  const Nm = await createNomadim();
  const chain = '[[1],[2],[3],[]]';
  assert.deepStrictEqual(JSON.parse(Nm.criticalPairs(chain)), []);
  assert.strictEqual(Nm.isDim2(chain), true);
});
```

- [ ] **Step 2: Run the harness**

Run: `mise run nomadim-editor-test`
Expected: all five tests pass (`# pass 5`, `# fail 0`). The build steps run first; if the module or CLI is stale they are rebuilt.

- [ ] **Step 3: Commit**

```bash
git add nomadim/editor/test/faithfulness.test.cjs
git commit -m "test(nomadim): Node faithfulness harness cross-checking WASM vs native CLI"
```

---

### Task 4: README + INDEX + final verification

**Files:**
- Create: `nomadim/editor/README.md`
- Modify: `docs/INDEX.md`

- [ ] **Step 1: Write the editor README**

Create `nomadim/editor/README.md`:

```markdown
# nomadim editor

A browser visualiser/editor for nomadim posets and executions. The poset math
(YAML I/O, execution→poset expansion, dimension-≤-2 check, critical pairs, and
the 2-realizer) runs as the exact `libnomadim` C++ compiled to WebAssembly, so
the editor never diverges from the `nomadim` CLI.

## Status

- **Phase 2a (this):** the WASM core + a headless Node faithfulness test harness.
- **Phase 2b (next):** the browser UI (Cytoscape.js layered-Hasse / swimlane
  views, an editable YAML panel, File System Access API load/save, and a
  `mise run nomadim-editor` task that builds, serves, and opens the browser).

## Build & test (via mise)

```bash
mise run nomadim-editor-build   # build nomadim.js + nomadim.wasm into editor/public/
mise run nomadim-editor-test    # build CLI + module, run the Node faithfulness harness
mise run nomadim-editor-clean   # remove the wasm build dir and generated module
```

Emscripten is provisioned automatically by the pinned mise `emsdk` tool (a ~1 GB
one-time download on first build). Generated `public/nomadim.{js,wasm}` are
gitignored.

## JS API (Embind, all string-in/string-out)

`isDim2(adjJson) -> bool`, `findRealizer(adjJson) -> {dim_le_2,l1,l2} JSON`,
`criticalPairs(adjJson) -> [[x,y]] JSON`, `expandExecution(execJson) -> poset JSON`,
`parseDocument(yamlText) -> {execution?,poset?} JSON`, `dumpPoset(posetJson) -> YAML`,
`dumpExecution(execJson) -> YAML`, `version() -> string`. Adjacency JSON is
array-of-arrays in adjacency form (`edges[u]` lists `v` with `u < v`).
```

- [ ] **Step 2: Add an INDEX entry**

Open `docs/INDEX.md`, find the nomadim Core library table, and add a row after the `realizer` row:

```
| `wasm_bindings` | Embind module `nomadim.{js,wasm}` (`isDim2`, `findRealizer`, `criticalPairs`, `expandExecution`, `parseDocument`, `dumpPoset`, `dumpExecution`) | JSON/YAML bridge over libnomadim for the browser editor; built with `-DNOMADIM_WASM=ON` via `mise run nomadim-editor-build` |
```

- [ ] **Step 3: Confirm the native build is unaffected**

Run: `mise run nomadim-test`
Expected: `100% tests passed ... out of 77` — the CMake refactor's `else()` branch must reproduce the native build exactly (CLI, gtests, golden counts).

- [ ] **Step 4: Confirm the editor build + faithfulness still pass**

Run: `mise run nomadim-editor-test`
Expected: all five Node tests pass.

- [ ] **Step 5: Commit**

```bash
git add nomadim/editor/README.md docs/INDEX.md
git commit -m "docs(nomadim): editor WASM core README + INDEX entry"
```

---

## Self-review notes (already reconciled)

- **Spec coverage:** Implements §1's WASM boundary table (`isDim2`, `findRealizer`, `criticalPairs`, `expandExecution`, `parseDocument`, `dumpPoset`, `dumpExecution`), §5's separate-build/mise-task requirement, and §6's faithfulness guard (Node harness cross-checking the same `data/` fixtures vs the CLI). The File System Access API, Cytoscape views, YAML panel, and browser-opening serve task are explicitly deferred to Phase 2b.
- **Native build untouched in behaviour:** Task 1 Step 2 moves the entire existing native build verbatim under `else()`; Task 4 Step 3 re-runs `mise run nomadim-test` to prove the 77-test suite and golden counts are unchanged.
- **No pthreads in wasm:** the `nomadim_wasm` target omits `enumerate.cpp` and `isomorphism.cpp`; only the binding-reachable sources are compiled.
- **Type/name consistency:** the JS API names (`isDim2`, `findRealizer`, `criticalPairs`, `expandExecution`, `parseDocument`, `dumpPoset`, `dumpExecution`, `version`) and the adjacency-form JSON contract are identical across `wasm_bindings.cpp`, the smoke test, the harness, the README, and the INDEX row.
- **No placeholders:** every code and command step is complete and runnable.
```
