# nomadim poset/execution visualiser & editor — design

**Date:** 2026-06-01
**Branch:** `nomadim-editor` (off `dev`)
**Status:** approved design, pending implementation plan

## Goal

A standalone browser web app, living under `nomadim/editor/`, for viewing and
editing nomadim documents — both general **posets** (vertices + edges) and
**executions** (`n_procs` + ordered syncs). It renders posets as layered Hasse
diagrams and executions as process swimlanes, lets the user edit them, shows a
live order-dimension-≤-2 verdict, and reads/writes the same YAML format as the
`nomadim` CLI.

## Implementation phasing

This spec is delivered as **two implementation plans**, because the realizer is
an independently useful libnomadim algorithm:

1. **`find_realizer` in libnomadim** (§2) — pure C++, exhaustively tested,
   reusable. Built and merged first.
2. **The web editor** (§1, §3–7) — WASM bindings + Cytoscape UI + mise task,
   consuming `find_realizer`.

## Core principle: one source of truth

All *semantics* come from the existing `libnomadim` C++ code compiled to
WebAssembly via Emscripten. The web app never re-implements the algorithms in
JavaScript. This keeps the editor faithful to the CLI (a standing project
constraint — see the dimension-faithful-port note) and avoids a second
implementation that can silently drift.

The graph **rendering and interaction** layer uses a vendored graph library
(Cytoscape.js + cytoscape-dagre). Only presentation lives in JS; all poset
math crosses the WASM boundary.

## Components

### 1. WASM boundary — `nomadim/src/wasm_bindings.cpp` (Emscripten-only)

An Embind wrapper compiled **only** in the Emscripten build (guarded by a
`NOMADIM_WASM` CMake option). Each function delegates to existing library code:

| JS function | Delegates to | Returns |
|-------------|--------------|---------|
| `parseDocument(text)` | `parse_document` | `{execution?, poset?}` |
| `dumpPoset(poset)` | `dump_poset` | YAML text |
| `dumpExecution(exec)` | `dump_execution` | YAML text |
| `expandExecution(exec)` | `ProcessGraph::build` → `Poset::from` | poset |
| `isDim2(adjacency)` | `is_dim2` | bool |
| `criticalPairs(adjacency)` | `find_critical_pairs` | `[{x,y}]` |
| `findRealizer(adjacency)` | **new** `find_realizer()` (see §2) | `{dim_le_2: bool, l1: [int], l2: [int]}` |

YAML parse/dump go through WASM too, so the editor's file format is byte-for-byte
the CLI's format.

### 2. New first-class libnomadim algorithm — `find_realizer()`

The realizer (the two linear extensions L₁, L₂ whose intersection is exactly the
partial order) is a **first-class algorithm in libnomadim**, not an editor
helper. It lives in its own `include/nomadim/realizer.hpp` + `src/realizer.cpp`,
is reusable by future work, and is covered by exhaustive tests. The editor is
just one consumer.

**API:**
```cpp
struct Realizer {
    bool dim_le_2 = false;       // true iff a 2-realizer was found
    std::vector<int> l1, l2;     // linear extensions (permutations, bottom→top)
};
Realizer find_realizer(const adjacency_list& g);  // {false,{},{}} when dim > 2
```

**Algorithm — verified transitive orientation (backtracking).** A poset has
order dimension ≤ 2 iff its incomparability graph admits a transitive
orientation (Dushnik–Miller); any such orientation O gives the realizer
`L₁ = P ∪ O`, `L₂ = P ∪ O⁻¹`. We find one by backtracking:

1. Compute the strict reachability relation `base` of `g` (Warshall).
2. List the incomparable unordered pairs (neither `base(u,v)` nor `base(v,u)`).
3. Recursively orient each incomparable pair, maintaining two transitively-closed
   strict relations R₁ (starts at `base`) and R₂ (starts at `base`): orienting a
   pair `u<v` in R₁ forces `v<u` in R₂. After each addition, close transitively
   and reject the branch on any cycle.
4. When every incomparable pair is oriented, both R₁ and R₂ are total orders
   extending P with opposite orientation on every incomparable pair, so
   `R₁ ∩ R₂ = P` **by construction**. Emit `l1`, `l2` as the topological orders.
5. If the search exhausts with no assignment, dim > 2 → `{false,{},{}}`.

Correctness is structural (the two relations are complementary on incomparable
pairs by construction) **and** re-verified at runtime in tests (`l1 ∩ l2 == P`).
Backtracking is exponential in the worst case but fine for the small posets in
scope; Golumbic's polynomial transitive-orientation is a noted future
optimisation. Precondition: `g` is acyclic (callers use `Poset::validate`
first). The existing `dimension.cpp` (and the golden enumeration counts) are
**not** modified.

**Tests (`tests/test_realizer.cpp`, exhaustive):** chains, antichains, empty/
singleton, fences; S₃ and the canonical execution → `dim_le_2 == false`;
single-sync execution → realizer found; for every fixture a property check that
`l1`/`l2` are permutations, each respects all `base` edges (valid linear
extensions), and `l1 ∩ l2 == base`; a brute-force cross-check that
`find_realizer(g).dim_le_2 == is_dim2(g)` over **all** small DAGs (≤ 4 vertices).

### 3. Web app — `nomadim/editor/`

Plain HTML + JS modules, Cytoscape.js for rendering. Two tabbed views plus a
YAML panel and a verdict bar.

**Poset view** — layered Hasse layout (`cytoscape-dagre`, minimal elements at
bottom, covers pointing up):
- Add vertex (button / double-click canvas).
- Draw edge `u → v` meaning *u below v* (drag with cytoscape-edgehandles).
- Delete selected node/edge (Delete key).
- Drag to reposition; re-layout on demand.
- Every structural edit: reject edges that introduce a cycle (toast, no commit),
  then re-run `isDim2` and update the verdict bar.

**Execution view** — swimlane layout (manual/preset positions):
- Set `n_procs`; each process is a vertical lane (chain of events).
- Append a sync as an ordered pair of process lanes; remove last / reorder via an
  ordered sync list panel.
- "Show derived poset" expands via `expandExecution` and switches to the Poset
  view with the result.

**Verdict bar** (persistent): dim ≤ 2 / not, with critical-pair count.
- Toggle "highlight critical pairs" → colours them on the poset.
- When dim ≤ 2, a "show realizer" panel renders the two linear extensions as
  parallel ordered columns.

**YAML panel**: editable text view kept in sync with the diagram. Editing text
and applying re-parses through WASM; diagram edits re-dump through WASM.

### 4. File I/O

- **File System Access API** for in-place open/save of a chosen `.yaml`
  (Chromium). Localhost is a secure context, so it works under the dev server.
- **Fallback** for Firefox/Safari: file-picker open + download save.

## Build, run & test — all via mise (separate from the native CMake build)

The native `nomadim` CMake build is **untouched**. New, separate flow:

- `nomadim/editor/build-wasm.sh` — runs `emcmake` over the existing CMake with
  `-DNOMADIM_WASM=ON`, compiling libnomadim + `wasm_bindings.cpp` and linking
  yaml-cpp, emitting `nomadim/editor/public/nomadim.js` + `nomadim.wasm`
  (gitignored build output).
- **`mise run nomadim-editor`** — the one command a user runs: build the WASM if
  stale → start a local static server (e.g. `python3 -m http.server`) → **open
  the default browser at the URL automatically** (`open` on macOS, `xdg-open` on
  Linux) → stay running until interrupted.
- `mise run nomadim-editor-test` — see Testing.
- `mise run nomadim-editor-clean` — remove the editor build output.
- Emscripten is provisioned via mise if a plugin is available; otherwise it is
  documented as a prerequisite (`emsdk`) in `nomadim/editor/README.md`.

## Testing — faithfulness guard

A Node harness in `nomadim/editor/test/` loads the built WASM module and
cross-checks it against the **same YAML fixtures** the C++ tests use plus known
dim-2 / non-dim-2 cases:

- `parseDocument` then `dumpPoset`/`dumpExecution` round-trips the fixture text.
- `isDim2` matches the expected verdict on each fixture.
- `expandExecution` matches `nomadim convert` output on the sample executions.
- `realizer` returns extensions whose intersection reproduces the input order
  (dim-2 fixtures) and is empty otherwise.

This catches any drift between the web build and the CLI. Run via
`mise run nomadim-editor-test`.

The new C++ `realizer()` has GoogleTest cases in the normal nomadim test suite.

Cytoscape rendering is not unit-tested; a small DOM smoke test confirms the app
boots and the WASM module loads.

## Layout on disk

```
nomadim/
  src/wasm_bindings.cpp        # Emscripten-only Embind wrapper
  src/dimension.cpp            # + realizer() (and coloring refactor)
  include/nomadim/dimension.hpp
  editor/
    index.html
    src/                       # app, model, yaml-sync, poset-view, exec-view, realizer-view
    vendor/                    # pinned cytoscape.js + cytoscape-dagre
    public/                    # nomadim.{js,wasm} build output (gitignored)
    build-wasm.sh
    test/                      # Node faithfulness harness
    README.md
```

## Out of scope (v1)

- Editing/rendering posets of more than a couple hundred vertices (no
  performance work beyond what Cytoscape gives for free).
- Multi-document tabs / project files.
- Undo/redo history (nice-to-have, not v1).
- Any change to the native CLI behaviour or the golden enumeration counts.
