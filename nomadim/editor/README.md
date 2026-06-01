# nomadim editor

A browser visualiser/editor for nomadim posets and executions. The poset math
(YAML I/O, execution→poset expansion, dimension-≤-2 check, critical pairs, and
the 2-realizer) runs as the exact `libnomadim` C++ compiled to WebAssembly, so
the editor never diverges from the `nomadim` CLI.

## Status

- **Phase 2a (done):** the WASM core + a headless Node faithfulness test harness.
- **Phase 2b-i (done):** browser viewer — load a YAML poset/execution, see the
  layered Hasse diagram, the live dimension-≤-2 verdict, and an editable YAML panel.
- **Phase 2b-ii (done):** poset editing — add/remove vertices and edges (cycles
  rejected), critical-pair highlight toggle, the realizer panel (two linear
  extensions when dim ≤ 2), and Save (File System Access API + download fallback).
- **Phase 2b-iii (next):** the execution swimlane view and execution editing.

## Build, run & test (via mise)

```bash
mise run nomadim-editor         # build WASM, serve the editor, open the browser
mise run nomadim-editor-build   # build nomadim.js + nomadim.wasm into editor/public/
mise run nomadim-editor-test    # build CLI + module, run Node faithfulness + unit tests
mise run nomadim-editor-e2e     # build module, run the Playwright browser smoke suite
mise run nomadim-editor-clean   # remove the wasm build dir and generated module
```

Emscripten is provisioned by the pinned mise `emsdk` tool (~1 GB one-time).
Cytoscape/dagre are committed under `editor/vendor/`. Generated
`public/nomadim.{js,wasm}` and `editor/node_modules/` are gitignored.

## JS API (Embind, all string-in/string-out)

`isDim2(adjJson) -> bool`, `findRealizer(adjJson) -> {dim_le_2,l1,l2} JSON`,
`criticalPairs(adjJson) -> [[x,y]] JSON`, `expandExecution(execJson) -> poset JSON`,
`parseDocument(yamlText) -> {execution?,poset?} JSON`, `dumpPoset(posetJson) -> YAML`,
`dumpExecution(execJson) -> YAML`, `version() -> string`. Adjacency JSON is
array-of-arrays in adjacency form (`edges[u]` lists `v` with `u < v`).
