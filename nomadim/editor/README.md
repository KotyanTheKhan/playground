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
