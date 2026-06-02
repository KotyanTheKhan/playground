# nomadim editor: compute heavy dimension/realizers on demand — design

Date: 2026-06-02

## Goal

In the browser editor, stop auto-running the heavy general-dimension analysis on
every poset load/edit. Run it only when the user presses a **Compute dimension**
button, and keep the last results visible but marked **(stale)** after the poset
changes.

## Scope (decisions)

- **Gated (button-only):** the general dimension panel — `Dimension: N (k
  hyperedges)`, the one-realizer line, and the all-realizers count
  (`client.dimension` / `findOneRealizer` / `allRealizers`).
- **Still auto-running (unchanged):** the dim-≤2 verdict + critical-pair count
  (`computeVerdict` → `isDim2` + `criticalPairs`) and the critical-pair overlay.
- **After an incremental poset edit** (add/remove vertex or edge): keep the last
  computed results visible but mark them stale (dimmed, with a hint).
- **On wholesale document replacement** (New poset, Load file, Apply YAML, Show
  derived poset): clear the panel back to its hint.
- Execution view is unaffected (it never showed the dimension panel).

## Approach

App-level cache keyed by adjacency. A `dim` state object holds the last result
plus `adjKey = JSON.stringify(adj)` captured at compute time. `refresh()` renders
from this cache and compares the current adjacency's `JSON.stringify` to
`dim.adjKey`; a mismatch means stale. Staleness is a plain JS string compare — no
new module, no extra WASM round-trip, no reuse of the C++ `source_hash`.

## Components

- **`nomadim/editor/index.html`** — add `<button id="compute-dim">Compute
  dimension</button>` to the `#poset-tools` toolbar group. The `#dimension` line
  starts showing the hint text.
- **`nomadim/editor/src/dimension.mjs`** — extend `dimensionText(result, opts)`
  with an optional `{ stale: true }` that appends `  (stale — press Compute)`.
  Add a `DIMENSION_HINT` constant (`'Dimension: press Compute'`). Pure, unit-
  tested. `realizerLines` unchanged.
- **`nomadim/editor/src/app.mjs`**
  - App state `let dim = null;` = `{ adjKey, result, one, all }`.
  - `computeDimension()` (bound to `#compute-dim`): if no poset, show error; else
    read `adj = posetAdjacency(model)`, call `client.dimension(adj)` /
    `findOneRealizer(adj)` / `allRealizers(adj)`, store keyed by
    `JSON.stringify(adj)`, then `renderDimensionPanel()`.
  - `renderDimensionPanel()` replaces the old auto `renderDimension(adj)` call in
    `refresh()`'s poset branch:
    - `dim === null` → `els.dimension.textContent = DIMENSION_HINT`; clear
      `#realizer` and `#realizers-all`; remove `stale` class.
    - else → `stale = JSON.stringify(posetAdjacency(model)) !== dim.adjKey`;
      render `dimensionText(dim.result, { stale })`, the realizer line, and the
      all-realizers count; toggle a `stale` CSS class on the three panel
      elements.
  - Reset `dim = null` in `loadText`, the `New poset` handler, `apply` (Apply
    YAML), the file-load handler, and `derivePoset`. Leave `dim` untouched in
    `editPoset` / `deleteSelected` (so edits render as stale).
  - Execution / empty branches of `refresh()` clear the panel as today (and
    `els.dimension`/`realizers-all` already cleared there).
  - Test hooks on `window.__editor`: `computeDimension()` (invoke the handler);
    keep `dimensionText()` / `realizerLineCount()`; the `dimensionText()` hook
    will return the hint when nothing is computed and the `(stale)` text when
    stale.
- **`nomadim/editor/styles.css`** — `.stale { opacity: 0.5; }`.

## Error handling

Unchanged cap behavior: if `client.dimension(adj)` returns `{ error }`,
`dimensionText` renders `Dimension: <error>` and the realizer/all lines stay
empty. Compute on an empty poset (no `model.poset`) surfaces the standard "Create
or load a poset first" error via the existing `showError`.

## Testing

- **`nomadim/editor/test/dimension.test.mjs`** (node:test) — extend: `dimensionText`
  with `{ stale: true }` appends the stale suffix; `DIMENSION_HINT` constant value.
- **`nomadim/editor/e2e/dimension.spec.mjs`** (Playwright) —
  - Update the S₃ test: after `loadText`, the panel shows the hint and 0 realizer
    lines; after pressing `#compute-dim`, it shows `Dimension: 3` and 3 realizer
    lines.
  - New test: load S₃, Compute, then add a vertex; assert the dimension text
    contains `(stale)`.
- **`nomadim/editor/e2e/app.spec.mjs`** — unaffected (verdict still auto-runs);
  must still pass.

## Out of scope (YAGNI)

- Pre-filling the panel from a loaded file's cached `meta.dimension`/`realizers`
  (possible later follow-up; the load path clears the panel for now).
- Gating the dim-≤2 verdict or critical pairs behind the button.
- Any change to the C++ library, CLI, or WASM bindings.
