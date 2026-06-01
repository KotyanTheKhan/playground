# nomadim editor — drag-and-drop execution editing — design

**Date:** 2026-06-01
**Branch:** `nomadim-editor-exec-drag` (off the editor work, which currently sits on
the unmerged `nomadim-editor-fix-exec-edit` branch — per-view toolbars + editable-
after-derive)
**Status:** approved design, pending implementation plan

## Goal

Add direct-manipulation (drag) editing to the editor's execution swimlane: create
syncs by dragging between process lanes, reorder syncs and processes by dragging,
and delete a sync by dragging it onto a delete strip. Drag **complements** the
existing toolbar (process count input, sync inputs, Add/Remove-last buttons) —
the toolbar stays for accessibility and deterministic use; drag is an additional
input path producing the same model edits.

## Context

The execution view renders an execution `{n_procs, syncs:[[a,b],...]}` as a
swimlane via a **pure** `executionSvg(execution)` string injected into `#exec` by
`execution-view.mjs`. Today editing is toolbar-only and the pure ops are
`emptyExecution`, `setNProcs`, `appendSync`, `removeLastSync` (in
`execution-edits.mjs`). The app's `editExec(fn)` applies a pure op to the model
and re-renders. All poset semantics come from the WASM module; the swimlane is a
pure view of the abstract `{n_procs, syncs}` model (the full event-DAG poset is
only produced by "Show derived poset" via WASM). This feature preserves that:
drag only mutates the abstract execution model.

## Gestures (handle-based — distinct grab targets, no ambiguity)

| Gesture | Grab target | Action | Live feedback |
|---------|-------------|--------|---------------|
| **New sync** | a lane's **body** (the vertical line / column area) | drag to another lane, release → `appendSync(a,b)` | rubber-band line from source lane to cursor; target lane highlights on hover |
| **Reorder process** | a lane's **header** (the `Pn` label) | drag left/right; release past another lane → `reorderProcess(from,to)` | dragged header follows cursor; insertion gap highlights |
| **Reorder sync** | a **sync connector** | drag up/down onto another row slot → `moveSync(from,to)` | connector follows; target row slot highlights |
| **Delete sync** | a **sync connector** | release over the **delete strip** → `removeSyncAt(i)` | delete strip (shown only while dragging a connector) highlights when hovered |

Rules:
- A connector drag resolves to **delete** if released over the delete strip, else
  to **reorder** to the nearest row slot, else (released back on its own slot /
  outside any target) a no-op.
- A lane-body drag that releases on the **same** lane, on empty space, or on a
  process already synced at the identical pair is a no-op (and `appendSync`'s
  existing validation rejects self/duplicate/out-of-range).
- A header drag that releases on its own position is a no-op.

## Architecture

Three pieces, each independently testable:

1. **`execution-svg.mjs` (modified, still pure).** Per lane, render a
   transparent **wide hit-rect** `<rect class="lane-hit" data-proc="p">` (a
   `LANE_GAP`-wide, full-height, `fill:transparent` band centered on the lane)
   so the thin 1px lane line is easy to grab and hit-test; tag the `Pn` `<text>`
   header with `class="proc-label" data-proc="p"` so the header is a distinct
   grab target. Render a delete-strip `<rect class="delete-strip">` (default
   `display:none`, positioned along the bottom edge). `data-sync="i"` already
   exists on connectors; also widen connector hit area is unnecessary (the dashed
   line + its two `event` dots are grabbable). Output remains a complete SVG
   string — unit-tested by attribute/coordinate assertions (e.g. one
   `.lane-hit[data-proc]` per process, a `.delete-strip` present).

2. **`execution-drag.mjs` (new) — the interaction controller.**
   `attachDrag(svgEl, execution, handlers)`:
   - Wires `pointerdown`/`pointermove`/`pointerup` on `svgEl`.
   - On `pointerdown`, classifies the grab from the target's `data-*`/class:
     lane header → process-reorder; lane body → new-sync; connector → sync
     move/delete.
   - Maintains a transient `<g class="drag-overlay">` for feedback (rubber-band
     line, highlights, the visible delete strip) without mutating the model.
   - Resolves the drop target by pointer position (lane under cursor via
     `data-proc` hit zones; row slot via y bands; delete strip via its rect).
   - On commit, calls the matching handler: `handlers.onNewSync(a,b)`,
     `onReorderProcess(from,to)`, `onMoveSync(from,to)`, `onDeleteSync(i)`.
   - Pure helper `classifyTarget(el)` and `rowFromY(y, nSyncs)` /
     `laneFromX(x, nProcs)` are exported for unit testing where geometry permits.

3. **`execution-edits.mjs` (extended).** New immutable ops:
   - `moveSync(exec, from, to)` — remove the sync at `from`, insert it at `to`
     (clamped to `[0, len-1]`); returns a new execution. No-op-safe when
     `from === to`.
   - `removeSyncAt(exec, i)` — drop the sync at index `i` (throws on out-of-range).
   - `reorderProcess(exec, from, to)` — move the process column from index `from`
     to `to`, building the index permutation and **remapping every sync
     endpoint** through it; `n_procs` unchanged.

`app.mjs` calls `attachDrag` after each `renderExecution`, wiring the handlers to
`editExec((e) => appendSync(e, a, b))`, `editExec((e) => reorderProcess(e, from,
to))`, `editExec((e) => moveSync(e, from, to))`, `editExec((e) =>
removeSyncAt(e, i))`. Because every drag flows through `editExec`, the existing
pipeline (re-render, verdict, YAML sync, view switching) is reused unchanged.

## Testing

- **Pure ops** (`execution-edits.mjs`): Node unit tests for `moveSync`
  (forward/backward/no-op/clamp), `removeSyncAt` (middle/first/last/out-of-range
  throw), and `reorderProcess` (endpoint remap correctness, immutability). Plus
  any exported pure geometry helpers from `execution-drag.mjs`
  (`rowFromY`/`laneFromX`/`classifyTarget`).
- **Drag integration** (Playwright): locate SVG elements by `[data-proc]` /
  `[data-sync]`, read `boundingBox()`, and perform real drags with
  `mouse.move/down/move/up`. Assert the resulting execution via a new
  `window.__editor.currentExecution()` hook (`{n_procs, syncs}`):
  - drag lane 0 → lane 1 appends `[0,1]`;
  - drag the first connector onto the second row swaps order (`moveSync`);
  - drag a connector onto the delete strip removes it;
  - drag a process header past another reorders processes and remaps syncs.
- The existing toolbar Playwright tests and the editable-after-derive / per-view-
  toolbar tests must remain green.

## Out of scope

- Animation/momentum, multi-select drag, undo/redo, touch-specific affordances
  beyond what pointer events provide for free.
- Any change to poset-side editing or to the WASM layer.

## File structure

```
nomadim/editor/src/execution-svg.mjs     # + data-proc on lanes/headers, delete strip
nomadim/editor/src/execution-drag.mjs     # NEW: pointer-event drag controller
nomadim/editor/src/execution-edits.mjs    # + moveSync, removeSyncAt, reorderProcess
nomadim/editor/src/app.mjs                # wire attachDrag handlers + currentExecution hook
nomadim/editor/styles.css                 # drag-overlay / delete-strip / highlight styles
nomadim/editor/test/execution.test.mjs    # + ops (+ geometry helper) unit tests
nomadim/editor/e2e/execution-drag.spec.mjs # NEW: Playwright drag tests
nomadim/editor/README.md                  # document drag editing
```
