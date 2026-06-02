# Drag-and-drop execution editing — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add direct-manipulation (drag) editing to the execution swimlane — create syncs by dragging lane→lane, reorder syncs and processes by dragging, and delete a sync by dragging it onto a delete strip — complementing the existing toolbar.

**Architecture:** Keep `executionSvg` a pure string renderer (add `data-proc` lanes/headers, transparent lane hit-rects, `data-sync` on event dots, and a hidden delete-zone) and expose pure geometry helpers from it. A new `execution-drag.mjs` attaches pointer-event handlers, recognizes the gesture from the grabbed element, draws transient feedback, and calls back into three new immutable ops in `execution-edits.mjs` (`moveSync`, `removeSyncAt`, `reorderProcess`). `app.mjs` re-attaches the controller after each execution render and routes callbacks through the existing `editExec` pipeline.

**Tech Stack:** Vanilla ES modules + SVG + Pointer Events (no new deps), the existing WASM module, Node ≥ 22 (`node:test`), Playwright.

**Branch:** `nomadim-editor-exec-drag` (already checked out; builds on the unmerged execution fixes).

**Spec:** `docs/superpowers/specs/2026-06-01-execution-drag-editing-design.md`.

---

## Conventions / current state

- Execution model: `{ n_procs, syncs:[[a,b],...] }`. `execution-edits.mjs` has `emptyExecution`, `setNProcs`, `appendSync`, `removeLastSync`.
- `execution-svg.mjs` renders the swimlane as a pure string; layout constants `MARGIN=40, LANE_GAP=90, ROW_GAP=50, TOP=30`; `laneX(p)=MARGIN+p*LANE_GAP`, `rowY(i)=TOP+(i+1)*ROW_GAP`.
- `app.mjs` `editExec(fn)` applies a pure op to `model.execution` and re-renders via `refresh()`.
- Tests: `mise run nomadim-editor-test` (Node, currently **30** pass), `mise run nomadim-editor-e2e` (Playwright, currently **15** pass). Build/run via mise only; no AI watermark in commits.
- **Geometry placement note:** the pure geometry helpers (`laneX`, `rowY`, `laneFromX`, `rowFromY`, `svgHeight`, `isInDeleteZone`) live in `execution-svg.mjs` (single source of the layout numbers); `classifyTarget` + `attachDrag` live in `execution-drag.mjs`.

## File structure

| File | Responsibility |
|------|----------------|
| `nomadim/editor/src/execution-edits.mjs` | (modify) + `moveSync`, `removeSyncAt`, `reorderProcess` |
| `nomadim/editor/src/execution-svg.mjs` | (modify) export geometry helpers; add lane hit-rects, `data-proc`, `data-sync` dots, hidden delete-zone |
| `nomadim/editor/src/execution-drag.mjs` | (new) `classifyTarget`, `attachDrag` pointer controller |
| `nomadim/editor/src/app.mjs` | (modify) re-attach drag after each exec render; wire callbacks; `currentExecution()` hook |
| `nomadim/editor/styles.css` | (modify) drag-overlay / hot / delete-zone styles |
| `nomadim/editor/test/execution.test.mjs` | (modify) + ops + geometry + SVG-structure unit tests |
| `nomadim/editor/e2e/execution-drag.spec.mjs` | (new) Playwright drag tests |
| `nomadim/editor/README.md` | (modify) document drag editing |

---

### Task 1: New immutable execution ops

**Files:** Modify `nomadim/editor/src/execution-edits.mjs`, `nomadim/editor/test/execution.test.mjs`.

- [ ] **Step 1: Append the three ops to `execution-edits.mjs`**

```js

// Move the sync at index `from` to index `to` (clamped to a valid slot).
export function moveSync(exec, from, to) {
  const len = exec.syncs.length;
  if (from < 0 || from >= len) throw new Error('sync index out of range');
  const t = Math.max(0, Math.min(len - 1, to));
  const syncs = exec.syncs.map(([a, b]) => [a, b]);
  const [moved] = syncs.splice(from, 1);
  syncs.splice(t, 0, moved);
  return { n_procs: exec.n_procs, syncs };
}

// Remove the sync at index `i`.
export function removeSyncAt(exec, i) {
  if (i < 0 || i >= exec.syncs.length) throw new Error('sync index out of range');
  return { n_procs: exec.n_procs, syncs: exec.syncs.filter((_, k) => k !== i).map(([a, b]) => [a, b]) };
}

// Move the process column at index `from` to index `to`, remapping every sync
// endpoint through the resulting index permutation. n_procs is unchanged.
export function reorderProcess(exec, from, to) {
  const n = exec.n_procs;
  if (from < 0 || from >= n || to < 0 || to >= n) throw new Error('process index out of range');
  const order = [];
  for (let i = 0; i < n; i++) order.push(i);
  order.splice(from, 1);
  order.splice(to, 0, from);
  const map = new Array(n);
  order.forEach((oldIdx, newIdx) => { map[oldIdx] = newIdx; });
  return { n_procs: n, syncs: exec.syncs.map(([a, b]) => [map[a], map[b]]) };
}
```

- [ ] **Step 2: Append unit tests to `execution.test.mjs`**

Add the import names to the existing `execution-edits.mjs` import line so it reads:

```js
import { emptyExecution, setNProcs, appendSync, removeLastSync, moveSync, removeSyncAt, reorderProcess } from '../src/execution-edits.mjs';
```

Append these tests:

```js
test('moveSync reorders syncs and is no-op-safe / clamped', () => {
  const e = { n_procs: 2, syncs: [[0, 1], [1, 0]] };
  assert.deepStrictEqual(moveSync(e, 0, 1).syncs, [[1, 0], [0, 1]]);
  assert.deepStrictEqual(moveSync(e, 0, 0).syncs, [[0, 1], [1, 0]]); // no-op
  assert.deepStrictEqual(moveSync(e, 0, 9).syncs, [[1, 0], [0, 1]]); // clamp to last
});

test('moveSync throws on out-of-range source', () => {
  assert.throws(() => moveSync({ n_procs: 2, syncs: [[0, 1]] }, 3, 0), /out of range/);
});

test('removeSyncAt drops the indexed sync and validates range', () => {
  const e = { n_procs: 3, syncs: [[0, 1], [1, 2], [0, 2]] };
  assert.deepStrictEqual(removeSyncAt(e, 1).syncs, [[0, 1], [0, 2]]);
  assert.throws(() => removeSyncAt(e, 5), /out of range/);
});

test('reorderProcess moves a column and remaps sync endpoints', () => {
  const e = { n_procs: 3, syncs: [[0, 1], [1, 2]] };
  const r = reorderProcess(e, 0, 2); // 0->2 ; old1->0, old2->1, old0->2
  assert.strictEqual(r.n_procs, 3);
  assert.deepStrictEqual(r.syncs, [[2, 0], [0, 1]]);
  assert.throws(() => reorderProcess(e, 0, 9), /out of range/);
});

test('the new ops do not mutate their input', () => {
  const e = { n_procs: 3, syncs: [[0, 1], [1, 2]] };
  moveSync(e, 0, 1); removeSyncAt(e, 0); reorderProcess(e, 0, 2);
  assert.deepStrictEqual(e, { n_procs: 3, syncs: [[0, 1], [1, 2]] });
});
```

- [ ] **Step 3: Run tests**

Run: `mise run nomadim-editor-test`
Expected: `# pass 35`, `# fail 0` (30 existing + 5 new).

- [ ] **Step 4: Commit**

```bash
git add nomadim/editor/src/execution-edits.mjs nomadim/editor/test/execution.test.mjs
git commit -m "feat(nomadim): execution ops moveSync/removeSyncAt/reorderProcess"
```

---

### Task 2: Geometry exports + drag-ready SVG

**Files:** Modify `nomadim/editor/src/execution-svg.mjs`, `nomadim/editor/test/execution.test.mjs`.

- [ ] **Step 1: Rewrite `execution-svg.mjs`**

Replace the entire file with:

```js
// Pure renderer + geometry for the execution swimlane. executionSvg returns a
// complete <svg> string (no DOM access). Geometry helpers are exported so the
// drag controller hit-tests against the exact same coordinate system.

const MARGIN = 40;     // left/top padding
const LANE_GAP = 90;   // horizontal gap between process lanes
const ROW_GAP = 50;    // vertical gap between sync rows
const TOP = 30;        // y of the first sync row baseline

export function laneX(p) { return MARGIN + p * LANE_GAP; }
export function rowY(i) { return TOP + (i + 1) * ROW_GAP; }
export function svgWidth(execution) { return MARGIN * 2 + Math.max(0, execution.n_procs - 1) * LANE_GAP; }
export function svgHeight(execution) { return TOP + (execution.syncs.length + 1) * ROW_GAP + MARGIN; }

// Nearest process lane for an SVG-space x, clamped to [0, n-1]; -1 if no lanes.
export function laneFromX(x, n) {
  if (n <= 0) return -1;
  return Math.max(0, Math.min(n - 1, Math.round((x - MARGIN) / LANE_GAP)));
}

// Nearest sync-row slot for an SVG-space y, clamped to [0, nSyncs-1]; -1 if none.
export function rowFromY(y, nSyncs) {
  if (nSyncs <= 0) return -1;
  return Math.max(0, Math.min(nSyncs - 1, Math.round((y - TOP) / ROW_GAP) - 1));
}

// True if an SVG-space y is within the bottom delete-zone band.
export function isInDeleteZone(y, execution) {
  return y > svgHeight(execution) - MARGIN;
}

export function executionSvg(execution) {
  const n = execution.n_procs;
  const syncs = execution.syncs;
  const width = svgWidth(execution);
  const height = svgHeight(execution);

  const parts = [];
  parts.push(`<svg xmlns="http://www.w3.org/2000/svg" width="${width}" height="${height}" class="exec-svg" data-procs="${n}" data-syncs="${syncs.length}">`);

  // Per lane: a transparent wide hit-rect (easy to grab + hit-test), the visible
  // lane line, and a grabbable process-header label.
  for (let p = 0; p < n; p++) {
    const x = laneX(p);
    parts.push(`<rect class="lane-hit" data-proc="${p}" x="${x - LANE_GAP / 2}" y="${TOP}" width="${LANE_GAP}" height="${height - MARGIN - TOP}" fill="transparent" />`);
    parts.push(`<line class="lane" x1="${x}" y1="${TOP}" x2="${x}" y2="${height - MARGIN}" />`);
    parts.push(`<text class="proc-label" data-proc="${p}" x="${x}" y="${TOP - 10}" text-anchor="middle">P${p}</text>`);
  }

  // Sync connectors (ordered top→bottom) + endpoint dots (also data-sync so the
  // dots are grabbable) + index labels.
  syncs.forEach(([a, b], i) => {
    const y = rowY(i);
    const xa = laneX(a), xb = laneX(b);
    parts.push(`<line class="sync" x1="${xa}" y1="${y}" x2="${xb}" y2="${y}" data-sync="${i}" data-a="${a}" data-b="${b}" />`);
    parts.push(`<circle class="event" data-sync="${i}" cx="${xa}" cy="${y}" r="5" />`);
    parts.push(`<circle class="event" data-sync="${i}" cx="${xb}" cy="${y}" r="5" />`);
    parts.push(`<text class="sync-label" x="${Math.min(xa, xb) - 12}" y="${y + 4}" text-anchor="end">${i}</text>`);
  });

  // Delete zone (hidden until a connector drag activates it).
  parts.push(`<g class="delete-zone"><rect x="4" y="${height - MARGIN + 4}" width="${Math.max(0, width - 8)}" height="${MARGIN - 8}" rx="4" /><text x="${width / 2}" y="${height - MARGIN / 2 + 4}" text-anchor="middle">drop here to delete</text></g>`);

  parts.push(`</svg>`);
  return parts.join('');
}
```

- [ ] **Step 2: Add geometry + structure tests to `execution.test.mjs`**

Update the `execution-svg.mjs` import line to:

```js
import { executionSvg, laneFromX, rowFromY, isInDeleteZone } from '../src/execution-svg.mjs';
```

Append these tests:

```js
test('laneFromX picks the nearest lane and clamps', () => {
  assert.strictEqual(laneFromX(40, 3), 0);    // exactly lane 0
  assert.strictEqual(laneFromX(130, 3), 1);   // exactly lane 1
  assert.strictEqual(laneFromX(120, 3), 1);   // nearest 1
  assert.strictEqual(laneFromX(9999, 3), 2);  // clamp high
  assert.strictEqual(laneFromX(-50, 3), 0);   // clamp low
  assert.strictEqual(laneFromX(40, 0), -1);   // no lanes
});

test('rowFromY picks the nearest row slot and clamps', () => {
  assert.strictEqual(rowFromY(80, 2), 0);     // rowY(0)=80
  assert.strictEqual(rowFromY(130, 2), 1);    // rowY(1)=130
  assert.strictEqual(rowFromY(9999, 2), 1);   // clamp high
  assert.strictEqual(rowFromY(0, 2), 0);      // clamp low
  assert.strictEqual(rowFromY(80, 0), -1);    // no syncs
});

test('isInDeleteZone is true only below the lane band', () => {
  const e = { n_procs: 2, syncs: [[0, 1]] }; // height = 30 + 2*50 + 40 = 170
  assert.strictEqual(isInDeleteZone(165, e), true);   // > 170-40 = 130
  assert.strictEqual(isInDeleteZone(80, e), false);
});

test('executionSvg emits hit-rects, data-sync dots, and a delete zone', () => {
  const svg = executionSvg({ n_procs: 3, syncs: [[0, 1]] });
  assert.strictEqual((svg.match(/class="lane-hit" data-proc="/g) || []).length, 3);
  assert.match(svg, /class="proc-label" data-proc="0"/);
  assert.strictEqual((svg.match(/class="event" data-sync="0"/g) || []).length, 2);
  assert.match(svg, /class="delete-zone"/);
  // existing structure preserved:
  assert.strictEqual((svg.match(/class="lane"/g) || []).length, 3);
  assert.strictEqual((svg.match(/class="sync"/g) || []).length, 1);
});
```

- [ ] **Step 3: Run tests**

Run: `mise run nomadim-editor-test`
Expected: `# pass 39`, `# fail 0` (35 + 4). The pre-existing `executionSvg` tests still pass (lane/sync counts unaffected; `class="lane-hit"` does not match `/class="lane"/`).

- [ ] **Step 4: Commit**

```bash
git add nomadim/editor/src/execution-svg.mjs nomadim/editor/test/execution.test.mjs
git commit -m "feat(nomadim): exec-svg geometry exports + drag-ready hit targets"
```

---

### Task 3: Pointer-event drag controller

**Files:** Create `nomadim/editor/src/execution-drag.mjs`.

- [ ] **Step 1: Write the controller**

```js
import { laneX, rowY, laneFromX, rowFromY, isInDeleteZone } from './execution-svg.mjs';

const SVGNS = 'http://www.w3.org/2000/svg';

// Classify the grabbed element into a gesture descriptor.
export function classifyTarget(el) {
  if (!el || !el.closest) return { kind: null };
  const conn = el.closest('[data-sync]');
  if (conn) return { kind: 'connector', sync: parseInt(conn.getAttribute('data-sync'), 10) };
  const label = el.closest('.proc-label');
  if (label) return { kind: 'header', proc: parseInt(label.getAttribute('data-proc'), 10) };
  const lane = el.closest('.lane-hit');
  if (lane) return { kind: 'lane', proc: parseInt(lane.getAttribute('data-proc'), 10) };
  return { kind: null };
}

// Attach drag editing to a freshly rendered swimlane <svg>. `handlers` =
// { onNewSync(a,b), onReorderProcess(from,to), onMoveSync(from,to), onDeleteSync(i) }.
// Window-level move/up listeners are added on pointerdown and removed on pointerup,
// so nothing leaks across re-renders (each render produces a new <svg>).
export function attachDrag(svgEl, execution, handlers) {
  const n = execution.n_procs;
  const nSyncs = execution.syncs.length;
  const deleteZone = svgEl.querySelector('.delete-zone');
  let drag = null;

  const toSvg = (ev) => {
    const pt = svgEl.createSVGPoint();
    pt.x = ev.clientX; pt.y = ev.clientY;
    return pt.matrixTransform(svgEl.getScreenCTM().inverse());
  };
  const clearHot = () => svgEl.querySelectorAll('.hot').forEach((e) => e.classList.remove('hot'));
  const hot = (sel) => { clearHot(); const e = svgEl.querySelector(sel); if (e) e.classList.add('hot'); };
  function clearFeedback() {
    svgEl.querySelectorAll('.drag-overlay').forEach((e) => e.remove());
    clearHot();
    if (deleteZone) deleteZone.classList.remove('active', 'hot');
  }
  function rubberBand(x1, y1, x2, y2) {
    let ln = svgEl.querySelector('line.drag-overlay');
    if (!ln) { ln = document.createElementNS(SVGNS, 'line'); ln.setAttribute('class', 'drag-overlay'); svgEl.appendChild(ln); }
    ln.setAttribute('x1', x1); ln.setAttribute('y1', y1);
    ln.setAttribute('x2', x2); ln.setAttribute('y2', y2);
  }

  function onMove(ev) {
    if (!drag) return;
    ev.preventDefault();
    const p = toSvg(ev);
    if (drag.kind === 'lane') {
      rubberBand(laneX(drag.proc), rowY(-1), p.x, p.y);
      const t = laneFromX(p.x, n);
      if (t >= 0) hot(`.lane-hit[data-proc="${t}"]`); else clearHot();
    } else if (drag.kind === 'header') {
      const t = laneFromX(p.x, n);
      if (t >= 0) hot(`.lane-hit[data-proc="${t}"]`); else clearHot();
    } else if (drag.kind === 'connector') {
      if (deleteZone) deleteZone.classList.add('active');
      if (isInDeleteZone(p.y, execution)) {
        clearHot();
        if (deleteZone) deleteZone.classList.add('hot');
      } else {
        if (deleteZone) deleteZone.classList.remove('hot');
        const to = rowFromY(p.y, nSyncs);
        if (to >= 0) hot(`.sync[data-sync="${to}"]`); else clearHot();
      }
    }
  }

  function onUp(ev) {
    if (!drag) return;
    const p = toSvg(ev);
    const d = drag;
    drag = null;
    window.removeEventListener('pointermove', onMove);
    window.removeEventListener('pointerup', onUp);
    clearFeedback();
    if (d.kind === 'lane') {
      const t = laneFromX(p.x, n);
      if (t >= 0 && t !== d.proc) handlers.onNewSync(d.proc, t);
    } else if (d.kind === 'header') {
      const t = laneFromX(p.x, n);
      if (t >= 0 && t !== d.proc) handlers.onReorderProcess(d.proc, t);
    } else if (d.kind === 'connector') {
      if (isInDeleteZone(p.y, execution)) handlers.onDeleteSync(d.sync);
      else {
        const to = rowFromY(p.y, nSyncs);
        if (to >= 0 && to !== d.sync) handlers.onMoveSync(d.sync, to);
      }
    }
  }

  function onDown(ev) {
    const c = classifyTarget(ev.target);
    if (!c.kind) return;
    ev.preventDefault();
    drag = c;
    window.addEventListener('pointermove', onMove);
    window.addEventListener('pointerup', onUp);
  }

  svgEl.addEventListener('pointerdown', onDown);
}
```

- [ ] **Step 2: Syntax-check**

Run: `node --check nomadim/editor/src/execution-drag.mjs && echo OK`
Expected: `OK`.

- [ ] **Step 3: Commit**

```bash
git add nomadim/editor/src/execution-drag.mjs
git commit -m "feat(nomadim): pointer-event drag controller for the swimlane"
```

---

### Task 4: Wire drag into the app + styles

**Files:** Modify `nomadim/editor/src/app.mjs`, `nomadim/editor/styles.css`.

- [ ] **Step 1: Import the new ops + controller in `app.mjs`**

Change the execution-edits import line to include the new ops, and add the drag import. The two lines become:

```js
import { emptyExecution, setNProcs, appendSync, removeLastSync, moveSync, removeSyncAt, reorderProcess } from './execution-edits.mjs';
import { renderExecution, clearExecution } from './execution-view.mjs';
import { attachDrag } from './execution-drag.mjs';
```

- [ ] **Step 2: Re-attach drag after each execution render**

In `app.mjs`, the `refresh()` execution branch currently reads:

```js
    } else if (v === 'execution' && model.execution) {
      renderExecution(els.exec, model.execution);
      els.verdict.textContent = `Execution: ${model.execution.n_procs} processes, ${model.execution.syncs.length} syncs`;
      els.realizer.textContent = '';
    } else {
```

Replace it with:

```js
    } else if (v === 'execution' && model.execution) {
      renderExecution(els.exec, model.execution);
      attachExecDrag();
      els.verdict.textContent = `Execution: ${model.execution.n_procs} processes, ${model.execution.syncs.length} syncs`;
      els.realizer.textContent = '';
    } else {
```

- [ ] **Step 3: Add the `attachExecDrag` helper**

In `app.mjs`, immediately after the `derivePoset()` function definition, add:

```js
  // Wire drag editing onto the freshly rendered swimlane. Each drag routes
  // through editExec, so it re-renders + re-attaches (no listener leak).
  function attachExecDrag() {
    const svg = els.exec.querySelector('svg');
    if (!svg || !model.execution) return;
    attachDrag(svg, model.execution, {
      onNewSync: (a, b) => editExec((e) => appendSync(e, a, b)),
      onReorderProcess: (from, to) => editExec((e) => reorderProcess(e, from, to)),
      onMoveSync: (from, to) => editExec((e) => moveSync(e, from, to)),
      onDeleteSync: (i) => editExec((e) => removeSyncAt(e, i)),
    });
  }
```

- [ ] **Step 4: Add a `currentExecution` test hook**

In the `window.__editor = { ... }` object in `app.mjs`, add this line after `currentYaml: () => currentYaml(),`:

```js
    currentExecution: () => model.execution,
```

- [ ] **Step 5: Append drag styles to `styles.css`**

```css
.exec-svg .lane-hit { cursor: crosshair; }
.exec-svg .lane-hit.hot { fill: rgba(79, 140, 255, 0.12); }
.exec-svg .proc-label { cursor: grab; }
.exec-svg .sync, .exec-svg .event { cursor: grab; }
.exec-svg .sync.hot { stroke-width: 4; }
.exec-svg .drag-overlay { stroke: #4f8cff; stroke-width: 2; stroke-dasharray: 4 3; pointer-events: none; }
.exec-svg .delete-zone { display: none; }
.exec-svg .delete-zone.active { display: block; }
.exec-svg .delete-zone rect { fill: #e0457b; opacity: 0.12; }
.exec-svg .delete-zone.hot rect { opacity: 0.32; }
.exec-svg .delete-zone text { fill: #e0457b; font: 11px system-ui; opacity: 0.7; pointer-events: none; }
```

- [ ] **Step 6: Syntax-check + unit tests**

Run: `node --check nomadim/editor/src/app.mjs && echo OK`
Expected: `OK`.
Run: `mise run nomadim-editor-test`
Expected: `# pass 39`, `# fail 0` (the wiring doesn't touch unit-tested pure modules).

- [ ] **Step 7: Commit**

```bash
git add nomadim/editor/src/app.mjs nomadim/editor/styles.css
git commit -m "feat(nomadim): wire swimlane drag editing into the app"
```

---

### Task 5: Playwright drag suite

**Files:** Create `nomadim/editor/e2e/execution-drag.spec.mjs`.

- [ ] **Step 1: Write the spec**

Create `nomadim/editor/e2e/execution-drag.spec.mjs`:

```js
import { test, expect } from '@playwright/test';

async function boot(page) {
  await page.goto('/index.html');
  await page.waitForFunction(() => window.__editor !== undefined);
}

// Center of a located element in page coordinates.
async function center(page, selector) {
  const box = await page.locator(selector).boundingBox();
  if (!box) throw new Error('no box for ' + selector);
  return { x: box.x + box.width / 2, y: box.y + box.height / 2 };
}

async function drag(page, from, to) {
  await page.mouse.move(from.x, from.y);
  await page.mouse.down();
  await page.mouse.move((from.x + to.x) / 2, (from.y + to.y) / 2, { steps: 4 });
  await page.mouse.move(to.x, to.y, { steps: 4 });
  await page.mouse.up();
}

test('dragging lane 0 to lane 1 creates a sync', async ({ page }) => {
  await boot(page);
  await page.evaluate(() => window.__editor.newExecution(3));
  await drag(page, await center(page, '.lane-hit[data-proc="0"]'),
                   await center(page, '.lane-hit[data-proc="1"]'));
  await expect.poll(() => page.evaluate(() => window.__editor.currentExecution().syncs)).toEqual([[0, 1]]);
});

test('dragging the first connector onto the second row reorders syncs', async ({ page }) => {
  await boot(page);
  await page.evaluate(() => {
    window.__editor.newExecution(3);
    window.__editor.appendSync(0, 1);
    window.__editor.appendSync(1, 2);
  });
  await drag(page, await center(page, '.sync[data-sync="0"]'),
                   await center(page, '.sync[data-sync="1"]'));
  await expect.poll(() => page.evaluate(() => window.__editor.currentExecution().syncs)).toEqual([[1, 2], [0, 1]]);
});

test('dragging a connector to the bottom deletes that sync', async ({ page }) => {
  await boot(page);
  await page.evaluate(() => {
    window.__editor.newExecution(3);
    window.__editor.appendSync(0, 1);
    window.__editor.appendSync(1, 2);
  });
  const svg = await page.locator('.exec-svg').boundingBox();
  const from = await center(page, '.sync[data-sync="0"]');
  await drag(page, from, { x: svg.x + svg.width / 2, y: svg.y + svg.height - 6 });
  // [0,1] removed, [1,2] remains
  await expect.poll(() => page.evaluate(() => window.__editor.currentExecution().syncs)).toEqual([[1, 2]]);
});

test('dragging a process header reorders processes and remaps syncs', async ({ page }) => {
  await boot(page);
  await page.evaluate(() => {
    window.__editor.newExecution(3);
    window.__editor.appendSync(0, 1);
    window.__editor.appendSync(1, 2);
  });
  // move process 0 onto lane 2's column: 0->2 ; old1->0, old2->1, old0->2
  await drag(page, await center(page, '.proc-label[data-proc="0"]'),
                   await center(page, '.lane-hit[data-proc="2"]'));
  await expect.poll(() => page.evaluate(() => window.__editor.currentExecution()))
    .toEqual({ n_procs: 3, syncs: [[2, 0], [0, 1]] });
});
```

- [ ] **Step 2: Run the browser suite**

Run: `mise run nomadim-editor-e2e` (timeout 600000).
Expected: the prior 15 tests + these 4 = `19 passed`. If a drag asserts the wrong result, investigate the real behavior — do NOT weaken. Common gotchas to check rather than mask: lane hit-rects must be present (Task 2) for `[data-proc]` to resolve; the delete drag must release below `svgHeight - MARGIN`; Playwright Chromium emits pointer events for `mouse.*`, which the controller listens to.

- [ ] **Step 3: Commit**

```bash
git add nomadim/editor/e2e/execution-drag.spec.mjs
git commit -m "test(nomadim): Playwright drag editing suite for the swimlane"
```

---

### Task 6: README + INDEX + final verification

**Files:** Modify `nomadim/editor/README.md`, `docs/INDEX.md`.

- [ ] **Step 1: Update the README**

In `nomadim/editor/README.md`, update the Phase 2b-iii status bullet to mention drag editing. Replace the existing `- **Phase 2b-iii (done):** ...` bullet with:

```markdown
- **Phase 2b-iii (done):** execution view — process swimlanes with ordered sync
  connectors, execution editing (process count, append/remove-last sync), and
  "Show derived poset". **Drag editing:** drag lane→lane to create a sync, drag a
  process header to reorder processes, drag a sync connector to reorder it, and
  drag a connector onto the delete strip to remove it (the toolbar still works too).
```

- [ ] **Step 2: Update INDEX**

In `docs/INDEX.md`, on the `wasm_bindings` row description, append: ` (incl. drag editing)`. Keep it on the same row; do not restructure.

- [ ] **Step 3: Final verification**

Run and confirm:
- `mise run nomadim-test` → `100% tests passed ... out of 77`.
- `mise run nomadim-editor-test` → `# pass 39`, `# fail 0`.
- `mise run nomadim-editor-e2e` → `19 passed`.

`git status --porcelain` must be clean.

- [ ] **Step 4: Commit**

```bash
git add nomadim/editor/README.md docs/INDEX.md
git commit -m "docs(nomadim): document drag-and-drop execution editing"
```

---

## Self-review notes (already reconciled)

- **Spec coverage:** all four gestures — new sync (lane-body drag → `appendSync`, Tasks 3/4/5), reorder process (header drag → `reorderProcess`, Tasks 1/3/4/5), reorder sync (connector drag → `moveSync`, Tasks 1/3/4/5), delete sync (connector→delete-zone → `removeSyncAt`, Tasks 1/3/4/5); handle-based mapping via `classifyTarget`; drag complements the toolbar (untouched); `executionSvg` stays pure with geometry exports + hit targets (Task 2); WASM untouched.
- **Testability:** pure ops + geometry helpers Node-unit-tested (Tasks 1–2); the DOM controller via Playwright real drags using `[data-proc]`/`[data-sync]` boundingBoxes + a `currentExecution()` hook (Task 5).
- **Type/name consistency:** `moveSync`/`removeSyncAt`/`reorderProcess`, `laneX`/`rowY`/`laneFromX`/`rowFromY`/`svgHeight`/`isInDeleteZone`, `classifyTarget`/`attachDrag`, the handler names (`onNewSync`/`onReorderProcess`/`onMoveSync`/`onDeleteSync`), `attachExecDrag`, and `currentExecution` are used identically across modules, app, and the Playwright spec. SVG classes (`lane-hit`, `proc-label`, `sync`, `event`, `delete-zone`, `drag-overlay`, `hot`) match between renderer, controller, CSS, and tests.
- **No leaks:** window pointer listeners are added on `pointerdown` and removed on `pointerup`; each re-render replaces the `<svg>`, so stale element listeners die with it.
- **No placeholders:** every code/command step is complete and runnable.
```
