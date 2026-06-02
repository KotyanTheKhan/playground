# nomadim editor — execution swimlane view (Phase 2b-iii) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add an execution view to the editor: render a distributed execution as process swimlanes with ordered synchronization connectors, edit it (set process count, append/remove syncs), and expand it to its poset (via the WASM module) shown in the existing poset view.

**Architecture:** A pure `execution-edits.mjs` (immutable execution ops) and a pure `execution-svg.mjs` (renders the execution as an SVG string — N vertical lanes + ordered horizontal sync connectors with event dots), both Node-unit-tested. A thin `execution-view.mjs` injects the SVG into a container. `app.mjs` gains a Poset/Execution view switcher, an execution toolbar, and a "Show derived poset" action that calls the WASM `expandExecution` and renders the result in the Cytoscape poset view. The swimlane shows the *abstract* execution (the `{n_procs, syncs}` model itself) — it does NOT re-implement the C++ event-DAG expansion in JS; the full expanded poset comes only from `expandExecution`, preserving WASM-as-single-source-of-truth.

**Tech Stack:** Vanilla ES modules, inline SVG for the swimlane, the existing vendored Cytoscape for the derived poset, the Phase-2a WASM module, Node ≥ 22 (`node:test`), Playwright. No new dependencies.

**Branch:** `nomadim-editor-2c` (already checked out, off `dev`).

**Spec:** `docs/superpowers/specs/2026-06-01-nomadim-poset-editor-design.md` §3 (Execution view — swimlane: each process a vertical lane, syncs as joins; "show derived poset"). This is the final phase of the editor design.

---

## Design decisions

- **Abstract swimlane (not the expanded event DAG).** The `Execution` model is exactly `{n_procs, syncs:[[a,b],…]}` (ordered). The swimlane draws that directly: process `p` is a vertical lane at x = `MARGIN + p*LANE_GAP`; sync `i` is a horizontal connector at y = `TOP + (i+1)*ROW_GAP` between lanes `a` and `b`, with a small event dot on each endpoint lane. This is faithful to the model and to the approved brainstorm mockup, and avoids duplicating `ProcessGraph::build` in JS. The full event-structure poset is obtained only via the WASM `expandExecution`.
- **Editing = set process count, append sync, remove last sync.** Syncs are an ordered list; v1 supports append and remove-last (arbitrary reorder/insert is deferred — note it in the README). `appendSync(a,b)` validates `a≠b` and both in `[0,n_procs)`.
- **View switcher.** Two buttons (Poset / Execution) toggle which container is visible. Loading a document selects the matching view (poset doc → poset view; execution doc → execution view). "Show derived poset" expands the current execution via WASM and switches to the poset view.
- **Conventions** unchanged: ES modules `.mjs`, tests `*.test.mjs`, adjacency JSON adjacency form, build/run via mise, no AI watermark.

## File structure

| File | Responsibility |
|------|----------------|
| `nomadim/editor/src/execution-edits.mjs` | Pure immutable execution ops: `emptyExecution`, `setNProcs`, `appendSync`, `removeLastSync`. |
| `nomadim/editor/src/execution-svg.mjs` | Pure `executionSvg(execution)` → SVG string (lanes, sync connectors, dots, labels). |
| `nomadim/editor/src/execution-view.mjs` | DOM: `renderExecution(container, execution)` sets the container's SVG. |
| `nomadim/editor/src/app.mjs` | (modify) view switcher, execution toolbar, expand-to-poset, `__editor` hooks. |
| `nomadim/editor/index.html` + `styles.css` | (modify) view tabs, execution toolbar + container. |
| `nomadim/editor/test/execution.test.mjs` | Node unit tests for edits + SVG builder. |
| `nomadim/editor/e2e/execution.spec.mjs` | Playwright: render, edit, derive poset. |
| `docs/INDEX.md`, `nomadim/editor/README.md` | Docs. |

---

### Task 1: Pure execution edit operations

**Files:** Create `nomadim/editor/src/execution-edits.mjs`, `nomadim/editor/test/execution.test.mjs`.

- [ ] **Step 1: Write the edit ops**

Create `nomadim/editor/src/execution-edits.mjs`:

```js
// Pure, immutable operations on an execution { n_procs, syncs:[[a,b],...] }.
// They return a NEW execution and throw Error on invalid requests.

export function emptyExecution(nProcs = 2) {
  return { n_procs: Math.max(0, nProcs | 0), syncs: [] };
}

// Set the process count. Drops any sync that references a now-out-of-range process.
export function setNProcs(exec, n) {
  const nProcs = Math.max(0, n | 0);
  return {
    n_procs: nProcs,
    syncs: exec.syncs.filter(([a, b]) => a < nProcs && b < nProcs).map(([a, b]) => [a, b]),
  };
}

// Append a synchronization between two distinct, in-range processes.
export function appendSync(exec, a, b) {
  if (a < 0 || b < 0 || a >= exec.n_procs || b >= exec.n_procs) throw new Error('process out of range');
  if (a === b) throw new Error('a sync needs two distinct processes');
  return { n_procs: exec.n_procs, syncs: [...exec.syncs.map(([x, y]) => [x, y]), [a, b]] };
}

export function removeLastSync(exec) {
  return { n_procs: exec.n_procs, syncs: exec.syncs.slice(0, -1).map(([x, y]) => [x, y]) };
}
```

- [ ] **Step 2: Write the unit tests (edits portion)**

Create `nomadim/editor/test/execution.test.mjs`:

```js
import test from 'node:test';
import assert from 'node:assert';
import { emptyExecution, setNProcs, appendSync, removeLastSync } from '../src/execution-edits.mjs';
import { executionSvg } from '../src/execution-svg.mjs';

test('emptyExecution has the requested process count and no syncs', () => {
  assert.deepStrictEqual(emptyExecution(3), { n_procs: 3, syncs: [] });
  assert.deepStrictEqual(emptyExecution(), { n_procs: 2, syncs: [] });
});

test('appendSync adds a valid sync and rejects bad ones', () => {
  const e = appendSync({ n_procs: 3, syncs: [] }, 0, 2);
  assert.deepStrictEqual(e.syncs, [[0, 2]]);
  assert.throws(() => appendSync(e, 1, 1), /distinct/);
  assert.throws(() => appendSync(e, 0, 5), /out of range/);
});

test('removeLastSync drops the final sync only', () => {
  const e = removeLastSync({ n_procs: 2, syncs: [[0, 1], [1, 0]] });
  assert.deepStrictEqual(e.syncs, [[0, 1]]);
});

test('setNProcs drops syncs that fall out of range', () => {
  const e = setNProcs({ n_procs: 4, syncs: [[0, 1], [2, 3]] }, 2);
  assert.strictEqual(e.n_procs, 2);
  assert.deepStrictEqual(e.syncs, [[0, 1]]); // [2,3] dropped
});

test('ops do not mutate their input', () => {
  const e = { n_procs: 2, syncs: [[0, 1]] };
  appendSync(e, 1, 0);
  removeLastSync(e);
  setNProcs(e, 1);
  assert.deepStrictEqual(e, { n_procs: 2, syncs: [[0, 1]] });
});
```

(The `executionSvg` import is used by tests added in Task 2; it is imported now so the file compiles once Task 2 lands. If you run the suite before Task 2, this file will error on the missing import — that is expected; run it after Task 2, OR temporarily comment the import. To keep Task 1 green on its own, the import line and SVG tests are added in Task 2; **for Task 1, omit the `executionSvg` import line and add it in Task 2.**)

For Task 1, the file's first two lines are ONLY:

```js
import test from 'node:test';
import assert from 'node:assert';
import { emptyExecution, setNProcs, appendSync, removeLastSync } from '../src/execution-edits.mjs';
```

(Do not import `executionSvg` yet — Task 2 adds it.)

- [ ] **Step 3: Run the tests**

Run: `mise run nomadim-editor-test`
Expected: `# pass 28`, `# fail 0` (23 existing + 5 here).

- [ ] **Step 4: Commit**

```bash
git add nomadim/editor/src/execution-edits.mjs nomadim/editor/test/execution.test.mjs
git commit -m "feat(nomadim): editor pure execution edit ops"
```

---

### Task 2: Pure execution SVG renderer

**Files:** Create `nomadim/editor/src/execution-svg.mjs`; modify `nomadim/editor/test/execution.test.mjs` (add import + SVG tests).

- [ ] **Step 1: Write the SVG builder**

Create `nomadim/editor/src/execution-svg.mjs`:

```js
// Pure renderer: turn an execution { n_procs, syncs } into an SVG string showing
// process swimlanes (vertical lanes) and ordered synchronization connectors
// (horizontal, with an event dot on each endpoint lane). Returns a complete
// <svg> element string. No DOM access — unit-testable.

const MARGIN = 40;     // left/top padding
const LANE_GAP = 90;   // horizontal gap between process lanes
const ROW_GAP = 50;    // vertical gap between sync rows
const TOP = 30;        // y of the first sync row baseline

export function executionSvg(execution) {
  const n = execution.n_procs;
  const syncs = execution.syncs;
  const width = MARGIN * 2 + Math.max(0, n - 1) * LANE_GAP;
  const height = TOP + (syncs.length + 1) * ROW_GAP + MARGIN;
  const laneX = (p) => MARGIN + p * LANE_GAP;
  const rowY = (i) => TOP + (i + 1) * ROW_GAP;

  const parts = [];
  parts.push(`<svg xmlns="http://www.w3.org/2000/svg" width="${width}" height="${height}" class="exec-svg" data-procs="${n}" data-syncs="${syncs.length}">`);

  // Lanes + process labels.
  for (let p = 0; p < n; p++) {
    const x = laneX(p);
    parts.push(`<line class="lane" x1="${x}" y1="${TOP}" x2="${x}" y2="${height - MARGIN}" />`);
    parts.push(`<text class="proc-label" x="${x}" y="${TOP - 10}" text-anchor="middle">P${p}</text>`);
  }

  // Sync connectors (in order, top to bottom) + endpoint dots + index labels.
  syncs.forEach(([a, b], i) => {
    const y = rowY(i);
    const xa = laneX(a), xb = laneX(b);
    parts.push(`<line class="sync" x1="${xa}" y1="${y}" x2="${xb}" y2="${y}" data-sync="${i}" data-a="${a}" data-b="${b}" />`);
    parts.push(`<circle class="event" cx="${xa}" cy="${y}" r="5" />`);
    parts.push(`<circle class="event" cx="${xb}" cy="${y}" r="5" />`);
    parts.push(`<text class="sync-label" x="${Math.min(xa, xb) - 12}" y="${y + 4}" text-anchor="end">${i}</text>`);
  });

  parts.push(`</svg>`);
  return parts.join('');
}
```

- [ ] **Step 2: Add the import + SVG tests to `execution.test.mjs`**

Add this import line to the top of `nomadim/editor/test/execution.test.mjs` (after the existing imports):

```js
import { executionSvg } from '../src/execution-svg.mjs';
```

And append these tests:

```js
test('executionSvg renders one lane per process and one connector per sync', () => {
  const svg = executionSvg({ n_procs: 3, syncs: [[0, 1], [1, 2]] });
  assert.match(svg, /^<svg /);
  assert.match(svg, /data-procs="3"/);
  assert.match(svg, /data-syncs="2"/);
  assert.strictEqual((svg.match(/class="lane"/g) || []).length, 3);
  assert.strictEqual((svg.match(/class="sync"/g) || []).length, 2);
  // each sync carries its endpoints
  assert.match(svg, /data-sync="0" data-a="0" data-b="1"/);
  assert.match(svg, /data-sync="1" data-a="1" data-b="2"/);
});

test('executionSvg handles an empty execution', () => {
  const svg = executionSvg({ n_procs: 0, syncs: [] });
  assert.match(svg, /data-procs="0"/);
  assert.strictEqual((svg.match(/class="lane"/g) || []).length, 0);
  assert.strictEqual((svg.match(/class="sync"/g) || []).length, 0);
});
```

- [ ] **Step 3: Run the tests**

Run: `mise run nomadim-editor-test`
Expected: `# pass 30`, `# fail 0` (28 + 2).

- [ ] **Step 4: Commit**

```bash
git add nomadim/editor/src/execution-svg.mjs nomadim/editor/test/execution.test.mjs
git commit -m "feat(nomadim): editor pure execution swimlane SVG renderer"
```

---

### Task 3: Execution view module (DOM)

**Files:** Create `nomadim/editor/src/execution-view.mjs`.

- [ ] **Step 1: Write the view module**

Create `nomadim/editor/src/execution-view.mjs`:

```js
import { executionSvg } from './execution-svg.mjs';

// Render the execution as a swimlane SVG into `container` (replacing its content).
export function renderExecution(container, execution) {
  container.innerHTML = executionSvg(execution);
}

export function clearExecution(container) {
  container.innerHTML = '';
}
```

- [ ] **Step 2: Syntax-check**

Run: `node --check nomadim/editor/src/execution-view.mjs && echo OK`
Expected: `OK`.

- [ ] **Step 3: Commit**

```bash
git add nomadim/editor/src/execution-view.mjs
git commit -m "feat(nomadim): editor execution-view DOM renderer"
```

---

### Task 4: App — view switcher, execution toolbar, derive-poset

**Files:** Modify `nomadim/editor/src/app.mjs`, `nomadim/editor/index.html`, `nomadim/editor/styles.css`.

- [ ] **Step 1: Rewrite `app.mjs`**

Replace the ENTIRE contents of `nomadim/editor/src/app.mjs` with:

```js
import { makeClient } from './wasm-client.mjs';
import { emptyModel, hasPoset, posetAdjacency } from './model.mjs';
import { yamlToModel, modelToYaml } from './yaml-sync.mjs';
import { computeVerdict, verdictText } from './verdict.mjs';
import { initPosetView, renderPoset, setCriticalOverlay, clearCriticalOverlay } from './poset-view.mjs';
import { emptyPoset, addVertex, removeVertex, addEdge, removeEdge } from './edits.mjs';
import { realizerColumns } from './realizer.mjs';
import { saveText } from './file-save.mjs';
import { emptyExecution, setNProcs, appendSync, removeLastSync } from './execution-edits.mjs';
import { renderExecution, clearExecution } from './execution-view.mjs';

async function main() {
  const client = await makeClient(window.createNomadim);
  const cy = initPosetView(document.getElementById('cy'));
  let model = emptyModel();
  let view = 'poset'; // 'poset' | 'execution'

  const ids = ['version', 'verdict', 'yaml', 'apply', 'file', 'error',
               'new', 'addv', 'adde', 'del', 'edge-u', 'edge-v', 'critical', 'realizer', 'save',
               'tab-poset', 'tab-exec', 'poset-pane', 'exec-pane', 'exec',
               'nprocs', 'sync-a', 'sync-b', 'addsync', 'delsync', 'derive'];
  const els = {};
  for (const id of ids) els[id] = document.getElementById(id);
  els.version.textContent = 'libnomadim ' + client.version();

  const showError = (msg) => { els.error.textContent = msg || ''; };

  function setView(v) {
    view = v;
    els['poset-pane'].style.display = v === 'poset' ? '' : 'none';
    els['exec-pane'].style.display = v === 'execution' ? '' : 'none';
    els['tab-poset'].classList.toggle('active', v === 'poset');
    els['tab-exec'].classList.toggle('active', v === 'execution');
    if (v === 'poset') cy.resize();
  }

  function renderRealizer(adj) {
    const cols = realizerColumns(client, adj);
    els.realizer.textContent = cols
      ? `realizer  L1: [${cols.l1.join(', ')}]   L2: [${cols.l2.join(', ')}]` : '';
  }

  function refresh({ syncYaml = true } = {}) {
    showError('');
    if (hasPoset(model)) {
      const adj = posetAdjacency(model);
      renderPoset(cy, model.poset);
      els.verdict.textContent = verdictText(computeVerdict(client, adj));
      renderRealizer(adj);
      if (els.critical.checked) setCriticalOverlay(cy, client.criticalPairs(adj));
    } else if (model.execution) {
      renderExecution(els.exec, model.execution);
      els.verdict.textContent = `Execution: ${model.execution.n_procs} processes, ${model.execution.syncs.length} syncs`;
      els.realizer.textContent = '';
    } else {
      cy.elements().remove();
      clearExecution(els.exec);
      els.verdict.textContent = 'No document loaded.';
      els.realizer.textContent = '';
    }
    if (syncYaml) els.yaml.value = modelToYaml(client, model);
  }

  // Poset edit helper (model holds a poset).
  function editPoset(fn) {
    if (!hasPoset(model)) { showError('Create or load a poset first (New poset).'); return; }
    try { model = { poset: fn(model.poset), execution: null }; setView('poset'); refresh(); }
    catch (e) { showError(e && e.message ? e.message : String(e)); }
  }

  // Execution edit helper (model holds an execution).
  function editExec(fn) {
    if (!model.execution) { showError('Create or load an execution first (New execution).'); return; }
    try { model = { poset: null, execution: fn(model.execution) }; setView('execution'); refresh(); }
    catch (e) { showError(e && e.message ? e.message : String(e)); }
  }

  function loadText(text) {
    try {
      model = yamlToModel(client, text);
      setView(model.execution && !model.poset ? 'execution' : 'poset');
      refresh();
    } catch (e) { showError('Could not load document: ' + (e && e.message ? e.message : e)); }
  }

  function deleteSelected() {
    if (!hasPoset(model)) return;
    const nodeIdx = cy.$('node:selected').map((n) => parseInt(n.id().slice(1), 10));
    const edgeSel = cy.$('edge:selected').filter((e) => !e.hasClass('critical'))
      .map((e) => [parseInt(e.data('source').slice(1), 10), parseInt(e.data('target').slice(1), 10)]);
    let poset = model.poset;
    for (const [u, v] of edgeSel) poset = removeEdge(poset, u, v);
    for (const i of nodeIdx.sort((a, b) => b - a)) poset = removeVertex(poset, i);
    model = { poset, execution: null };
    refresh();
  }

  // Expand the current execution to its poset (via WASM) and show the poset view.
  function derivePoset() {
    if (!model.execution) { showError('Load or build an execution first.'); return; }
    try {
      const poset = client.expandExecution(model.execution);
      model = { poset, execution: null };
      setView('poset');
      refresh();
    } catch (e) { showError('Expand failed: ' + (e && e.message ? e.message : e)); }
  }

  // --- view tabs ---
  els['tab-poset'].addEventListener('click', () => setView('poset'));
  els['tab-exec'].addEventListener('click', () => setView('execution'));

  // --- poset toolbar ---
  els.new.addEventListener('click', () => { model = { poset: emptyPoset(), execution: null }; setView('poset'); refresh(); });
  els.addv.addEventListener('click', () => editPoset(addVertex));
  els.adde.addEventListener('click', () => {
    const u = parseInt(els['edge-u'].value, 10), v = parseInt(els['edge-v'].value, 10);
    if (Number.isNaN(u) || Number.isNaN(v)) { showError('Enter source and target vertex numbers.'); return; }
    editPoset((p) => addEdge(p, u, v));
  });
  els.del.addEventListener('click', deleteSelected);
  els.critical.addEventListener('change', () => {
    if (!hasPoset(model)) return;
    if (els.critical.checked) setCriticalOverlay(cy, client.criticalPairs(posetAdjacency(model)));
    else clearCriticalOverlay(cy);
  });

  // --- execution toolbar ---
  els.nprocs.addEventListener('change', () => {
    const n = parseInt(els.nprocs.value, 10);
    if (Number.isNaN(n) || n < 0) { showError('Process count must be a non-negative integer.'); return; }
    if (!model.execution) { model = { poset: null, execution: emptyExecution(n) }; setView('execution'); refresh(); }
    else editExec((e) => setNProcs(e, n));
  });
  els.addsync.addEventListener('click', () => {
    const a = parseInt(els['sync-a'].value, 10), b = parseInt(els['sync-b'].value, 10);
    if (Number.isNaN(a) || Number.isNaN(b)) { showError('Enter two process numbers for the sync.'); return; }
    editExec((e) => appendSync(e, a, b));
  });
  els.delsync.addEventListener('click', () => editExec(removeLastSync));
  els.derive.addEventListener('click', derivePoset);

  // --- shared ---
  els.save.addEventListener('click', async () => {
    try { await saveText(modelToYaml(client, model) || '', model.execution ? 'execution.yaml' : 'poset.yaml'); }
    catch (e) { if (e && e.name !== 'AbortError') showError('Save failed: ' + (e.message || e)); }
  });
  els.apply.addEventListener('click', () => {
    try {
      model = yamlToModel(client, els.yaml.value);
      setView(model.execution && !model.poset ? 'execution' : 'poset');
      refresh({ syncYaml: false });
    } catch (e) { showError('Invalid YAML: ' + (e && e.message ? e.message : e)); }
  });
  els.file.addEventListener('change', async (ev) => {
    const f = ev.target.files[0];
    if (f) loadText(await f.text());
  });

  setView('poset');
  refresh();

  // Test hooks for Playwright (deterministic; bypass DOM selection).
  window.__editor = {
    loadText,
    newPoset: () => { model = { poset: emptyPoset(), execution: null }; setView('poset'); refresh(); },
    addVertex: () => editPoset(addVertex),
    addEdge: (u, v) => editPoset((p) => addEdge(p, u, v)),
    removeVertex: (i) => editPoset((p) => removeVertex(p, i)),
    setCritical: (on) => { els.critical.checked = on; els.critical.dispatchEvent(new Event('change')); },
    newExecution: (n) => { model = { poset: null, execution: emptyExecution(n) }; setView('execution'); refresh(); },
    appendSync: (a, b) => editExec((e) => appendSync(e, a, b)),
    removeLastSync: () => editExec(removeLastSync),
    derivePoset,
    currentView: () => view,
    laneCount: () => els.exec.querySelectorAll('.lane').length,
    syncCount: () => els.exec.querySelectorAll('.sync').length,
    realizerText: () => els.realizer.textContent,
    currentYaml: () => modelToYaml(client, model),
    nodeCount: () => cy.nodes().length,
    criticalCount: () => cy.$('edge.critical').length,
    verdictText: () => els.verdict.textContent,
    errorText: () => els.error.textContent,
  };
}

main().catch((e) => {
  const bar = document.getElementById('error');
  if (bar) bar.textContent = 'Editor failed to start: ' + (e && e.message ? e.message : e);
});
```

- [ ] **Step 2: Replace `index.html`** with (adds view tabs, an execution toolbar, and the two panes):

```html
<!DOCTYPE html>
<html lang="en">
<head>
  <meta charset="utf-8" />
  <meta name="viewport" content="width=device-width, initial-scale=1" />
  <title>nomadim editor</title>
  <link rel="stylesheet" href="styles.css" />
  <script src="vendor/cytoscape.min.js"></script>
  <script src="vendor/dagre.min.js"></script>
  <script src="vendor/cytoscape-dagre.js"></script>
  <script src="public/nomadim.js"></script>
</head>
<body>
  <header>
    <h1>nomadim editor</h1>
    <span id="version"></span>
    <label>Load <input id="file" type="file" accept=".yaml,.yml" /></label>
    <button id="save">Save</button>
    <span class="tabs"><button id="tab-poset" class="active">Poset</button><button id="tab-exec">Execution</button></span>
  </header>
  <div id="toolbar">
    <span class="grp" id="poset-tools">
      <button id="new">New poset</button>
      <button id="addv">Add vertex</button>
      <label>edge <input id="edge-u" type="number" min="0" class="vnum" /> &rarr;
        <input id="edge-v" type="number" min="0" class="vnum" /></label>
      <button id="adde">Add edge</button>
      <button id="del">Delete selected</button>
      <label><input id="critical" type="checkbox" /> critical pairs</label>
    </span>
    <span class="sep"></span>
    <span class="grp" id="exec-tools">
      procs <input id="nprocs" type="number" min="0" class="vnum" />
      <label>sync <input id="sync-a" type="number" min="0" class="vnum" /> &harr;
        <input id="sync-b" type="number" min="0" class="vnum" /></label>
      <button id="addsync">Add sync</button>
      <button id="delsync">Remove last sync</button>
      <button id="derive">Show derived poset</button>
    </span>
  </div>
  <div id="verdict">No document loaded.</div>
  <div id="realizer"></div>
  <div id="error"></div>
  <main>
    <div id="view">
      <div id="poset-pane"><div id="cy"></div></div>
      <div id="exec-pane" style="display:none"><div id="exec"></div></div>
    </div>
    <div id="side">
      <textarea id="yaml" spellcheck="false" placeholder="poset / execution YAML"></textarea>
      <div class="controls"><button id="apply">Apply YAML</button></div>
    </div>
  </main>
  <script type="module" src="src/app.mjs"></script>
</body>
</html>
```

- [ ] **Step 3: Append to `styles.css`**:

```css
header .tabs { margin-left: auto; }
header .tabs button { background: #2a3140; color: #cfd6e4; border: 1px solid #3a4357; }
header .tabs button.active { background: #4f8cff; color: #fff; }
#view { flex: 2; min-width: 0; display: flex; }
#poset-pane, #exec-pane { flex: 1; min-width: 0; }
#cy { width: 100%; height: 100%; background: #fff; }
#exec-pane { overflow: auto; background: #fff; }
#exec { padding: 8px; }
.exec-svg .lane { stroke: #ccd; stroke-width: 1; }
.exec-svg .sync { stroke: #ff7043; stroke-width: 2; stroke-dasharray: 5 3; }
.exec-svg .event { fill: #2ca06c; }
.exec-svg .proc-label { fill: #555; font: 12px system-ui; }
.exec-svg .sync-label { fill: #999; font: 11px ui-monospace, monospace; }
#toolbar .grp { display: flex; align-items: center; gap: 8px; flex-wrap: wrap; }
```

Note: the old `#cy { flex: 2; ... }` rule from 2b-i is superseded by the `#view`/`#cy` rules above (since `#cy` now lives inside `#poset-pane`). The CSS cascade uses the later rule; leaving the old rule in place is harmless, but if it sets a conflicting `flex` on `#cy`, the new `#cy { width:100%; height:100% }` governs sizing inside the pane. Do not delete other rules.

- [ ] **Step 4: Syntax-check + unit tests**

Run: `node --check nomadim/editor/src/app.mjs && echo OK`
Expected: `OK`.
Run: `mise run nomadim-editor-test`
Expected: `# pass 30`, `# fail 0` (DOM changes don't affect the unit-tested pure modules).

- [ ] **Step 5: Commit**

```bash
git add nomadim/editor/src/app.mjs nomadim/editor/index.html nomadim/editor/styles.css
git commit -m "feat(nomadim): editor execution view, swimlane toolbar, derive-poset"
```

---

### Task 5: Playwright execution suite

**Files:** Create `nomadim/editor/e2e/execution.spec.mjs`.

- [ ] **Step 1: Write the spec**

Create `nomadim/editor/e2e/execution.spec.mjs`:

```js
import { test, expect } from '@playwright/test';

async function boot(page) {
  await page.goto('/index.html');
  await page.waitForFunction(() => window.__editor !== undefined);
}

const EXEC_DIM2 = `execution:
  n_procs: 2
  syncs:
    - [0, 1]
`;

test('loading an execution shows the execution view with lanes and a sync', async ({ page }) => {
  await boot(page);
  await page.evaluate((yaml) => window.__editor.loadText(yaml), EXEC_DIM2);
  await expect.poll(() => page.evaluate(() => window.__editor.currentView())).toBe('execution');
  await expect.poll(() => page.evaluate(() => window.__editor.laneCount())).toBe(2);
  await expect.poll(() => page.evaluate(() => window.__editor.syncCount())).toBe(1);
  await expect(page.locator('#verdict')).toContainText('2 processes, 1 syncs');
});

test('building an execution by editing updates the swimlane', async ({ page }) => {
  await boot(page);
  await page.evaluate(() => window.__editor.newExecution(3));
  await expect.poll(() => page.evaluate(() => window.__editor.laneCount())).toBe(3);
  await page.evaluate(() => { window.__editor.appendSync(0, 1); window.__editor.appendSync(1, 2); });
  await expect.poll(() => page.evaluate(() => window.__editor.syncCount())).toBe(2);
  await page.evaluate(() => window.__editor.removeLastSync());
  await expect.poll(() => page.evaluate(() => window.__editor.syncCount())).toBe(1);
});

test('an invalid sync is rejected with an error', async ({ page }) => {
  await boot(page);
  await page.evaluate(() => window.__editor.newExecution(2));
  await page.evaluate(() => window.__editor.appendSync(1, 1)); // same process
  await expect(page.locator('#error')).toContainText('distinct');
  await expect.poll(() => page.evaluate(() => window.__editor.syncCount())).toBe(0);
});

test('Show derived poset expands the execution and switches to the poset view', async ({ page }) => {
  await boot(page);
  await page.evaluate(() => { window.__editor.newExecution(2); window.__editor.appendSync(0, 1); });
  await page.evaluate(() => window.__editor.derivePoset());
  await expect.poll(() => page.evaluate(() => window.__editor.currentView())).toBe('poset');
  await expect.poll(() => page.evaluate(() => window.__editor.nodeCount())).toBeGreaterThan(0);
  // a single-sync 2-process execution expands to a dimension-2 poset
  await expect(page.locator('#verdict')).toContainText('Dimension <= 2: YES');
});
```

- [ ] **Step 2: Run the browser suite**

Run: `mise run nomadim-editor-e2e` (timeout 600000).
Expected: the prior 9 tests (`app.spec.mjs` 4 + `editing.spec.mjs` 5) PLUS these 4 = `13 passed`. Investigate failures against real behavior; do not weaken assertions. If the derived-poset verdict differs, confirm against `nomadim check` on the same execution (`mise run nomadim-build` then `./nomadim/build/nomadim check nomadim/data/exec_dim2.yaml` → "YES") before changing any expectation.

- [ ] **Step 3: Commit**

```bash
git add nomadim/editor/e2e/execution.spec.mjs
git commit -m "test(nomadim): Playwright execution swimlane + derive-poset suite"
```

---

### Task 6: README + INDEX + final verification

**Files:** Modify `nomadim/editor/README.md`, `docs/INDEX.md`.

- [ ] **Step 1: Update the README status**

In `nomadim/editor/README.md`, replace the `## Status` section with:

```markdown
## Status

- **Phase 2a (done):** the WASM core + a headless Node faithfulness test harness.
- **Phase 2b-i (done):** browser viewer — load a YAML poset/execution, layered
  Hasse diagram, live dimension-≤-2 verdict, editable YAML panel.
- **Phase 2b-ii (done):** poset editing — add/remove vertices & edges (cycles
  rejected), critical-pair highlight, realizer panel, and Save.
- **Phase 2b-iii (done):** execution view — process swimlanes with ordered sync
  connectors, execution editing (process count, append/remove-last sync), and
  "Show derived poset" (expands via the WASM module into the poset view).

Sync editing is append / remove-last; arbitrary reorder/insert is not yet
supported. The swimlane shows the abstract execution; the full event-structure
poset is produced by "Show derived poset".
```

- [ ] **Step 2: Update INDEX**

In `docs/INDEX.md`, on the `wasm_bindings` row description, append: ` + execution swimlane view & expand-to-poset`. Keep it on the same row.

- [ ] **Step 3: Final verification — all suites**

Run and confirm:
- `mise run nomadim-test` → `100% tests passed ... out of 77`.
- `mise run nomadim-editor-test` → `# pass 30`, `# fail 0`.
- `mise run nomadim-editor-e2e` → `13 passed`.

`git status --porcelain` must be clean.

- [ ] **Step 4: Commit**

```bash
git add nomadim/editor/README.md docs/INDEX.md
git commit -m "docs(nomadim): document the execution swimlane view (phase 2b-iii)"
```

---

## Self-review notes (already reconciled)

- **Spec coverage:** §3 Execution view — swimlanes (Task 2 SVG, Task 3 view, Task 4 wiring), execution editing (Task 1 ops, Task 4 toolbar), and "show derived poset" via the WASM `expandExecution` (Task 4 `derivePoset`). This completes the editor design.
- **WASM-as-truth preserved:** the swimlane renders only the abstract `{n_procs, syncs}` model; the expanded poset comes solely from `expandExecution` — no JS reimplementation of `ProcessGraph::build`.
- **Testability:** `execution-edits` and `execution-svg` are pure and Node-unit-tested (the SVG via string/attribute assertions); the DOM (view switch, swimlane injection, derive) is covered by Playwright via `window.__editor` hooks (`currentView`, `laneCount`, `syncCount`, `newExecution`, `appendSync`, `removeLastSync`, `derivePoset`).
- **Type/name consistency:** `emptyExecution`/`setNProcs`/`appendSync`/`removeLastSync`, `executionSvg`, `renderExecution`/`clearExecution`, the new DOM ids (`tab-poset`, `tab-exec`, `poset-pane`, `exec-pane`, `exec`, `nprocs`, `sync-a`, `sync-b`, `addsync`, `delsync`, `derive`), and the `__editor` hook names are used identically across the module, the app, the HTML, and the Playwright spec. The poset-side ids/hooks from 2b-ii are preserved unchanged.
- **No placeholders:** every code and command step is complete. (Task 1 explicitly notes the `executionSvg` test import is added in Task 2 so the test file is green at each step.)
```
