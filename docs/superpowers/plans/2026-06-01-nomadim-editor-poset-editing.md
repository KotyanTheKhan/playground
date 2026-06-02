# nomadim editor — poset interactive editing + verdict extras (Phase 2b-ii) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Turn the read-only poset viewer into an editor: add/remove vertices and edges (with cycle rejection), highlight critical pairs, show the realizer (two linear extensions) when dim ≤ 2, and save the document to disk — with the diagram, verdict, and YAML panel all staying in sync on every edit.

**Architecture:** New pure ES-module logic — graph reachability (`graph.mjs`), immutable poset edit operations (`edits.mjs`), a critical-pair overlay builder, and a realizer shaper — each Node-unit-tested against the real WASM module. The DOM layer (`poset-view.mjs`, `app.mjs`) gains a toolbar, a critical-pair toggle, a realizer panel, and a save button; it re-runs the WASM dim-2 check after every structural edit. A `file-save.mjs` uses the File System Access API with a download fallback. The Playwright suite drives editing/highlight/realizer/save through the page.

**Tech Stack:** Vanilla ES modules + the existing vendored Cytoscape/dagre + the Phase-2a WASM module, Node ≥ 22 (`node:test`), Playwright. No new vendored libraries (edge creation is click/input-driven, not drag).

**Branch:** `nomadim-editor-2b` (already checked out, off `dev`).

**Spec:** `docs/superpowers/specs/2026-06-01-nomadim-poset-editor-design.md` §3 (Poset view editing, verdict bar with critical-pair highlight + realizer panel) and §4 (File System Access save).

---

## Scope & deviations

- **In scope:** interactive **poset** editing (add vertex, remove selected, add/remove edge with acyclicity enforced), critical-pair highlighting, the realizer panel, File System Access save (+ download fallback), and two polish items from the 2b-i review (top-level `main().catch`; the execution-only verdict message).
- **Deferred to Phase 2b-iii:** the execution **swimlane** view and execution editing. In 2b-ii, an execution-only document still loads and can be expanded to a poset via the YAML panel, but there is no swimlane editor yet.
- **Edge-creation UX deviation (approved):** the spec said "draw an edge by dragging" (cytoscape-edgehandles). We instead use two small **source/target number inputs + an "Add edge" button**. No extra dependency, deterministic, fully testable. The add-edge *logic* is a pure model op; the button is one thin caller.
- **Conventions** (unchanged from 2b-i): adjacency JSON is array-of-arrays adjacency form (`edges[u]` lists `v` with `u < v`); ES modules are `.mjs`; tests are `*.test.mjs`/`*.test.cjs` under `nomadim/editor/test/`; build/run via mise tasks; no AI watermark in commits.

## File structure

| File | Responsibility |
|------|----------------|
| `nomadim/editor/src/graph.mjs` | Pure reachability: `reaches(adj, a, b)`. |
| `nomadim/editor/src/edits.mjs` | Pure immutable poset edits: `emptyPoset`, `addVertex`, `removeVertex`, `addEdge` (cycle-rejecting), `removeEdge`. |
| `nomadim/editor/src/cytoscape-elements.mjs` | (modify) add `criticalPairsToElements(pairs)`. |
| `nomadim/editor/src/realizer.mjs` | Pure `realizerColumns(client, adjacency)` → `{l1,l2}` or `null`. |
| `nomadim/editor/src/poset-view.mjs` | (modify) critical-overlay + selection styling; `setCriticalOverlay`/`clearCriticalOverlay`. |
| `nomadim/editor/src/file-save.mjs` | `saveText(text, name)` — FS Access API or download fallback. |
| `nomadim/editor/src/app.mjs` | (rewrite) toolbar, critical toggle, realizer panel, save, re-verify on edit, `window.__editor` hooks, `main().catch`. |
| `nomadim/editor/index.html` + `styles.css` | (modify) toolbar, critical checkbox, realizer panel, save button. |
| `nomadim/editor/test/edits.test.mjs`, `overlay-realizer.test.mjs` | Node unit tests. |
| `nomadim/editor/e2e/editing.spec.mjs` | Playwright editing/highlight/realizer/save tests. |
| `docs/INDEX.md`, `nomadim/editor/README.md` | Docs. |

---

### Task 1: Pure graph reachability + poset edit operations

**Files:** Create `nomadim/editor/src/graph.mjs`, `nomadim/editor/src/edits.mjs`, `nomadim/editor/test/edits.test.mjs`.

- [ ] **Step 1: Write the reachability helper**

Create `nomadim/editor/src/graph.mjs`:

```js
// Pure graph reachability over an adjacency list (edges[u] lists v with u < v).
// reaches(adj, a, b): true iff there is a directed path a -> ... -> b of length >= 1.
export function reaches(adj, a, b) {
  const seen = new Array(adj.length).fill(false);
  const stack = [a];
  while (stack.length) {
    const x = stack.pop();
    for (const y of adj[x]) {
      if (y === b) return true;
      if (!seen[y]) { seen[y] = true; stack.push(y); }
    }
  }
  return false;
}
```

- [ ] **Step 2: Write the immutable edit operations**

Create `nomadim/editor/src/edits.mjs`:

```js
import { reaches } from './graph.mjs';

// All operations return a NEW poset { n_vertices, edges } (adjacency form) and
// never mutate the input. They throw Error on invalid requests so the UI can
// surface a message.

export function emptyPoset() {
  return { n_vertices: 0, edges: [] };
}

export function addVertex(poset) {
  return {
    n_vertices: poset.n_vertices + 1,
    edges: [...poset.edges.map((r) => [...r]), []],
  };
}

// Remove vertex `idx`, dropping incident edges and renumbering higher vertices.
export function removeVertex(poset, idx) {
  const n = poset.n_vertices;
  if (idx < 0 || idx >= n) throw new Error('vertex out of range: ' + idx);
  const remap = (x) => (x > idx ? x - 1 : x);
  const edges = [];
  for (let u = 0; u < n; u++) {
    if (u === idx) continue;
    edges.push(poset.edges[u].filter((v) => v !== idx).map(remap));
  }
  return { n_vertices: n - 1, edges };
}

// Add edge u -> v (meaning u < v). Rejects self-loops, out-of-range endpoints,
// duplicates, and any edge that would create a cycle (v already reaches u).
export function addEdge(poset, u, v) {
  const n = poset.n_vertices;
  if (u < 0 || v < 0 || u >= n || v >= n) throw new Error('endpoint out of range');
  if (u === v) throw new Error('self-loops are not allowed');
  if (poset.edges[u].includes(v)) throw new Error('edge already exists');
  if (reaches(poset.edges, v, u)) throw new Error('edge would create a cycle');
  const edges = poset.edges.map((r) => [...r]);
  edges[u].push(v);
  return { n_vertices: n, edges };
}

export function removeEdge(poset, u, v) {
  if (u < 0 || u >= poset.n_vertices) throw new Error('endpoint out of range');
  return {
    n_vertices: poset.n_vertices,
    edges: poset.edges.map((r, i) => (i === u ? r.filter((x) => x !== v) : [...r])),
  };
}
```

- [ ] **Step 3: Write the unit tests**

Create `nomadim/editor/test/edits.test.mjs`:

```js
import test from 'node:test';
import assert from 'node:assert';
import { reaches } from '../src/graph.mjs';
import { emptyPoset, addVertex, removeVertex, addEdge, removeEdge } from '../src/edits.mjs';

test('reaches finds transitive paths and respects direction', () => {
  const adj = [[1], [2], []]; // 0<1<2
  assert.strictEqual(reaches(adj, 0, 2), true);
  assert.strictEqual(reaches(adj, 2, 0), false);
  assert.strictEqual(reaches(adj, 0, 0), false);
});

test('addVertex appends an isolated vertex without mutating input', () => {
  const p = { n_vertices: 1, edges: [[]] };
  const q = addVertex(p);
  assert.deepStrictEqual(q, { n_vertices: 2, edges: [[], []] });
  assert.strictEqual(p.n_vertices, 1); // unchanged
});

test('addEdge adds a valid relation', () => {
  const p = addEdge({ n_vertices: 3, edges: [[], [], []] }, 0, 2);
  assert.deepStrictEqual(p.edges, [[2], [], []]);
});

test('addEdge rejects self-loops, duplicates, out-of-range, and cycles', () => {
  const base = { n_vertices: 3, edges: [[1], [2], []] }; // 0<1<2
  assert.throws(() => addEdge(base, 1, 1), /self-loop/);
  assert.throws(() => addEdge(base, 0, 1), /already exists/);
  assert.throws(() => addEdge(base, 0, 9), /out of range/);
  assert.throws(() => addEdge(base, 2, 0), /cycle/); // 0<...<2 already, so 2->0 cycles
});

test('removeEdge drops just that relation', () => {
  const p = removeEdge({ n_vertices: 3, edges: [[1, 2], [], []] }, 0, 1);
  assert.deepStrictEqual(p.edges, [[2], [], []]);
});

test('removeVertex renumbers higher vertices and drops incident edges', () => {
  // 0<1, 1<2, 0<2 ; remove vertex 1 -> remaining {0,1(old 2)} with edge 0<1
  const p = { n_vertices: 3, edges: [[1, 2], [2], []] };
  const q = removeVertex(p, 1);
  assert.strictEqual(q.n_vertices, 2);
  assert.deepStrictEqual(q.edges, [[1], []]); // old 0->2 becomes 0->1
});

test('emptyPoset is a zero-vertex poset', () => {
  assert.deepStrictEqual(emptyPoset(), { n_vertices: 0, edges: [] });
});
```

- [ ] **Step 4: Run the tests**

Run: `mise run nomadim-editor-test`
Expected: all previously-passing tests plus the new 7 — `# pass 20`, `# fail 0` (13 from 2b-i + 7 here).

- [ ] **Step 5: Commit**

```bash
git add nomadim/editor/src/graph.mjs nomadim/editor/src/edits.mjs nomadim/editor/test/edits.test.mjs
git commit -m "feat(nomadim): editor pure poset edit ops with cycle rejection"
```

---

### Task 2: Critical-pair overlay builder + realizer shaper

**Files:** Modify `nomadim/editor/src/cytoscape-elements.mjs`; create `nomadim/editor/src/realizer.mjs`, `nomadim/editor/test/overlay-realizer.test.mjs`.

- [ ] **Step 1: Add the critical-pair element builder**

Append to `nomadim/editor/src/cytoscape-elements.mjs`:

```js

// Overlay elements for critical pairs (incomparable pairs, drawn as a separate
// dashed class so they don't affect the Hasse layout). Ids are "c<x>_<y>".
export function criticalPairsToElements(pairs) {
  return pairs.map(([x, y]) => ({
    data: { id: `c${x}_${y}`, source: 'n' + x, target: 'n' + y },
    classes: 'critical',
  }));
}
```

- [ ] **Step 2: Write the realizer shaper**

Create `nomadim/editor/src/realizer.mjs`:

```js
// Pure shaping over the WASM realizer result. Returns { l1, l2 } (two linear
// extensions, arrays of vertex indices bottom-to-top) when the poset has order
// dimension <= 2, else null.
export function realizerColumns(client, adjacency) {
  const r = client.findRealizer(adjacency);
  return r.dim_le_2 ? { l1: r.l1, l2: r.l2 } : null;
}
```

- [ ] **Step 3: Write the unit tests**

Create `nomadim/editor/test/overlay-realizer.test.mjs`:

```js
import test from 'node:test';
import assert from 'node:assert';
import { createRequire } from 'node:module';
import { makeClient } from '../src/wasm-client.mjs';
import { criticalPairsToElements } from '../src/cytoscape-elements.mjs';
import { realizerColumns } from '../src/realizer.mjs';

const require = createRequire(import.meta.url);
const factory = require('../public/nomadim.js');

test('criticalPairsToElements builds dashed-class overlay edges', () => {
  const els = criticalPairsToElements([[0, 1], [2, 3]]);
  assert.strictEqual(els.length, 2);
  assert.deepStrictEqual(els[0], { data: { id: 'c0_1', source: 'n0', target: 'n1' }, classes: 'critical' });
  assert.strictEqual(els[1].classes, 'critical');
});

test('empty critical-pair list yields no overlay', () => {
  assert.deepStrictEqual(criticalPairsToElements([]), []);
});

test('realizerColumns returns two extensions for a dim-2 poset, null for S3', async () => {
  const c = await makeClient(factory);
  const cols = realizerColumns(c, [[1], [2], [3], []]); // chain
  assert.ok(cols && Array.isArray(cols.l1) && Array.isArray(cols.l2));
  assert.strictEqual(cols.l1.length, 4);
  assert.strictEqual(realizerColumns(c, [[4, 5], [3, 5], [3, 4], [], [], []]), null); // S3
});
```

- [ ] **Step 4: Run the tests**

Run: `mise run nomadim-editor-test`
Expected: `# pass 23`, `# fail 0` (20 + 3).

- [ ] **Step 5: Commit**

```bash
git add nomadim/editor/src/cytoscape-elements.mjs nomadim/editor/src/realizer.mjs nomadim/editor/test/overlay-realizer.test.mjs
git commit -m "feat(nomadim): editor critical-pair overlay builder + realizer shaper"
```

---

### Task 3: Poset-view critical overlay + selection styling

**Files:** Modify `nomadim/editor/src/poset-view.mjs`.

- [ ] **Step 1: Add the critical + selected styles and overlay functions**

Replace the entire contents of `nomadim/editor/src/poset-view.mjs` with:

```js
import { posetToElements, criticalPairsToElements } from './cytoscape-elements.mjs';

// Initialise a Cytoscape instance in `container` for poset rendering. Uses the
// dagre layered layout bottom-to-top so minimal elements sit at the bottom and
// cover edges point upward (the Hasse convention). Returns the cy instance.
export function initPosetView(container) {
  // cytoscape + cytoscape-dagre are loaded as globals by index.html script tags.
  const cy = window.cytoscape({
    container,
    elements: [],
    style: [
      { selector: 'node', style: {
        'background-color': '#4f8cff', 'label': 'data(label)',
        'color': '#fff', 'text-valign': 'center', 'text-halign': 'center',
        'width': 28, 'height': 28, 'font-size': 12,
      } },
      { selector: 'node:selected', style: {
        'background-color': '#ff7043', 'border-width': 3, 'border-color': '#b53',
      } },
      { selector: 'edge', style: {
        'width': 2, 'line-color': '#888', 'target-arrow-color': '#888',
        'target-arrow-shape': 'triangle', 'curve-style': 'bezier',
      } },
      { selector: 'edge:selected', style: { 'line-color': '#ff7043', 'width': 4 } },
      { selector: 'edge.critical', style: {
        'width': 2, 'line-color': '#e0457b', 'line-style': 'dashed',
        'target-arrow-shape': 'none', 'curve-style': 'unbundled-bezier',
        'control-point-distances': 40, 'opacity': 0.8,
      } },
    ],
  });
  return cy;
}

// Replace the rendered graph with the given poset and re-run the layout.
// (Critical overlay, if any, must be re-applied by the caller after this.)
export function renderPoset(cy, poset) {
  cy.elements().remove();
  cy.add(posetToElements(poset));
  cy.layout({ name: 'dagre', rankDir: 'BT', nodeSep: 30, rankSep: 50 }).run();
  cy.fit(undefined, 30);
}

// Add critical-pair overlay edges on top of the current layout (no relayout, so
// the Hasse positions are preserved). Clears any prior overlay first.
export function setCriticalOverlay(cy, pairs) {
  cy.remove('edge.critical');
  cy.add(criticalPairsToElements(pairs));
}

export function clearCriticalOverlay(cy) {
  cy.remove('edge.critical');
}
```

- [ ] **Step 2: Syntax-check**

Run: `node --check nomadim/editor/src/poset-view.mjs && echo OK`
Expected: `OK`. (DOM/`window` refs are inside functions; `--check` parses only.)

- [ ] **Step 3: Commit**

```bash
git add nomadim/editor/src/poset-view.mjs
git commit -m "feat(nomadim): editor critical overlay + selection styling in poset view"
```

---

### Task 4: File save (File System Access API + download fallback)

**Files:** Create `nomadim/editor/src/file-save.mjs`.

- [ ] **Step 1: Write the save module**

Create `nomadim/editor/src/file-save.mjs`:

```js
// Save `text` to a file. Uses the File System Access API when available
// (Chromium, secure context — localhost qualifies); otherwise falls back to a
// browser download. Returns 'saved' (picker) or 'downloaded' (fallback).
export async function saveText(text, suggestedName = 'poset.yaml') {
  if (typeof window !== 'undefined' && window.showSaveFilePicker) {
    const handle = await window.showSaveFilePicker({
      suggestedName,
      types: [{ description: 'YAML', accept: { 'text/yaml': ['.yaml', '.yml'] } }],
    });
    const writable = await handle.createWritable();
    await writable.write(text);
    await writable.close();
    return 'saved';
  }
  const blob = new Blob([text], { type: 'text/yaml' });
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  a.download = suggestedName;
  document.body.appendChild(a);
  a.click();
  a.remove();
  URL.revokeObjectURL(url);
  return 'downloaded';
}
```

- [ ] **Step 2: Syntax-check**

Run: `node --check nomadim/editor/src/file-save.mjs && echo OK`
Expected: `OK`. (This module is exercised by the Playwright download test in Task 6; the File System Access path is browser-only and feature-detected.)

- [ ] **Step 3: Commit**

```bash
git add nomadim/editor/src/file-save.mjs
git commit -m "feat(nomadim): editor file save via File System Access API + download fallback"
```

---

### Task 5: App rewrite — toolbar, critical toggle, realizer panel, save, polish

**Files:** Rewrite `nomadim/editor/src/app.mjs`; modify `nomadim/editor/index.html`, `nomadim/editor/styles.css`.

- [ ] **Step 1: Rewrite `app.mjs`**

Replace the entire contents of `nomadim/editor/src/app.mjs` with:

```js
import { makeClient } from './wasm-client.mjs';
import { emptyModel, hasPoset, posetAdjacency } from './model.mjs';
import { yamlToModel, modelToYaml } from './yaml-sync.mjs';
import { computeVerdict, verdictText } from './verdict.mjs';
import { initPosetView, renderPoset, setCriticalOverlay, clearCriticalOverlay } from './poset-view.mjs';
import { emptyPoset, addVertex, removeVertex, addEdge, removeEdge } from './edits.mjs';
import { realizerColumns } from './realizer.mjs';
import { saveText } from './file-save.mjs';

async function main() {
  const client = await makeClient(window.createNomadim);
  const cy = initPosetView(document.getElementById('cy'));
  let model = emptyModel();

  const els = {};
  for (const id of ['version', 'verdict', 'yaml', 'apply', 'file', 'error',
                    'new', 'addv', 'adde', 'del', 'edge-u', 'edge-v',
                    'critical', 'realizer', 'save']) {
    els[id] = document.getElementById(id);
  }
  els.version.textContent = 'libnomadim ' + client.version();

  const showError = (msg) => { els.error.textContent = msg || ''; };

  // Render the realizer panel (two linear extensions) for the current poset.
  function renderRealizer(adj) {
    const cols = realizerColumns(client, adj);
    if (!cols) { els.realizer.textContent = ''; return; }
    els.realizer.textContent = `realizer  L1: [${cols.l1.join(', ')}]   L2: [${cols.l2.join(', ')}]`;
  }

  // Render everything from the current model.
  function refresh({ syncYaml = true } = {}) {
    showError('');
    if (hasPoset(model)) {
      const adj = posetAdjacency(model);
      renderPoset(cy, model.poset);
      els.verdict.textContent = verdictText(computeVerdict(client, adj));
      renderRealizer(adj);
      if (els.critical.checked) setCriticalOverlay(cy, client.criticalPairs(adj));
    } else {
      cy.elements().remove();
      els.realizer.textContent = '';
      els.verdict.textContent = model.execution
        ? 'Execution loaded — apply the YAML panel to expand it; the swimlane editor is Phase 2b-iii.'
        : 'No document loaded.';
    }
    if (syncYaml) els.yaml.value = modelToYaml(client, model);
  }

  // Apply a pure poset edit (fn: poset -> poset) to the model, with error surfacing.
  function edit(fn) {
    if (!hasPoset(model)) { showError('Create or load a poset first (New poset).'); return; }
    try {
      model = { poset: fn(model.poset), execution: null };
      refresh();
    } catch (e) {
      showError(e && e.message ? e.message : String(e));
    }
  }

  function loadText(text) {
    try { model = yamlToModel(client, text); refresh(); }
    catch (e) { showError('Could not load document: ' + (e && e.message ? e.message : e)); }
  }

  // Delete currently-selected nodes (descending, so renumbering stays valid),
  // then any selected overlay-free edges.
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

  // --- wiring ---
  els.new.addEventListener('click', () => { model = { poset: emptyPoset(), execution: null }; refresh(); });
  els.addv.addEventListener('click', () => edit(addVertex));
  els.adde.addEventListener('click', () => {
    const u = parseInt(els['edge-u'].value, 10), v = parseInt(els['edge-v'].value, 10);
    if (Number.isNaN(u) || Number.isNaN(v)) { showError('Enter source and target vertex numbers.'); return; }
    edit((p) => addEdge(p, u, v));
  });
  els.del.addEventListener('click', deleteSelected);
  els.critical.addEventListener('change', () => {
    if (!hasPoset(model)) return;
    if (els.critical.checked) setCriticalOverlay(cy, client.criticalPairs(posetAdjacency(model)));
    else clearCriticalOverlay(cy);
  });
  els.save.addEventListener('click', async () => {
    try { await saveText(modelToYaml(client, model) || '', 'poset.yaml'); }
    catch (e) { if (e && e.name !== 'AbortError') showError('Save failed: ' + (e.message || e)); }
  });
  els.apply.addEventListener('click', () => {
    try { model = yamlToModel(client, els.yaml.value); refresh({ syncYaml: false }); }
    catch (e) { showError('Invalid YAML: ' + (e && e.message ? e.message : e)); }
  });
  els.file.addEventListener('change', async (ev) => {
    const f = ev.target.files[0];
    if (f) loadText(await f.text());
  });

  refresh();

  // Test hook: deterministic drivers for Playwright (bypass DOM selection).
  window.__editor = {
    loadText,
    newPoset: () => { model = { poset: emptyPoset(), execution: null }; refresh(); },
    addVertex: () => edit(addVertex),
    addEdge: (u, v) => edit((p) => addEdge(p, u, v)),
    removeVertex: (i) => edit((p) => removeVertex(p, i)),
    setCritical: (on) => { els.critical.checked = on; els.critical.dispatchEvent(new Event('change')); },
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

- [ ] **Step 2: Update `index.html`** — replace the `<header>` and `<main>` regions to add the toolbar, critical checkbox, realizer panel, and save button. Replace the whole file with:

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
  </header>
  <div id="toolbar">
    <button id="new">New poset</button>
    <button id="addv">Add vertex</button>
    <span class="sep"></span>
    <label>edge <input id="edge-u" type="number" min="0" class="vnum" /> →
      <input id="edge-v" type="number" min="0" class="vnum" /></label>
    <button id="adde">Add edge</button>
    <button id="del">Delete selected</button>
    <span class="sep"></span>
    <label><input id="critical" type="checkbox" /> critical pairs</label>
  </div>
  <div id="verdict">No document loaded.</div>
  <div id="realizer"></div>
  <div id="error"></div>
  <main>
    <div id="cy"></div>
    <div id="side">
      <textarea id="yaml" spellcheck="false" placeholder="poset / execution YAML"></textarea>
      <div class="controls"><button id="apply">Apply YAML</button></div>
    </div>
  </main>
  <script type="module" src="src/app.mjs"></script>
</body>
</html>
```

- [ ] **Step 3: Update `styles.css`** — append toolbar/realizer styling:

```css
#toolbar { padding: 6px 12px; display: flex; align-items: center; gap: 8px; flex-wrap: wrap; background: #f5f5f8; border-bottom: 1px solid #ddd; font-size: 13px; }
#toolbar .sep { width: 1px; align-self: stretch; background: #ccc; margin: 0 4px; }
#toolbar .vnum { width: 48px; }
#realizer { padding: 2px 12px; font-family: ui-monospace, monospace; font-size: 12px; color: #225; min-height: 16px; }
```

- [ ] **Step 4: Syntax-check the app**

Run: `node --check nomadim/editor/src/app.mjs && echo OK`
Expected: `OK`.

- [ ] **Step 5: Confirm unit tests still pass (no logic regressions in pure modules)**

Run: `mise run nomadim-editor-test`
Expected: `# pass 23`, `# fail 0` (the DOM rewrite doesn't touch the unit-tested modules; this confirms nothing broke).

- [ ] **Step 6: Commit**

```bash
git add nomadim/editor/src/app.mjs nomadim/editor/index.html nomadim/editor/styles.css
git commit -m "feat(nomadim): editor toolbar, critical toggle, realizer panel, save wiring"
```

---

### Task 6: Playwright editing/highlight/realizer/save suite

**Files:** Create `nomadim/editor/e2e/editing.spec.mjs`.

- [ ] **Step 1: Write the spec**

Create `nomadim/editor/e2e/editing.spec.mjs`:

```js
import { test, expect } from '@playwright/test';

async function boot(page) {
  await page.goto('/index.html');
  await page.waitForFunction(() => window.__editor !== undefined);
}

test('building a chain by editing yields dim-2 YES and a realizer', async ({ page }) => {
  await boot(page);
  await page.evaluate(() => window.__editor.newPoset());
  await page.evaluate(() => { window.__editor.addVertex(); window.__editor.addVertex();
                              window.__editor.addVertex(); window.__editor.addVertex(); });
  await expect.poll(() => page.evaluate(() => window.__editor.nodeCount())).toBe(4);
  await page.evaluate(() => { window.__editor.addEdge(0, 1); window.__editor.addEdge(1, 2);
                              window.__editor.addEdge(2, 3); });
  await expect(page.locator('#verdict')).toContainText('Dimension <= 2: YES');
  await expect(page.locator('#realizer')).toContainText('realizer');
});

test('an edge that would create a cycle is rejected with an error', async ({ page }) => {
  await boot(page);
  await page.evaluate(() => {
    window.__editor.newPoset();
    window.__editor.addVertex(); window.__editor.addVertex(); window.__editor.addVertex();
    window.__editor.addEdge(0, 1); window.__editor.addEdge(1, 2);
    window.__editor.addEdge(2, 0); // cycle
  });
  await expect(page.locator('#error')).toContainText('cycle');
  // the cycle edge was not added: 0<1, 1<2 only -> still dim-2
  await expect(page.locator('#verdict')).toContainText('Dimension <= 2: YES');
});

test('critical-pair toggle overlays edges on the S3 poset', async ({ page }) => {
  await boot(page);
  await page.evaluate(() => window.__editor.loadText(
    'poset:\n  n_vertices: 6\n  edges:\n    - [0, 4]\n    - [0, 5]\n    - [1, 3]\n    - [1, 5]\n    - [2, 3]\n    - [2, 4]\n'));
  await expect(page.locator('#verdict')).toContainText('Dimension <= 2: NO');
  await page.evaluate(() => window.__editor.setCritical(true));
  await expect.poll(() => page.evaluate(() => window.__editor.criticalCount())).toBeGreaterThan(0);
  await page.evaluate(() => window.__editor.setCritical(false));
  await expect.poll(() => page.evaluate(() => window.__editor.criticalCount())).toBe(0);
});

test('S3 shows no realizer text', async ({ page }) => {
  await boot(page);
  await page.evaluate(() => window.__editor.loadText(
    'poset:\n  n_vertices: 6\n  edges:\n    - [0, 4]\n    - [0, 5]\n    - [1, 3]\n    - [1, 5]\n    - [2, 3]\n    - [2, 4]\n'));
  await expect.poll(() => page.evaluate(() => window.__editor.realizerText())).toBe('');
});

test('Save downloads the current document as YAML', async ({ page }) => {
  await boot(page);
  await page.evaluate(() => { window.__editor.newPoset(); window.__editor.addVertex();
                              window.__editor.addVertex(); window.__editor.addEdge(0, 1); });
  const [download] = await Promise.all([
    page.waitForEvent('download'),
    page.click('#save'),
  ]);
  expect(download.suggestedFilename()).toBe('poset.yaml');
  const stream = await download.createReadStream();
  let text = '';
  for await (const chunk of stream) text += chunk;
  expect(text).toContain('poset:');
  expect(text).toContain('[0, 1]');
});
```

- [ ] **Step 2: Run the browser suite**

Run: `mise run nomadim-editor-e2e` (timeout 600000; Chromium already installed from 2b-i).
Expected: the original 4 smoke tests (from `app.spec.mjs`) PLUS these 5 = `9 passed`. If the cycle/critical/realizer/save assertions fail, investigate against the real behavior (do not weaken). In headless Chromium `window.showSaveFilePicker` is undefined, so Save hits the download fallback — the `waitForEvent('download')` path is correct.

- [ ] **Step 3: Commit**

```bash
git add nomadim/editor/e2e/editing.spec.mjs
git commit -m "test(nomadim): Playwright editing, critical-pair, realizer, and save suite"
```

---

### Task 7: README + INDEX + final verification

**Files:** Modify `nomadim/editor/README.md`, `docs/INDEX.md`.

- [ ] **Step 1: Update the README status + features**

In `nomadim/editor/README.md`, replace the `## Status` section with:

```markdown
## Status

- **Phase 2a (done):** the WASM core + a headless Node faithfulness test harness.
- **Phase 2b-i (done):** browser viewer — load a YAML poset/execution, see the
  layered Hasse diagram, the live dimension-≤-2 verdict, and an editable YAML panel.
- **Phase 2b-ii (done):** poset editing — add/remove vertices and edges (cycles
  rejected), critical-pair highlight toggle, the realizer panel (two linear
  extensions when dim ≤ 2), and Save (File System Access API + download fallback).
- **Phase 2b-iii (next):** the execution swimlane view and execution editing.
```

- [ ] **Step 2: Update INDEX**

In `docs/INDEX.md`, on the `wasm_bindings` row description, the editor reference already exists from 2b-i; extend it to note editing, e.g. append: ` (viewer + poset editing: add/remove vertices & edges, critical-pair highlight, realizer panel, save)`. Keep it on the same row; do not restructure.

- [ ] **Step 3: Final verification — all suites**

Run and confirm:
- `mise run nomadim-test` → `100% tests passed ... out of 77`.
- `mise run nomadim-editor-test` → `# pass 23`, `# fail 0`.
- `mise run nomadim-editor-e2e` → `9 passed`.

Also `git status --porcelain` must be clean (no stray untracked build dirs / node_modules — they are gitignored).

- [ ] **Step 4: Commit**

```bash
git add nomadim/editor/README.md docs/INDEX.md
git commit -m "docs(nomadim): document poset editing, highlight, realizer, save (phase 2b-ii)"
```

---

## Self-review notes (already reconciled)

- **Spec coverage:** §3 poset editing (add/remove vertex + add/remove edge with acyclicity — Task 1; toolbar wiring — Task 5), critical-pair highlight (Tasks 2,3,5), realizer panel (Tasks 2,5); §4 File System Access save with download fallback (Tasks 4,5). The two 2b-i review polish items are addressed in Task 5 (`main().catch`; the execution-only verdict message now points to 2b-iii). The execution **swimlane** is explicitly deferred to Phase 2b-iii.
- **Testability:** all edit logic (`graph`, `edits`), the overlay builder, and the realizer shaper are pure and Node-unit-tested; the DOM layer is covered by Playwright via deterministic `window.__editor` hooks plus a real download-event assertion for Save.
- **Type/name consistency:** `reaches`, `emptyPoset`/`addVertex`/`removeVertex`/`addEdge`/`removeEdge`, `criticalPairsToElements`, `realizerColumns`, `setCriticalOverlay`/`clearCriticalOverlay`, `saveText`, and the `window.__editor` hook names (`newPoset`, `addVertex`, `addEdge`, `removeVertex`, `setCritical`, `realizerText`, `currentYaml`, `nodeCount`, `criticalCount`, `verdictText`, `errorText`, `loadText`) are used identically across modules, the app, and the Playwright spec. The DOM ids in `index.html` (`new`, `addv`, `adde`, `del`, `edge-u`, `edge-v`, `critical`, `realizer`, `save`, plus existing `version`/`verdict`/`yaml`/`apply`/`file`/`error`/`cy`) match every `getElementById` in `app.mjs`.
- **Layout integrity:** critical-pair overlay edges are added AFTER the dagre layout (and given their own `critical` class with no arrow) so they never perturb the Hasse positions; `renderPoset` re-applies them via `refresh()` when the toggle is on.
- **No placeholders:** every code and command step is complete and runnable.
```
