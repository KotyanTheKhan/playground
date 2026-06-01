# nomadim editor — browser UI shell (Phase 2b-i) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A runnable browser viewer for nomadim documents: load a YAML poset/execution, render the poset as a layered Hasse diagram (Cytoscape + dagre), show the live dimension-≤-2 verdict, and edit the document through a synced YAML panel — all powered by the Phase-2a WASM module.

**Architecture:** A static, no-bundler page (`editor/index.html`) loads vendored Cytoscape/dagre UMD builds and the Emscripten module via classic `<script>` tags, then runs the app as ES modules. All poset semantics come from the WASM module through a thin `wasm-client` wrapper; the rest is small pure-logic modules (document model, Cytoscape element builder, verdict, YAML sync) each unit-tested under Node, plus a thin DOM layer in `app.mjs`. A Playwright smoke suite drives the served page in a real browser. A `mise run nomadim-editor` task builds the WASM, serves the directory, and opens the browser.

**Tech Stack:** Vanilla ES modules + Cytoscape.js 3.30.2 + cytoscape-dagre 2.5.0 (+ dagre 0.8.5), the Phase-2a Emscripten module, Node ≥ 22 (`node:test`), Playwright (`@playwright/test`), Python 3 `http.server`, mise tasks.

**Branch:** `nomadim-editor` (already checked out; Phases 1, 2a already on it).

**Spec:** `docs/superpowers/specs/2026-06-01-nomadim-poset-editor-design.md` §3 (Poset view, verdict bar, YAML panel) and §4 (file load). This plan is **Phase 2b-i** — the viewer shell. Deferred to **Phase 2b-ii**: interactive editing (drag-to-add edges + cycle-rejection UI, add/remove vertices), the execution swimlane view, critical-pair highlighting, the realizer panel, and File System Access API in-place save. 2b-i loads via a file picker and edits via the YAML panel only.

---

## Conventions used by every module

- **Adjacency JSON** is array-of-arrays in adjacency form: `edges[u]` lists `v` with `u < v`. This is exactly what the WASM `isDim2`/`findRealizer`/`criticalPairs` expect and what `parseDocument(...).poset.edges` returns.
- **Document JSON** (from `parseDocument`): `{ "execution"?: {n_procs, syncs:[[a,b]...]}, "poset"?: {n_vertices, edges:[[...]]} }`.
- ES module files use the `.mjs` extension. Node test files are `*.test.mjs` / `*.test.cjs` under `nomadim/editor/test/`.
- Build/run only via mise tasks. No AI watermark / `Co-Authored-By` in commits.

## File structure

| File | Responsibility |
|------|----------------|
| `nomadim/editor/vendor/` | Pinned Cytoscape/dagre/cytoscape-dagre UMD builds (committed) + `fetch.sh` + `README.md`. |
| `nomadim/editor/src/wasm-client.mjs` | `makeClient(factory)` → typed wrapper over the Embind module (JSON marshalling). |
| `nomadim/editor/src/model.mjs` | In-memory document model: load a parsed document, expose current poset adjacency. |
| `nomadim/editor/src/cytoscape-elements.mjs` | Pure `posetToElements(poset)` → Cytoscape element array. |
| `nomadim/editor/src/verdict.mjs` | Pure `computeVerdict(client, adjacency)` → `{dim2, criticalCount}`. |
| `nomadim/editor/src/yaml-sync.mjs` | `modelToYaml(client, model)` / `yamlToModel(client, text)`. |
| `nomadim/editor/src/poset-view.mjs` | DOM: init/refresh the Cytoscape instance in a container with the Hasse (dagre BT) layout. |
| `nomadim/editor/src/app.mjs` | DOM wiring: file load, render, verdict bar, YAML panel apply; exposes `window.__editor` for tests. |
| `nomadim/editor/index.html` | Page skeleton + script tags. |
| `nomadim/editor/styles.css` | Minimal layout styling. |
| `nomadim/editor/test/*.test.mjs` | Node unit tests for the pure-logic modules. |
| `nomadim/editor/e2e/app.spec.mjs` + `playwright.config.mjs` + `package.json` | Playwright browser smoke suite. |
| `mise.toml` | `nomadim-editor` (serve+open), `nomadim-editor-e2e`; fix `nomadim-editor-test` globbing. |
| `nomadim/.gitignore` | Ignore Playwright/npm install output. |

---

### Task 1: Vendor Cytoscape + dagre (committed, pinned)

**Files:** Create `nomadim/editor/vendor/fetch.sh`, `nomadim/editor/vendor/README.md`, and the three downloaded JS files.

- [ ] **Step 1: Write the fetch script**

Create `nomadim/editor/vendor/fetch.sh`:

```bash
#!/usr/bin/env bash
# Download the pinned browser (UMD) builds of the graph libraries into this dir.
# These files are committed so the editor works offline and reproducibly.
set -euo pipefail
cd "$(dirname "$0")"
curl -fsSL -o cytoscape.min.js       https://unpkg.com/cytoscape@3.30.2/dist/cytoscape.min.js
curl -fsSL -o dagre.min.js           https://unpkg.com/dagre@0.8.5/dist/dagre.min.js
curl -fsSL -o cytoscape-dagre.js     https://unpkg.com/cytoscape-dagre@2.5.0/cytoscape-dagre.js
echo "✅ vendored cytoscape 3.30.2, dagre 0.8.5, cytoscape-dagre 2.5.0"
```

Make it executable: `chmod +x nomadim/editor/vendor/fetch.sh`.

- [ ] **Step 2: Run it to fetch the libraries**

Run: `bash nomadim/editor/vendor/fetch.sh`
Expected: ends with `✅ vendored ...`; then `ls -l nomadim/editor/vendor/*.js` shows three non-empty files. Sanity-check they are JS, not error pages: `head -c 60 nomadim/editor/vendor/cytoscape.min.js` should look like minified JS (e.g. starts with `/*!` or `(function`).

- [ ] **Step 3: Write the vendor README**

Create `nomadim/editor/vendor/README.md`:

```markdown
# Vendored browser libraries (pinned, committed)

These UMD builds are committed so the editor runs offline and reproducibly:

- `cytoscape.min.js` — Cytoscape.js 3.30.2 (graph rendering)
- `dagre.min.js` — dagre 0.8.5 (layered layout engine)
- `cytoscape-dagre.js` — cytoscape-dagre 2.5.0 (Cytoscape ↔ dagre adapter)

Re-fetch / bump versions with `bash fetch.sh` (edit the pinned versions there).
```

- [ ] **Step 4: Commit (force-add the vendored JS, since `*.js` may be broadly ignored)**

```bash
git add -f nomadim/editor/vendor/cytoscape.min.js nomadim/editor/vendor/dagre.min.js nomadim/editor/vendor/cytoscape-dagre.js
git add nomadim/editor/vendor/fetch.sh nomadim/editor/vendor/README.md
git commit -m "build(nomadim): vendor pinned cytoscape + dagre browser builds for the editor"
```

Then confirm they are tracked: `git ls-files nomadim/editor/vendor` lists all five files.

---

### Task 2: WASM client wrapper + fix the test runner

**Files:** Create `nomadim/editor/src/wasm-client.mjs`, `nomadim/editor/test/wasm-client.test.mjs`; modify `mise.toml`; delete `nomadim/editor/test/package.json`.

- [ ] **Step 1: Write the client wrapper**

Create `nomadim/editor/src/wasm-client.mjs`:

```js
// Thin typed wrapper over the Embind module. `factory` is the MODULARIZE export
// (createNomadim): in the browser it's window.createNomadim, in Node it's
// require('../public/nomadim.js'). All marshalling of JSON lives here so the
// rest of the app works with plain JS objects/arrays.
export async function makeClient(factory) {
  const m = await factory();
  return {
    isDim2: (adjacency) => m.isDim2(JSON.stringify(adjacency)),
    findRealizer: (adjacency) => JSON.parse(m.findRealizer(JSON.stringify(adjacency))),
    criticalPairs: (adjacency) => JSON.parse(m.criticalPairs(JSON.stringify(adjacency))),
    expandExecution: (execution) => JSON.parse(m.expandExecution(JSON.stringify(execution))),
    parseDocument: (yamlText) => JSON.parse(m.parseDocument(yamlText)),
    dumpPoset: (poset) => m.dumpPoset(JSON.stringify(poset)),
    dumpExecution: (execution) => m.dumpExecution(JSON.stringify(execution)),
    version: () => m.version(),
  };
}
```

- [ ] **Step 2: Fix the mise test task to discover all test files**

In `mise.toml`, the `nomadim-editor-test` task currently ends with `node --test nomadim/editor/test/`, which (with the `package.json` `main`) only runs one file. Replace that last line so all `*.test.cjs` and `*.test.mjs` are discovered. The task's `run` block becomes:

```toml
[tasks.nomadim-editor-test]
description = "Build the WASM module + native CLI, run the Node faithfulness + unit tests"
tools = { emsdk = "4.0.23", node = "22" }
run = '''
#!/usr/bin/env bash
set -euo pipefail
# Native CLI is the faithfulness oracle.
cmake -S nomadim -B nomadim/build -DCMAKE_BUILD_TYPE=Release
cmake --build nomadim/build -j --target nomadim
# WASM module under test.
bash nomadim/editor/build-wasm.sh
# Headless cross-check + pure-logic unit tests.
node --test nomadim/editor/test/*.test.cjs nomadim/editor/test/*.test.mjs
'''
```

Then delete the now-unneeded resolver stub: `git rm nomadim/editor/test/package.json`.

- [ ] **Step 3: Write the client unit test**

Create `nomadim/editor/test/wasm-client.test.mjs`:

```js
import test from 'node:test';
import assert from 'node:assert';
import { createRequire } from 'node:module';
import { makeClient } from '../src/wasm-client.mjs';

const require = createRequire(import.meta.url);
const factory = require('../public/nomadim.js');

test('client marshals adjacency and document calls to/from the module', async () => {
  const c = await makeClient(factory);
  assert.match(c.version(), /\d+\.\d+\.\d+/);
  assert.strictEqual(c.isDim2([[1], [2], [3], []]), true);
  assert.strictEqual(c.isDim2([[4, 5], [3, 5], [3, 4], [], [], []]), false);

  const r = c.findRealizer([[1], [2], [3], []]);
  assert.strictEqual(r.dim_le_2, true);
  assert.ok(Array.isArray(r.l1) && Array.isArray(r.l2));

  assert.deepStrictEqual(c.criticalPairs([[1], [2], [3], []]), []);

  const doc = c.parseDocument('poset:\n  n_vertices: 3\n  edges:\n    - [0, 2]\n');
  assert.strictEqual(doc.poset.n_vertices, 3);
  assert.deepStrictEqual(doc.poset.edges, [[2], [], []]);

  const exec = c.parseDocument('execution:\n  n_procs: 2\n  syncs:\n    - [0, 1]\n');
  const expanded = c.expandExecution(exec.execution);
  assert.ok(expanded.n_vertices > 0 && Array.isArray(expanded.edges));
});
```

- [ ] **Step 4: Run the tests**

Run: `mise run nomadim-editor-test`
Expected: both the faithfulness suite (`faithfulness.test.cjs`, 5 tests) AND `wasm-client.test.mjs` run and pass — total `# pass 6`, `# fail 0`. (Confirms the glob fix discovers both files.)

- [ ] **Step 5: Commit**

```bash
git add nomadim/editor/src/wasm-client.mjs nomadim/editor/test/wasm-client.test.mjs mise.toml
git rm --cached nomadim/editor/test/package.json 2>/dev/null || true
git commit -m "feat(nomadim): editor WASM client wrapper; run all editor test files"
```

---

### Task 3: Document model + YAML sync

**Files:** Create `nomadim/editor/src/model.mjs`, `nomadim/editor/src/yaml-sync.mjs`, `nomadim/editor/test/model.test.mjs`.

- [ ] **Step 1: Write the model**

Create `nomadim/editor/src/model.mjs`:

```js
// In-memory document model. Holds at most one poset and/or one execution (as
// returned by the WASM parseDocument). For the 2b-i viewer the model is loaded
// from a document and queried; structural editing arrives in 2b-ii.

export function emptyModel() {
  return { poset: null, execution: null };
}

// doc: parseDocument output { execution?, poset? }
export function loadFromDocument(doc) {
  return { poset: doc.poset ?? null, execution: doc.execution ?? null };
}

// Adjacency (array-of-arrays) of the current poset, or null if none.
export function posetAdjacency(model) {
  return model.poset ? model.poset.edges : null;
}

// True if the model has something renderable as a poset.
export function hasPoset(model) {
  return model.poset != null;
}
```

- [ ] **Step 2: Write the YAML-sync module**

Create `nomadim/editor/src/yaml-sync.mjs`:

```js
import { loadFromDocument } from './model.mjs';

// Serialize the current model back to YAML text (poset takes precedence if both
// are present, matching what the viewer renders).
export function modelToYaml(client, model) {
  if (model.poset) return client.dumpPoset(model.poset);
  if (model.execution) return client.dumpExecution(model.execution);
  return '';
}

// Parse YAML text into a model. Throws (via the client) on malformed input;
// callers should catch and surface the error.
export function yamlToModel(client, text) {
  return loadFromDocument(client.parseDocument(text));
}
```

- [ ] **Step 3: Write the model/yaml-sync unit test**

Create `nomadim/editor/test/model.test.mjs`:

```js
import test from 'node:test';
import assert from 'node:assert';
import { createRequire } from 'node:module';
import { makeClient } from '../src/wasm-client.mjs';
import { loadFromDocument, posetAdjacency, hasPoset, emptyModel } from '../src/model.mjs';
import { modelToYaml, yamlToModel } from '../src/yaml-sync.mjs';

const require = createRequire(import.meta.url);
const factory = require('../public/nomadim.js');

test('model loads a poset document and exposes adjacency', () => {
  const m = loadFromDocument({ poset: { n_vertices: 3, edges: [[2], [], []] } });
  assert.strictEqual(hasPoset(m), true);
  assert.deepStrictEqual(posetAdjacency(m), [[2], [], []]);
});

test('empty model has no poset', () => {
  assert.strictEqual(hasPoset(emptyModel()), false);
  assert.strictEqual(posetAdjacency(emptyModel()), null);
});

test('yaml <-> model round-trips a poset through the client', async () => {
  const c = await makeClient(factory);
  const text = 'poset:\n  n_vertices: 3\n  edges:\n    - [0, 2]\n';
  const m = yamlToModel(c, text);
  assert.deepStrictEqual(posetAdjacency(m), [[2], [], []]);
  const back = yamlToModel(c, modelToYaml(c, m));
  assert.deepStrictEqual(back.poset, m.poset);
});

test('yamlToModel surfaces parse errors', async () => {
  const c = await makeClient(factory);
  assert.throws(() => yamlToModel(c, 'not a document'));
});
```

- [ ] **Step 4: Run the tests**

Run: `mise run nomadim-editor-test`
Expected: all pass — `# pass 10`, `# fail 0` (5 faithfulness + 1 client + 4 model).

- [ ] **Step 5: Commit**

```bash
git add nomadim/editor/src/model.mjs nomadim/editor/src/yaml-sync.mjs nomadim/editor/test/model.test.mjs
git commit -m "feat(nomadim): editor document model + YAML sync"
```

---

### Task 4: Cytoscape element builder + verdict (pure logic)

**Files:** Create `nomadim/editor/src/cytoscape-elements.mjs`, `nomadim/editor/src/verdict.mjs`, `nomadim/editor/test/elements-verdict.test.mjs`.

- [ ] **Step 1: Write the element builder**

Create `nomadim/editor/src/cytoscape-elements.mjs`:

```js
// Pure transform: poset {n_vertices, edges(adjacency)} -> Cytoscape element list.
// Node ids are "n<index>"; edge ids are "e<u>_<v>" for the relation u < v.
export function posetToElements(poset) {
  const elements = [];
  for (let i = 0; i < poset.n_vertices; i++) {
    elements.push({ data: { id: 'n' + i, label: String(i) } });
  }
  for (let u = 0; u < poset.edges.length; u++) {
    for (const v of poset.edges[u]) {
      elements.push({ data: { id: `e${u}_${v}`, source: 'n' + u, target: 'n' + v } });
    }
  }
  return elements;
}
```

- [ ] **Step 2: Write the verdict module**

Create `nomadim/editor/src/verdict.mjs`:

```js
// Compute the dimension verdict for an adjacency list using the WASM client.
export function computeVerdict(client, adjacency) {
  const dim2 = client.isDim2(adjacency);
  const criticalCount = client.criticalPairs(adjacency).length;
  return { dim2, criticalCount };
}

// Human-readable one-liner for the verdict bar.
export function verdictText(verdict) {
  return `Dimension <= 2: ${verdict.dim2 ? 'YES' : 'NO'} (${verdict.criticalCount} critical pairs)`;
}
```

- [ ] **Step 3: Write the unit test**

Create `nomadim/editor/test/elements-verdict.test.mjs`:

```js
import test from 'node:test';
import assert from 'node:assert';
import { createRequire } from 'node:module';
import { makeClient } from '../src/wasm-client.mjs';
import { posetToElements } from '../src/cytoscape-elements.mjs';
import { computeVerdict, verdictText } from '../src/verdict.mjs';

const require = createRequire(import.meta.url);
const factory = require('../public/nomadim.js');

test('posetToElements builds nodes and directed edges', () => {
  const els = posetToElements({ n_vertices: 3, edges: [[2], [], []] });
  const nodes = els.filter((e) => !e.data.source);
  const edges = els.filter((e) => e.data.source);
  assert.strictEqual(nodes.length, 3);
  assert.deepStrictEqual(nodes.map((n) => n.data.id), ['n0', 'n1', 'n2']);
  assert.strictEqual(edges.length, 1);
  assert.deepStrictEqual(edges[0].data, { id: 'e0_2', source: 'n0', target: 'n2' });
});

test('empty poset yields no elements', () => {
  assert.deepStrictEqual(posetToElements({ n_vertices: 0, edges: [] }), []);
});

test('verdict reflects the WASM dim-2 check and critical-pair count', async () => {
  const c = await makeClient(factory);
  const chain = computeVerdict(c, [[1], [2], [3], []]);
  assert.deepStrictEqual(chain, { dim2: true, criticalCount: 0 });
  assert.strictEqual(verdictText(chain), 'Dimension <= 2: YES (0 critical pairs)');

  const s3 = computeVerdict(c, [[4, 5], [3, 5], [3, 4], [], [], []]);
  assert.strictEqual(s3.dim2, false);
  assert.ok(s3.criticalCount > 0);
});
```

- [ ] **Step 4: Run the tests**

Run: `mise run nomadim-editor-test`
Expected: all pass — `# pass 13`, `# fail 0`.

- [ ] **Step 5: Commit**

```bash
git add nomadim/editor/src/cytoscape-elements.mjs nomadim/editor/src/verdict.mjs nomadim/editor/test/elements-verdict.test.mjs
git commit -m "feat(nomadim): editor Cytoscape element builder + dimension verdict"
```

---

### Task 5: Page shell, Cytoscape view, and app wiring (DOM)

**Files:** Create `nomadim/editor/src/poset-view.mjs`, `nomadim/editor/src/app.mjs`, `nomadim/editor/index.html`, `nomadim/editor/styles.css`.

- [ ] **Step 1: Write the Cytoscape view module**

Create `nomadim/editor/src/poset-view.mjs`:

```js
import { posetToElements } from './cytoscape-elements.mjs';

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
      { selector: 'edge', style: {
        'width': 2, 'line-color': '#888', 'target-arrow-color': '#888',
        'target-arrow-shape': 'triangle', 'curve-style': 'bezier',
      } },
    ],
  });
  return cy;
}

// Replace the rendered graph with the given poset and re-run the layout.
export function renderPoset(cy, poset) {
  cy.elements().remove();
  cy.add(posetToElements(poset));
  cy.layout({ name: 'dagre', rankDir: 'BT', nodeSep: 30, rankSep: 50 }).run();
  cy.fit(undefined, 30);
}
```

- [ ] **Step 2: Write the app wiring**

Create `nomadim/editor/src/app.mjs`:

```js
import { makeClient } from './wasm-client.mjs';
import { emptyModel, hasPoset, posetAdjacency } from './model.mjs';
import { yamlToModel, modelToYaml } from './yaml-sync.mjs';
import { computeVerdict, verdictText } from './verdict.mjs';
import { initPosetView, renderPoset } from './poset-view.mjs';

async function main() {
  const client = await makeClient(window.createNomadim);
  const cy = initPosetView(document.getElementById('cy'));
  let model = emptyModel();

  const els = {
    version: document.getElementById('version'),
    verdict: document.getElementById('verdict'),
    yaml: document.getElementById('yaml'),
    apply: document.getElementById('apply'),
    file: document.getElementById('file'),
    error: document.getElementById('error'),
  };
  els.version.textContent = 'libnomadim ' + client.version();

  function showError(msg) { els.error.textContent = msg || ''; }

  // Render the current model: graph + verdict bar + (re)fill the YAML panel.
  function refresh({ syncYaml = true } = {}) {
    showError('');
    if (hasPoset(model)) {
      const adj = posetAdjacency(model);
      renderPoset(cy, model.poset);
      els.verdict.textContent = verdictText(computeVerdict(client, adj));
    } else {
      cy.elements().remove();
      els.verdict.textContent = model.execution
        ? 'Execution loaded — switch to the YAML panel (poset view is 2b-i).'
        : 'No document loaded.';
    }
    if (syncYaml) els.yaml.value = modelToYaml(client, model);
  }

  function loadText(text) {
    try {
      model = yamlToModel(client, text);
      refresh();
    } catch (e) {
      showError('Could not load document: ' + (e && e.message ? e.message : e));
    }
  }

  els.apply.addEventListener('click', () => {
    try {
      model = yamlToModel(client, els.yaml.value);
      refresh({ syncYaml: false });
    } catch (e) {
      showError('Invalid YAML: ' + (e && e.message ? e.message : e));
    }
  });

  els.file.addEventListener('change', async (ev) => {
    const f = ev.target.files[0];
    if (f) loadText(await f.text());
  });

  refresh();

  // Test hook: lets Playwright drive loading and inspect state.
  window.__editor = {
    loadText,
    nodeCount: () => cy.nodes().length,
    verdictText: () => els.verdict.textContent,
  };
}

main();
```

- [ ] **Step 2b: Write the styles**

Create `nomadim/editor/styles.css`:

```css
* { box-sizing: border-box; }
body { margin: 0; font-family: system-ui, sans-serif; display: flex; flex-direction: column; height: 100vh; }
header { padding: 8px 12px; background: #1f2430; color: #fff; display: flex; align-items: center; gap: 16px; }
header h1 { font-size: 16px; margin: 0; }
#version { font-size: 12px; opacity: 0.8; }
#verdict { padding: 6px 12px; background: #eef; font-weight: 600; }
#error { padding: 0 12px; color: #b00; min-height: 18px; font-size: 13px; }
main { flex: 1; display: flex; min-height: 0; }
#cy { flex: 2; min-width: 0; background: #fff; }
#side { flex: 1; display: flex; flex-direction: column; border-left: 1px solid #ddd; min-width: 280px; }
#side textarea { flex: 1; width: 100%; border: 0; padding: 8px; font-family: ui-monospace, monospace; font-size: 13px; resize: none; }
#side .controls { padding: 8px; display: flex; gap: 8px; align-items: center; border-top: 1px solid #ddd; }
button { padding: 6px 12px; cursor: pointer; }
```

- [ ] **Step 3: Write the page**

Create `nomadim/editor/index.html`:

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
    <label>Load YAML <input id="file" type="file" accept=".yaml,.yml" /></label>
  </header>
  <div id="verdict">No document loaded.</div>
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

- [ ] **Step 4: Register cytoscape-dagre after load (verify the extension wires up)**

The `cytoscape-dagre` UMD auto-registers when loaded after `cytoscape` and `dagre` globals exist (it calls `cytoscape('layout', 'dagre', ...)` via the global). No code change needed, but confirm in Task 6 that the layout name `dagre` resolves (the smoke test in Task 7 will catch it if not). If the extension does NOT auto-register against the global, add this one line at the top of `initPosetView` before creating `cy`:

```js
if (window.cytoscapeDagre) window.cytoscape.use(window.cytoscapeDagre);
```

(Leave it out unless Task 6/7 shows the `dagre` layout is unregistered — cytoscape-dagre 2.5.0's UMD self-registers when `window.cytoscape` is present at load time.)

- [ ] **Step 5: Commit**

```bash
git add nomadim/editor/src/poset-view.mjs nomadim/editor/src/app.mjs nomadim/editor/index.html nomadim/editor/styles.css
git commit -m "feat(nomadim): editor page shell, Cytoscape Hasse view, and app wiring"
```

---

### Task 6: Serve task (`mise run nomadim-editor`)

**Files:** Modify `mise.toml`.

- [ ] **Step 1: Add the serve task**

Append to `mise.toml`:

```toml
[tasks.nomadim-editor]
description = "Build the WASM module, serve the editor, and open it in the browser"
tools = { emsdk = "4.0.23" }
run = '''
#!/usr/bin/env bash
set -euo pipefail
bash nomadim/editor/build-wasm.sh
PORT="${NOMADIM_EDITOR_PORT:-8731}"
URL="http://localhost:${PORT}/index.html"
# Open the browser once the server is up (macOS `open`, Linux `xdg-open`).
( sleep 1
  if command -v open >/dev/null 2>&1; then open "$URL"
  elif command -v xdg-open >/dev/null 2>&1; then xdg-open "$URL"
  else echo "Open $URL in your browser."; fi ) &
echo "Serving nomadim editor at ${URL} (Ctrl-C to stop)"
exec python3 -m http.server "$PORT" --directory nomadim/editor
'''
```

- [ ] **Step 2: Verify the server serves the page and the module (headless check, no browser needed)**

Run this one-liner (starts the server, curls key assets, stops it):
```bash
python3 -m http.server 8731 --directory nomadim/editor >/tmp/nmsrv.log 2>&1 &
SRV=$!; sleep 1
echo "index:";   curl -s -o /dev/null -w '%{http_code}\n' http://localhost:8731/index.html
echo "module:";  curl -s -o /dev/null -w '%{http_code}\n' http://localhost:8731/public/nomadim.js
echo "wasm:";    curl -s -o /dev/null -w '%{http_code}\n' http://localhost:8731/public/nomadim.wasm
echo "vendor:";  curl -s -o /dev/null -w '%{http_code}\n' http://localhost:8731/vendor/cytoscape.min.js
kill $SRV
```
Expected: four `200` lines. (Requires `nomadim/editor/public/nomadim.js` to exist — run `mise run nomadim-editor-build` first if needed.)

- [ ] **Step 3: Commit**

```bash
git add mise.toml
git commit -m "build(nomadim): mise run nomadim-editor serves and opens the editor"
```

---

### Task 7: Playwright browser smoke suite

**Files:** Create `nomadim/editor/package.json`, `nomadim/editor/playwright.config.mjs`, `nomadim/editor/e2e/app.spec.mjs`; modify `mise.toml` and `nomadim/.gitignore`.

- [ ] **Step 1: Ignore Playwright/npm install output**

Append to `nomadim/.gitignore`:

```
editor/package-lock.json
editor/test-results/
editor/playwright-report/
```

(`editor/node_modules/` is already ignored from Phase 2a.)

- [ ] **Step 2: Add the editor package manifest (Playwright dev dependency)**

Create `nomadim/editor/package.json`:

```json
{
  "name": "nomadim-editor",
  "private": true,
  "type": "module",
  "devDependencies": {
    "@playwright/test": "1.48.2"
  }
}
```

- [ ] **Step 3: Write the Playwright config (it starts the static server itself)**

Create `nomadim/editor/playwright.config.mjs`:

```js
import { defineConfig } from '@playwright/test';

const PORT = 8732;

export default defineConfig({
  testDir: './e2e',
  timeout: 30000,
  use: { baseURL: `http://localhost:${PORT}` },
  webServer: {
    command: `python3 -m http.server ${PORT} --directory .`,
    url: `http://localhost:${PORT}/index.html`,
    reuseExistingServer: true,
    timeout: 30000,
  },
});
```

- [ ] **Step 4: Write the smoke spec**

Create `nomadim/editor/e2e/app.spec.mjs`:

```js
import { test, expect } from '@playwright/test';

const POSET_S3 = `poset:
  n_vertices: 6
  edges:
    - [0, 4]
    - [0, 5]
    - [1, 3]
    - [1, 5]
    - [2, 3]
    - [2, 4]
`;

const CHAIN = `poset:
  n_vertices: 4
  edges:
    - [0, 1]
    - [1, 2]
    - [2, 3]
`;

test('app boots, loads the WASM version, and starts empty', async ({ page }) => {
  await page.goto('/index.html');
  await expect(page.locator('#version')).toContainText('libnomadim');
  await expect(page.locator('#verdict')).toContainText('No document loaded');
  await page.waitForFunction(() => window.__editor !== undefined);
});

test('loading the S3 poset renders 6 nodes and reports NOT dim-2', async ({ page }) => {
  await page.goto('/index.html');
  await page.waitForFunction(() => window.__editor !== undefined);
  await page.evaluate((yaml) => window.__editor.loadText(yaml), POSET_S3);
  await expect.poll(() => page.evaluate(() => window.__editor.nodeCount())).toBe(6);
  await expect(page.locator('#verdict')).toContainText('Dimension <= 2: NO');
});

test('loading a chain renders 4 nodes and reports dim-2 YES', async ({ page }) => {
  await page.goto('/index.html');
  await page.waitForFunction(() => window.__editor !== undefined);
  await page.evaluate((yaml) => window.__editor.loadText(yaml), CHAIN);
  await expect.poll(() => page.evaluate(() => window.__editor.nodeCount())).toBe(4);
  await expect(page.locator('#verdict')).toContainText('Dimension <= 2: YES');
});

test('applying invalid YAML shows an error and does not crash', async ({ page }) => {
  await page.goto('/index.html');
  await page.waitForFunction(() => window.__editor !== undefined);
  await page.fill('#yaml', 'this is not a valid document');
  await page.click('#apply');
  await expect(page.locator('#error')).toContainText('Invalid YAML');
});
```

- [ ] **Step 5: Add the e2e mise task**

Append to `mise.toml`:

```toml
[tasks.nomadim-editor-e2e]
description = "Build the WASM module and run the Playwright browser smoke suite"
tools = { emsdk = "4.0.23", node = "22" }
dir = "nomadim/editor"
run = '''
#!/usr/bin/env bash
set -euo pipefail
# Build the module the page loads (paths are relative to repo root, so cd back).
( cd ../.. && bash nomadim/editor/build-wasm.sh )
npm install --no-audit --no-fund
npx playwright install chromium
npx playwright test
'''
```

- [ ] **Step 6: Run the smoke suite**

Run: `mise run nomadim-editor-e2e` (use a generous timeout ≥ 600000; first run downloads Chromium ~150 MB and the Playwright npm package).
Expected: 4 passed. If `expect.poll(nodeCount)` never reaches the expected count, the `dagre` layout likely failed to register — apply the one-line `window.cytoscape.use(window.cytoscapeDagre)` fallback from Task 5 Step 4, rebuild nothing (it's JS), and re-run.

If Chromium cannot be downloaded (sandbox/no network), STOP and report BLOCKED with the error — do not delete or weaken the spec.

- [ ] **Step 7: Commit**

```bash
git add nomadim/editor/package.json nomadim/editor/playwright.config.mjs nomadim/editor/e2e/app.spec.mjs mise.toml nomadim/.gitignore
git commit -m "test(nomadim): Playwright browser smoke suite for the editor"
```

---

### Task 8: README + INDEX + final verification

**Files:** Modify `nomadim/editor/README.md`, `docs/INDEX.md`.

- [ ] **Step 1: Update the editor README**

In `nomadim/editor/README.md`, replace the `## Status` section and the `## Build & test (via mise)` section with:

```markdown
## Status

- **Phase 2a (done):** the WASM core + a headless Node faithfulness test harness.
- **Phase 2b-i (done):** browser viewer — load a YAML poset/execution, see the
  layered Hasse diagram (Cytoscape + dagre), the live dimension-≤-2 verdict, and
  an editable YAML panel. Node unit tests + a Playwright browser smoke suite.
- **Phase 2b-ii (next):** interactive editing (drag-to-add edges with cycle
  rejection, add/remove vertices), the execution swimlane view, critical-pair
  highlighting, the realizer panel, and File System Access API in-place save.

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
```

- [ ] **Step 2: Update the INDEX entry**

In `docs/INDEX.md`, update the `wasm_bindings` row's description (or add a sibling note) to mention the browser editor now exists. Find the `wasm_bindings` row and append to its description cell: `; consumed by the browser editor (\`nomadim/editor/\`, \`mise run nomadim-editor\`)`.

- [ ] **Step 3: Final verification — all suites**

Run each and confirm:
- `mise run nomadim-test` → `100% tests passed ... out of 77` (native unaffected).
- `mise run nomadim-editor-test` → `# pass 13`, `# fail 0` (faithfulness + unit).
- `mise run nomadim-editor-e2e` → 4 passed (browser smoke).

- [ ] **Step 4: Commit**

```bash
git add nomadim/editor/README.md docs/INDEX.md
git commit -m "docs(nomadim): document the browser editor viewer (phase 2b-i)"
```

---

## Self-review notes (already reconciled)

- **Spec coverage:** Implements §3's Poset view (layered Hasse via cytoscape-dagre BT), verdict bar (dim-≤-2 + critical-pair count), and the editable YAML panel synced through the WASM client; §4's file load (file picker — in-place FS Access save is explicitly 2b-ii). The execution swimlane, critical-pair highlight, and realizer panel are explicitly deferred to 2b-ii.
- **Testability:** every non-DOM module (`wasm-client`, `model`, `yaml-sync`, `cytoscape-elements`, `verdict`) has Node unit tests; the DOM layer is covered by the Playwright smoke suite driving the real page via the `window.__editor` hook.
- **Native build untouched:** no C++ changes; Task 8 re-runs `mise run nomadim-test` (77) to confirm.
- **Test-runner fix:** Task 2 replaces the `node --test <dir>` invocation (which only ran the `package.json` `main` file) with explicit `*.test.cjs`/`*.test.mjs` globs and removes the stub, so all editor test files are discovered.
- **Type/name consistency:** the client method names (`isDim2`, `findRealizer`, `criticalPairs`, `expandExecution`, `parseDocument`, `dumpPoset`, `dumpExecution`, `version`), `posetToElements`, `computeVerdict`/`verdictText`, `loadFromDocument`/`posetAdjacency`/`hasPoset`, `modelToYaml`/`yamlToModel`, `initPosetView`/`renderPoset`, and the `window.__editor` test hook are used identically across modules, tests, and the Playwright spec.
- **No placeholders:** every code and command step is complete; the one conditional (cytoscape-dagre registration fallback) is fully specified with the exact line and the condition under which to add it.
```
