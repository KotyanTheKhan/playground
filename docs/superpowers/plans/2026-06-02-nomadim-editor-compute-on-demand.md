# nomadim Editor Compute-On-Demand Dimension — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make the editor's heavy general-dimension panel run only when a **Compute dimension** button is pressed, keeping the last result visible but marked **(stale)** after the poset changes.

**Architecture:** An app-level `dim` cache in `app.mjs` keyed by `JSON.stringify(adjacency)`. The button fills it; `refresh()` renders from it and marks results stale when the current adjacency no longer matches the cached key. The dim-≤2 verdict + critical pairs keep auto-running. No C++/WASM changes.

**Tech Stack:** ES modules, `node:test`, Playwright. Editor under `nomadim/editor/`.

**Branch:** `feat/nomadim-editor-compute-on-demand` (already created).

---

## Conventions

- Editor unit tests (no browser): `cd nomadim/editor && mise exec node@22 -- node --test test/<file>.test.mjs`
- Editor e2e (browser): `cd nomadim/editor && mise exec node@22 -- npx playwright test e2e/<file>.spec.mjs`
  (The WASM module is already built at `nomadim/editor/public/nomadim.{js,wasm}`; these changes are JS-only so no rebuild is needed.)
- Commit messages: imperative; **no Co-Authored-By / AI watermark** (CLAUDE.md).

---

## Task 1: `dimension.mjs` — stale formatting + hint constant

**Files:**
- Modify: `nomadim/editor/src/dimension.mjs`
- Test: `nomadim/editor/test/dimension.test.mjs`

- [ ] **Step 1: Write the failing test**

Append to `nomadim/editor/test/dimension.test.mjs`:
```javascript
import { DIMENSION_HINT } from '../src/dimension.mjs';

test('dimensionText marks stale results', () => {
  assert.strictEqual(dimensionText({ dimension: 3, hyperedges: [[0, 1, 2]] }, { stale: true }),
                     'Dimension: 3 (1 hyperedge)  (stale — press Compute)');
  // not stale → no suffix
  assert.strictEqual(dimensionText({ dimension: 3, hyperedges: [[0, 1, 2]] }, { stale: false }),
                     'Dimension: 3 (1 hyperedge)');
  // error is never decorated as stale
  assert.strictEqual(dimensionText({ error: 'too large' }, { stale: true }),
                     'Dimension: too large');
});

test('DIMENSION_HINT is the pre-compute placeholder', () => {
  assert.strictEqual(DIMENSION_HINT, 'Dimension: press Compute');
});
```
(`dimensionText` and `assert`/`test` are already imported at the top of this file.)

- [ ] **Step 2: Run to verify it fails**

Run: `cd nomadim/editor && mise exec node@22 -- node --test test/dimension.test.mjs`
Expected: FAIL — `DIMENSION_HINT` is undefined and the `{ stale }` arg is ignored.

- [ ] **Step 3: Implement**

In `nomadim/editor/src/dimension.mjs`, add the constant and extend `dimensionText`:
```javascript
export const DIMENSION_HINT = 'Dimension: press Compute';

export function dimensionText(result, opts = {}) {
  if (result && result.error) return `Dimension: ${result.error}`;
  const h = (result.hyperedges || []).length;
  const plural = h === 1 ? 'hyperedge' : 'hyperedges';
  const base = `Dimension: ${result.dimension} (${h} ${plural})`;
  return opts.stale ? `${base}  (stale — press Compute)` : base;
}
```
(Replace the existing `dimensionText`. `realizerLines` and `isMetaStale` stay unchanged.)

- [ ] **Step 4: Run to verify it passes**

Run: `cd nomadim/editor && mise exec node@22 -- node --test test/dimension.test.mjs`
Expected: PASS (all dimension tests green).

- [ ] **Step 5: Commit**

```bash
git add nomadim/editor/src/dimension.mjs nomadim/editor/test/dimension.test.mjs
git commit -m "feat(nomadim): dimension panel stale label and pre-compute hint"
```

---

## Task 2: `app.mjs` — gate the panel behind a Compute button

**Files:**
- Modify: `nomadim/editor/index.html`
- Modify: `nomadim/editor/styles.css`
- Modify: `nomadim/editor/src/app.mjs`

No new automated test in this task (DOM wiring is covered by the e2e in Task 3). Verify manually via the build/serve at the end.

- [ ] **Step 1: Add the button to the toolbar**

In `nomadim/editor/index.html`, inside the `#poset-tools` group, after the
`critical pairs` label, add the button:
```html
      <label><input id="critical" type="checkbox" /> critical pairs</label>
      <button id="compute-dim">Compute dimension</button>
```

- [ ] **Step 2: Add the stale style**

Append to `nomadim/editor/styles.css`:
```css
.stale { opacity: 0.5; }
```

- [ ] **Step 3: Import the hint constant**

In `nomadim/editor/src/app.mjs`, extend the dimension import:
```javascript
import { dimensionText, realizerLines, DIMENSION_HINT } from './dimension.mjs';
```

- [ ] **Step 4: Register the button id**

In the `ids` array in `app.mjs`, add `'compute-dim'` (next to `'critical'`):
```javascript
               'new', 'addv', 'adde', 'del', 'edge-u', 'edge-v', 'critical', 'compute-dim', 'realizer',
```

- [ ] **Step 5: Replace `renderDimension` with cache + panel renderer + compute handler**

In `app.mjs`, replace the whole `renderDimension(adj)` function (currently:)
```javascript
  function renderDimension(adj) {
    const result = client.dimension(adj);
    els.dimension.textContent = dimensionText(result);
    if (result.error) { els.realizer.textContent = ''; els['realizers-all'].textContent = ''; return; }
    const one = client.findOneRealizer(adj);
    els.realizer.textContent = one.error ? '' : 'realizer  ' + realizerLines(one.realizer).join('   ');
    const all = client.allRealizers(adj);
    els['realizers-all'].textContent = all.error ? '' : `${all.colorings.length} minimum realizer(s)`;
  }
```
with:
```javascript
  // Heavy general-dimension analysis runs only on demand (Compute button). `dim`
  // caches the last result keyed by the adjacency it was computed for; a later
  // edit leaves it shown but marked stale until recomputed.
  let dim = null;   // { adjKey, result, one, all }

  function renderDimensionPanel() {
    const panel = [els.dimension, els.realizer, els['realizers-all']];
    if (!dim) {
      els.dimension.textContent = DIMENSION_HINT;
      els.realizer.textContent = '';
      els['realizers-all'].textContent = '';
      panel.forEach((e) => e.classList.remove('stale'));
      return;
    }
    const stale = JSON.stringify(posetAdjacency(model)) !== dim.adjKey;
    els.dimension.textContent = dimensionText(dim.result, { stale });
    const failed = dim.result.error || dim.one.error;
    els.realizer.textContent = failed ? '' : 'realizer  ' + realizerLines(dim.one.realizer).join('   ');
    els['realizers-all'].textContent = (dim.result.error || dim.all.error)
      ? '' : `${dim.all.colorings.length} minimum realizer(s)`;
    panel.forEach((e) => e.classList.toggle('stale', stale));
  }

  function computeDimension() {
    if (!hasPoset(model)) { showError('Create or load a poset first (New poset).'); return; }
    const adj = posetAdjacency(model);
    const result = client.dimension(adj);
    const one = result.error ? { error: result.error } : client.findOneRealizer(adj);
    const all = result.error ? { error: result.error } : client.allRealizers(adj);
    dim = { adjKey: JSON.stringify(adj), result, one, all };
    renderDimensionPanel();
  }
```

- [ ] **Step 6: Call the panel renderer from `refresh()` (instead of auto-computing)**

In `refresh()`'s poset branch, replace:
```javascript
      renderDimension(adj);
```
with:
```javascript
      renderDimensionPanel();
```

- [ ] **Step 7: Reset the cache on wholesale document replacement**

Add `dim = null;` as the first statement inside each of these handlers/functions in `app.mjs`:

In `loadText`:
```javascript
  function loadText(text) {
    dim = null;
    try {
```
In the `New poset` click handler (`els.new`):
```javascript
  els.new.addEventListener('click', () => { dim = null; model = { poset: emptyPoset(), execution: null }; setView('poset'); refresh(); });
```
In `derivePoset`:
```javascript
  function derivePoset() {
    dim = null;
    if (!model.execution) { showError('Load or build an execution first.'); return; }
```
In the `Apply YAML` click handler (`els.apply`):
```javascript
  els.apply.addEventListener('click', () => {
    dim = null;
    try {
```

- [ ] **Step 8: Wire the button + expose the test hook**

Add the click binding near the other listeners (e.g. right after the `els.critical` change listener, before `els.notes`):
```javascript
  els['compute-dim'].addEventListener('click', computeDimension);
```
And in the `window.__editor` object, add a hook (next to `dimensionText`):
```javascript
    computeDimension: () => computeDimension(),
```

- [ ] **Step 9: Build, serve, and manually verify**

Run: `mise run nomadim-editor` (background) and open the page. Confirm:
- On load (or New poset) the panel reads `Dimension: press Compute` and no realizer line.
- Pressing **Compute dimension** with the S₃ poset shows `Dimension: 3 (…)` and a 3-extension realizer line.
- Adding a vertex/edge afterward keeps the numbers but appends `(stale — press Compute)` and dims them.

- [ ] **Step 10: Commit**

```bash
git add nomadim/editor/index.html nomadim/editor/styles.css nomadim/editor/src/app.mjs
git commit -m "feat(nomadim): compute general dimension/realizers on demand with stale marking"
```

---

## Task 3: e2e coverage — compute gate + stale marker

**Files:**
- Modify: `nomadim/editor/e2e/dimension.spec.mjs`

- [ ] **Step 1: Update the S₃ test to require a button press, and add a stale test**

Replace the body of `nomadim/editor/e2e/dimension.spec.mjs` (keep the `POSET_S3`
constant and imports) so the dimension assertions press Compute first, and add a
stale-marker test:
```javascript
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

test('dimension is blank until Compute, then shows 3 and a 3-extension realizer', async ({ page }) => {
  await page.goto('/index.html');
  await page.waitForFunction(() => window.__editor !== undefined);
  await page.evaluate((yaml) => window.__editor.loadText(yaml), POSET_S3);
  // Before compute: hint, no realizer lines.
  await expect(page.locator('#dimension')).toHaveText('Dimension: press Compute');
  expect(await page.evaluate(() => window.__editor.realizerLineCount())).toBe(0);
  // After compute: dimension 3 and 3 linear extensions.
  await page.click('#compute-dim');
  await expect.poll(() => page.evaluate(() => window.__editor.dimensionText()))
    .toContain('Dimension: 3');
  expect(await page.evaluate(() => window.__editor.realizerLineCount())).toBe(3);
});

test('editing the poset after Compute marks the dimension stale', async ({ page }) => {
  await page.goto('/index.html');
  await page.waitForFunction(() => window.__editor !== undefined);
  await page.evaluate((yaml) => window.__editor.loadText(yaml), POSET_S3);
  await page.click('#compute-dim');
  await expect.poll(() => page.evaluate(() => window.__editor.dimensionText()))
    .toContain('Dimension: 3');
  await page.evaluate(() => window.__editor.addVertex());
  await expect.poll(() => page.evaluate(() => window.__editor.dimensionText()))
    .toContain('(stale');
});

test('notes round-trip into saved YAML', async ({ page }) => {
  await page.goto('/index.html');
  await page.waitForFunction(() => window.__editor !== undefined);
  await page.evaluate(() => window.__editor.newPoset());
  await page.evaluate(() => window.__editor.setNotes('my note'));
  const yaml = await page.evaluate(() => window.__editor.currentYaml());
  expect(yaml).toContain('my note');
});
```
(`window.__editor.addVertex()` and `newPoset()`/`setNotes()` are existing hooks.)

- [ ] **Step 2: Run the e2e spec**

Run: `cd nomadim/editor && mise exec node@22 -- npx playwright test e2e/dimension.spec.mjs`
Expected: 3 tests PASS.

- [ ] **Step 3: Regression — run the rest of the editor suites**

Run:
```bash
cd nomadim/editor && mise exec node@22 -- node --test test/*.test.mjs
mise exec node@22 -- npx playwright test e2e/app.spec.mjs
```
Expected: all editor unit tests PASS; the app verdict e2e still PASSES (verdict auto-runs, unaffected).

- [ ] **Step 4: Commit**

```bash
git add nomadim/editor/e2e/dimension.spec.mjs
git commit -m "test(nomadim): e2e for compute-on-demand dimension and stale marking"
```

---

## Self-review notes

- **Spec coverage:** gating (Task 2 button + `renderDimensionPanel`), keep-stale-on-edit (Task 2 `dim` survives `editPoset`/`deleteSelected`; staleness via adjacency compare), clear-on-replace (Task 2 Step 7 resets in load/new/apply/derive), verdict still auto-runs (untouched in `refresh`), hint constant + stale label (Task 1), styles (Task 2 Step 2), tests (Tasks 1 & 3). All covered.
- **Stale vs. clear distinction:** incremental edits (`editPoset`, `deleteSelected`) do NOT reset `dim`, so the panel renders stale; the four wholesale-replacement paths reset `dim = null` → hint.
- **No C++/WASM/CLI changes** — JS + HTML/CSS only.
