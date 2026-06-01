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
