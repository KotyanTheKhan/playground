import { makeClient } from './wasm-client.mjs';
import { emptyModel, hasPoset, posetAdjacency } from './model.mjs';
import { yamlToModel } from './yaml-sync.mjs';
import { computeVerdict, verdictText } from './verdict.mjs';
import { initPosetView, renderPoset, setCriticalOverlay, clearCriticalOverlay } from './poset-view.mjs';
import { emptyPoset, addVertex, removeVertex, addEdge, removeEdge } from './edits.mjs';
import { realizerColumns } from './realizer.mjs';
import { saveText } from './file-save.mjs';
import { emptyExecution, setNProcs, appendSync, removeLastSync, moveSync, removeSyncAt, reorderProcess } from './execution-edits.mjs';
import { renderExecution, clearExecution } from './execution-view.mjs';
import { attachDrag } from './execution-drag.mjs';

async function main() {
  const client = await makeClient(window.createNomadim);
  const cy = initPosetView(document.getElementById('cy'));
  let model = emptyModel();
  let view = 'poset'; // 'poset' | 'execution'

  const ids = ['version', 'verdict', 'yaml', 'apply', 'file', 'error',
               'new', 'addv', 'adde', 'del', 'edge-u', 'edge-v', 'critical', 'realizer', 'save',
               'tab-poset', 'tab-exec', 'poset-pane', 'exec-pane', 'exec',
               'nprocs', 'sync-a', 'sync-b', 'addsync', 'delsync', 'derive',
               'poset-tools', 'exec-tools'];
  const els = {};
  for (const id of ids) els[id] = document.getElementById(id);
  els.version.textContent = 'libnomadim ' + client.version();

  const showError = (msg) => { els.error.textContent = msg || ''; };

  function setView(v) {
    view = v;
    els['poset-pane'].style.display = v === 'poset' ? '' : 'none';
    els['exec-pane'].style.display = v === 'execution' ? '' : 'none';
    els['poset-tools'].style.display = v === 'poset' ? '' : 'none';
    els['exec-tools'].style.display = v === 'execution' ? '' : 'none';
    els['tab-poset'].classList.toggle('active', v === 'poset');
    els['tab-exec'].classList.toggle('active', v === 'execution');
    if (v === 'poset') cy.resize();
  }

  function renderRealizer(adj) {
    const cols = realizerColumns(client, adj);
    els.realizer.textContent = cols
      ? `realizer  L1: [${cols.l1.join(', ')}]   L2: [${cols.l2.join(', ')}]` : '';
  }

  // The model may hold a poset, an execution, or BOTH (after "Show derived
  // poset" keeps its source execution). The active `view` decides what is shown;
  // fall back to whatever the model actually has if the active pane is empty.
  function effectiveView() {
    if (view === 'execution' && model.execution) return 'execution';
    if (view === 'poset' && model.poset) return 'poset';
    if (model.poset) return 'poset';
    if (model.execution) return 'execution';
    return view;
  }

  // YAML for the document currently in view (so the panel matches what's shown).
  function currentYaml() {
    const v = effectiveView();
    if (v === 'execution' && model.execution) return client.dumpExecution(model.execution);
    if (model.poset) return client.dumpPoset(model.poset);
    if (model.execution) return client.dumpExecution(model.execution);
    return '';
  }

  function refresh({ syncYaml = true } = {}) {
    showError('');
    const v = effectiveView();
    setView(v);
    if (v === 'poset' && model.poset) {
      const adj = posetAdjacency(model);
      renderPoset(cy, model.poset);
      els.verdict.textContent = verdictText(computeVerdict(client, adj));
      renderRealizer(adj);
      if (els.critical.checked) setCriticalOverlay(cy, client.criticalPairs(adj));
    } else if (v === 'execution' && model.execution) {
      renderExecution(els.exec, model.execution);
      attachExecDrag();
      els.verdict.textContent = `Execution: ${model.execution.n_procs} processes, ${model.execution.syncs.length} syncs`;
      els.realizer.textContent = '';
    } else {
      cy.elements().remove();
      clearExecution(els.exec);
      els.verdict.textContent = 'No document loaded.';
      els.realizer.textContent = '';
    }
    if (syncYaml) els.yaml.value = currentYaml();
  }

  // Editing the poset keeps any source execution so you can switch back to it.
  function editPoset(fn) {
    if (!hasPoset(model)) { showError('Create or load a poset first (New poset).'); return; }
    try { model = { poset: fn(model.poset), execution: model.execution }; setView('poset'); refresh(); }
    catch (e) { showError(e && e.message ? e.message : String(e)); }
  }

  // Editing the execution invalidates any previously-derived poset, so drop it.
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

  // Expand the execution to its poset (via WASM) and show it, but KEEP the source
  // execution so the user can switch back to the Execution tab and keep editing.
  function derivePoset() {
    if (!model.execution) { showError('Load or build an execution first.'); return; }
    try {
      const poset = client.expandExecution(model.execution);
      model = { poset, execution: model.execution };
      setView('poset');
      refresh();
    } catch (e) { showError('Expand failed: ' + (e && e.message ? e.message : e)); }
  }

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

  els['tab-poset'].addEventListener('click', () => { setView('poset'); refresh(); });
  els['tab-exec'].addEventListener('click', () => { setView('execution'); refresh(); });

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

  els.save.addEventListener('click', async () => {
    const name = effectiveView() === 'execution' && model.execution ? 'execution.yaml' : 'poset.yaml';
    try { await saveText(currentYaml(), name); }
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
    currentYaml: () => currentYaml(),
    currentExecution: () => model.execution,
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
