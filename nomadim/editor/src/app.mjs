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
