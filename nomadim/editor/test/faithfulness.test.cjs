// Cross-checks the WASM module against the native nomadim CLI (the oracle) on the
// repo's data fixtures plus known cases. Run via `mise run nomadim-editor-test`,
// which builds both the CLI and the module first. Requires Node >= 22.
const test = require('node:test');
const assert = require('node:assert');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const { execFileSync } = require('node:child_process');
const createNomadim = require('../public/nomadim.js');

const ROOT = path.resolve(__dirname, '../../..');     // repo root
const DATA = path.join(ROOT, 'nomadim/data');
const CLI = path.join(ROOT, 'nomadim/build/nomadim');

function cliCheck(file) {
  if (!fs.existsSync(CLI)) throw new Error('native CLI not built: ' + CLI + ' (run `mise run nomadim-editor-test`)');
  // The CLI exits 0 for YES and 2 for NO; execFileSync throws on non-zero, so
  // capture stdout from the thrown error object when the exit code is non-zero.
  let out;
  try {
    out = execFileSync(CLI, ['check', file], { encoding: 'utf8' });
  } catch (err) {
    out = err.stdout || '';
  }
  if (/Dimension <= 2: YES/.test(out)) return true;
  if (/Dimension <= 2: NO/.test(out)) return false;
  throw new Error('unexpected CLI output: ' + out);
}

function adjacencyOf(Nm, text) {
  const doc = JSON.parse(Nm.parseDocument(text));
  if (doc.poset) return doc.poset.edges;
  if (doc.execution) return JSON.parse(Nm.expandExecution(JSON.stringify(doc.execution))).edges;
  throw new Error('document has neither poset nor execution');
}

// Strict reachability of an adjacency list (Warshall), as a Set of "a<b" keys.
function reachKeys(adj) {
  const n = adj.length;
  const lt = Array.from({ length: n }, () => new Array(n).fill(false));
  for (let u = 0; u < n; u++) for (const v of adj[u]) lt[u][v] = true;
  for (let k = 0; k < n; k++)
    for (let i = 0; i < n; i++)
      for (let j = 0; j < n; j++)
        if (lt[i][k] && lt[k][j]) lt[i][j] = true;
  const keys = new Set();
  for (let a = 0; a < n; a++) for (let b = 0; b < n; b++) if (a !== b && lt[a][b]) keys.add(a + '<' + b);
  return keys;
}

function isPermutation(arr, n) {
  if (arr.length !== n) return false;
  const seen = new Array(n).fill(false);
  for (const x of arr) { if (x < 0 || x >= n || seen[x]) return false; seen[x] = true; }
  return true;
}

test('wasm isDim2 matches native CLI on all data fixtures', async () => {
  const Nm = await createNomadim();
  const files = fs.readdirSync(DATA).filter((f) => f.endsWith('.yaml'));
  assert.ok(files.length >= 3, 'expected the data fixtures to be present');
  for (const f of files) {
    const file = path.join(DATA, f);
    const adj = adjacencyOf(Nm, fs.readFileSync(file, 'utf8'));
    assert.strictEqual(Nm.isDim2(JSON.stringify(adj)), cliCheck(file), `isDim2 mismatch on ${f}`);
  }
});

test('parseDocument/dump round-trips the poset and execution fixtures', async () => {
  const Nm = await createNomadim();
  const pdoc = JSON.parse(Nm.parseDocument(fs.readFileSync(path.join(DATA, 'poset_s3.yaml'), 'utf8')));
  const reposet = JSON.parse(Nm.parseDocument(Nm.dumpPoset(JSON.stringify(pdoc.poset))));
  assert.deepStrictEqual(reposet.poset, pdoc.poset);

  const edoc = JSON.parse(Nm.parseDocument(fs.readFileSync(path.join(DATA, 'exec_dim2.yaml'), 'utf8')));
  const reexec = JSON.parse(Nm.parseDocument(Nm.dumpExecution(JSON.stringify(edoc.execution))));
  assert.deepStrictEqual(reexec.execution, edoc.execution);
});

test('expandExecution matches native `nomadim convert`', async () => {
  const Nm = await createNomadim();
  const src = path.join(DATA, 'exec_dim2.yaml');
  const edoc = JSON.parse(Nm.parseDocument(fs.readFileSync(src, 'utf8')));
  const wasmPoset = JSON.parse(Nm.expandExecution(JSON.stringify(edoc.execution)));
  const tmp = path.join(os.tmpdir(), `nm_convert_${process.pid}_${Date.now()}.yaml`);
  try {
    execFileSync(CLI, ['convert', src, tmp]);
    const nativePoset = JSON.parse(Nm.parseDocument(fs.readFileSync(tmp, 'utf8'))).poset;
    assert.deepStrictEqual(wasmPoset, nativePoset);
  } finally {
    try { fs.rmSync(tmp); } catch (_) {}
  }
});

test('findRealizer: dim-2 yields a verified realizer; S3 yields none', async () => {
  const Nm = await createNomadim();

  const chain = '[[1],[2],[3],[]]';
  const r = JSON.parse(Nm.findRealizer(chain));
  assert.strictEqual(r.dim_le_2, true);
  const n = JSON.parse(chain).length;
  assert.ok(isPermutation(r.l1, n) && isPermutation(r.l2, n), 'l1/l2 must be permutations');
  const base = reachKeys(JSON.parse(chain));
  const pos1 = []; r.l1.forEach((e, i) => (pos1[e] = i));
  const pos2 = []; r.l2.forEach((e, i) => (pos2[e] = i));
  const inter = new Set();
  for (let a = 0; a < n; a++) for (let b = 0; b < n; b++)
    if (a !== b && pos1[a] < pos1[b] && pos2[a] < pos2[b]) inter.add(a + '<' + b);
  assert.deepStrictEqual([...inter].sort(), [...base].sort(), 'l1 ∩ l2 must equal the order');

  const s3 = JSON.parse(Nm.findRealizer('[[4,5],[3,5],[3,4],[],[],[]]'));
  assert.strictEqual(s3.dim_le_2, false);
  assert.deepStrictEqual(s3.l1, []);
  assert.deepStrictEqual(s3.l2, []);
});

test('criticalPairs agrees with isDim2 (empty critical set => dim2)', async () => {
  const Nm = await createNomadim();
  const chain = '[[1],[2],[3],[]]';
  assert.deepStrictEqual(JSON.parse(Nm.criticalPairs(chain)), []);
  assert.strictEqual(Nm.isDim2(chain), true);
});
