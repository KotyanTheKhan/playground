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
