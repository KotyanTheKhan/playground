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

test('client exposes general dimension, realizers, and document meta', async () => {
  const c = await makeClient(factory);
  // S_3: dimension 3.
  const s3 = [[4, 5], [3, 5], [3, 4], [], [], []];
  const dim = c.dimension(s3);
  assert.strictEqual(dim.dimension, 3);
  assert.ok(Array.isArray(dim.hyperedges));

  const one = c.findOneRealizer(s3);
  assert.strictEqual(one.dimension, 3);
  assert.strictEqual(one.realizer.length, 3);

  const all = c.allRealizers(s3);
  assert.ok(all.colorings.length >= 1);
  assert.strictEqual(all.colorings[0].realizer.length, 3);

  // Round-trip a document with meta through dumpDocument + parseDocument.
  const yaml = c.dumpDocument({ poset: { n_vertices: 3, edges: [[2], [2], []] },
                               meta: { notes: 'hi', dimension: 2 } });
  const parsed = c.parseDocument(yaml);
  assert.strictEqual(parsed.meta.notes, 'hi');
  assert.strictEqual(parsed.meta.dimension, 2);

  // Notes with quotes/newlines must survive the dump -> parse round trip
  // (parseDocument emits JSON by hand, so the note must be JSON-escaped).
  const tricky = 'a "quoted" note\nwith a newline\tand tab';
  const yaml2 = c.dumpDocument({ poset: { n_vertices: 2, edges: [[1], []] },
                                meta: { notes: tricky } });
  const parsed2 = c.parseDocument(yaml2);
  assert.strictEqual(parsed2.meta.notes, tricky);
});
