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
