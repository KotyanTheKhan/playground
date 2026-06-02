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
