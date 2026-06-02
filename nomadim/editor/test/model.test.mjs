import test from 'node:test';
import assert from 'node:assert';
import { createRequire } from 'node:module';
import { makeClient } from '../src/wasm-client.mjs';
import { loadFromDocument, posetAdjacency, hasPoset, emptyModel, getMeta, setNotes } from '../src/model.mjs';
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

test('model carries meta from a document and updates notes', () => {
  const m = loadFromDocument({ poset: { n_vertices: 2, edges: [[1], []] },
                              meta: { notes: 'hi', dimension: 1 } });
  assert.strictEqual(getMeta(m).notes, 'hi');
  const m2 = setNotes(m, 'bye');
  assert.strictEqual(getMeta(m2).notes, 'bye');
  assert.strictEqual(getMeta(m).notes, 'hi');   // immutable update
});
