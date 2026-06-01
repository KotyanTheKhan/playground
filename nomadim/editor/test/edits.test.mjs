import test from 'node:test';
import assert from 'node:assert';
import { reaches } from '../src/graph.mjs';
import { emptyPoset, addVertex, removeVertex, addEdge, removeEdge } from '../src/edits.mjs';

test('reaches finds transitive paths and respects direction', () => {
  const adj = [[1], [2], []]; // 0<1<2
  assert.strictEqual(reaches(adj, 0, 2), true);
  assert.strictEqual(reaches(adj, 2, 0), false);
  assert.strictEqual(reaches(adj, 0, 0), false);
});

test('addVertex appends an isolated vertex without mutating input', () => {
  const p = { n_vertices: 1, edges: [[]] };
  const q = addVertex(p);
  assert.deepStrictEqual(q, { n_vertices: 2, edges: [[], []] });
  assert.strictEqual(p.n_vertices, 1); // unchanged
});

test('addEdge adds a valid relation', () => {
  const p = addEdge({ n_vertices: 3, edges: [[], [], []] }, 0, 2);
  assert.deepStrictEqual(p.edges, [[2], [], []]);
});

test('addEdge rejects self-loops, duplicates, out-of-range, and cycles', () => {
  const base = { n_vertices: 3, edges: [[1], [2], []] }; // 0<1<2
  assert.throws(() => addEdge(base, 1, 1), /self-loop/);
  assert.throws(() => addEdge(base, 0, 1), /already exists/);
  assert.throws(() => addEdge(base, 0, 9), /out of range/);
  assert.throws(() => addEdge(base, 2, 0), /cycle/); // 0<...<2 already, so 2->0 cycles
});

test('removeEdge drops just that relation', () => {
  const p = removeEdge({ n_vertices: 3, edges: [[1, 2], [], []] }, 0, 1);
  assert.deepStrictEqual(p.edges, [[2], [], []]);
});

test('removeVertex renumbers higher vertices and drops incident edges', () => {
  // 0<1, 1<2, 0<2 ; remove vertex 1 -> remaining {0,1(old 2)} with edge 0<1
  const p = { n_vertices: 3, edges: [[1, 2], [2], []] };
  const q = removeVertex(p, 1);
  assert.strictEqual(q.n_vertices, 2);
  assert.deepStrictEqual(q.edges, [[1], []]); // old 0->2 becomes 0->1
});

test('emptyPoset is a zero-vertex poset', () => {
  assert.deepStrictEqual(emptyPoset(), { n_vertices: 0, edges: [] });
});
