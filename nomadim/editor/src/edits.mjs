import { reaches } from './graph.mjs';

// All operations return a NEW poset { n_vertices, edges } (adjacency form) and
// never mutate the input. They throw Error on invalid requests so the UI can
// surface a message.

export function emptyPoset() {
  return { n_vertices: 0, edges: [] };
}

export function addVertex(poset) {
  return {
    n_vertices: poset.n_vertices + 1,
    edges: [...poset.edges.map((r) => [...r]), []],
  };
}

// Remove vertex `idx`, dropping incident edges and renumbering higher vertices.
export function removeVertex(poset, idx) {
  const n = poset.n_vertices;
  if (idx < 0 || idx >= n) throw new Error('vertex out of range: ' + idx);
  const remap = (x) => (x > idx ? x - 1 : x);
  const edges = [];
  for (let u = 0; u < n; u++) {
    if (u === idx) continue;
    edges.push(poset.edges[u].filter((v) => v !== idx).map(remap));
  }
  return { n_vertices: n - 1, edges };
}

// Add edge u -> v (meaning u < v). Rejects self-loops, out-of-range endpoints,
// duplicates, and any edge that would create a cycle (v already reaches u).
export function addEdge(poset, u, v) {
  const n = poset.n_vertices;
  if (u < 0 || v < 0 || u >= n || v >= n) throw new Error('endpoint out of range');
  if (u === v) throw new Error('self-loops are not allowed');
  if (poset.edges[u].includes(v)) throw new Error('edge already exists');
  if (reaches(poset.edges, v, u)) throw new Error('edge would create a cycle');
  const edges = poset.edges.map((r) => [...r]);
  edges[u].push(v);
  return { n_vertices: n, edges };
}

export function removeEdge(poset, u, v) {
  if (u < 0 || u >= poset.n_vertices) throw new Error('endpoint out of range');
  return {
    n_vertices: poset.n_vertices,
    edges: poset.edges.map((r, i) => (i === u ? r.filter((x) => x !== v) : [...r])),
  };
}
