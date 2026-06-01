// Pure transform: poset {n_vertices, edges(adjacency)} -> Cytoscape element list.
// Node ids are "n<index>"; edge ids are "e<u>_<v>" for the relation u < v.
export function posetToElements(poset) {
  const elements = [];
  for (let i = 0; i < poset.n_vertices; i++) {
    elements.push({ data: { id: 'n' + i, label: String(i) } });
  }
  for (let u = 0; u < poset.edges.length; u++) {
    for (const v of poset.edges[u]) {
      elements.push({ data: { id: `e${u}_${v}`, source: 'n' + u, target: 'n' + v } });
    }
  }
  return elements;
}

// Overlay elements for critical pairs (incomparable pairs, drawn as a separate
// dashed class so they don't affect the Hasse layout). Ids are "c<x>_<y>".
export function criticalPairsToElements(pairs) {
  return pairs.map(([x, y]) => ({
    data: { id: `c${x}_${y}`, source: 'n' + x, target: 'n' + y },
    classes: 'critical',
  }));
}
