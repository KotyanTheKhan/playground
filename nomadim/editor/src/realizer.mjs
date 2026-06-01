// Pure shaping over the WASM realizer result. Returns { l1, l2 } (two linear
// extensions, arrays of vertex indices bottom-to-top) when the poset has order
// dimension <= 2, else null.
export function realizerColumns(client, adjacency) {
  const r = client.findRealizer(adjacency);
  return r.dim_le_2 ? { l1: r.l1, l2: r.l2 } : null;
}
