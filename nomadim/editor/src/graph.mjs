// Pure graph reachability over an adjacency list (edges[u] lists v with u < v).
// reaches(adj, a, b): true iff there is a directed path a -> ... -> b of length >= 1.
export function reaches(adj, a, b) {
  const seen = new Array(adj.length).fill(false);
  const stack = [a];
  while (stack.length) {
    const x = stack.pop();
    for (const y of adj[x]) {
      if (y === b) return true;
      if (!seen[y]) { seen[y] = true; stack.push(y); }
    }
  }
  return false;
}
