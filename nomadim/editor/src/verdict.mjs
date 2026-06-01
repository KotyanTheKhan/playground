// Compute the dimension verdict for an adjacency list using the WASM client.
export function computeVerdict(client, adjacency) {
  const dim2 = client.isDim2(adjacency);
  const criticalCount = client.criticalPairs(adjacency).length;
  return { dim2, criticalCount };
}

// Human-readable one-liner for the verdict bar.
export function verdictText(verdict) {
  return `Dimension <= 2: ${verdict.dim2 ? 'YES' : 'NO'} (${verdict.criticalCount} critical pairs)`;
}
