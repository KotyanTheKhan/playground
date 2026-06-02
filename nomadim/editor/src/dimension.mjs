// Pure shaping over the WASM dimension/realizer results — no WASM here.

export const DIMENSION_HINT = 'Dimension: press Compute';

export function dimensionText(result, opts = {}) {
  if (result && result.error) return `Dimension: ${result.error}`;
  const h = (result.hyperedges || []).length;
  const plural = h === 1 ? 'hyperedge' : 'hyperedges';
  const base = `Dimension: ${result.dimension} (${h} ${plural})`;
  return opts.stale ? `${base}  (stale — press Compute)` : base;
}

export function realizerLines(realizer) {
  return (realizer || []).map((ext, i) => `L${i + 1}: [${ext.join(', ')}]`);
}

// A cached meta block is stale unless its source_hash matches the current poset.
export function isMetaStale(meta, currentHash) {
  return !meta || !meta.source_hash || meta.source_hash !== currentHash;
}
