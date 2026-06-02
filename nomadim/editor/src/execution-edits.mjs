// Pure, immutable operations on an execution { n_procs, syncs:[[a,b],...] }.
// They return a NEW execution and throw Error on invalid requests.

export function emptyExecution(nProcs = 2) {
  return { n_procs: Math.max(0, nProcs | 0), syncs: [] };
}

// Set the process count. Drops any sync that references a now-out-of-range process.
export function setNProcs(exec, n) {
  const nProcs = Math.max(0, n | 0);
  return {
    n_procs: nProcs,
    syncs: exec.syncs.filter(([a, b]) => a < nProcs && b < nProcs).map(([a, b]) => [a, b]),
  };
}

// Append a synchronization between two distinct, in-range processes.
export function appendSync(exec, a, b) {
  if (a < 0 || b < 0 || a >= exec.n_procs || b >= exec.n_procs) throw new Error('process out of range');
  if (a === b) throw new Error('a sync needs two distinct processes');
  return { n_procs: exec.n_procs, syncs: [...exec.syncs.map(([x, y]) => [x, y]), [a, b]] };
}

export function removeLastSync(exec) {
  return { n_procs: exec.n_procs, syncs: exec.syncs.slice(0, -1).map(([x, y]) => [x, y]) };
}

// Move the sync at index `from` to index `to` (clamped to a valid slot).
export function moveSync(exec, from, to) {
  const len = exec.syncs.length;
  if (from < 0 || from >= len) throw new Error('sync index out of range');
  const t = Math.max(0, Math.min(len - 1, to));
  const syncs = exec.syncs.map(([a, b]) => [a, b]);
  const [moved] = syncs.splice(from, 1);
  syncs.splice(t, 0, moved);
  return { n_procs: exec.n_procs, syncs };
}

// Remove the sync at index `i`.
export function removeSyncAt(exec, i) {
  if (i < 0 || i >= exec.syncs.length) throw new Error('sync index out of range');
  return { n_procs: exec.n_procs, syncs: exec.syncs.filter((_, k) => k !== i).map(([a, b]) => [a, b]) };
}

// Move the process column at index `from` to index `to`, remapping every sync
// endpoint through the resulting index permutation. n_procs is unchanged.
export function reorderProcess(exec, from, to) {
  const n = exec.n_procs;
  if (from < 0 || from >= n || to < 0 || to >= n) throw new Error('process index out of range');
  const order = [];
  for (let i = 0; i < n; i++) order.push(i);
  order.splice(from, 1);
  order.splice(to, 0, from);
  const map = new Array(n);
  order.forEach((oldIdx, newIdx) => { map[oldIdx] = newIdx; });
  return { n_procs: n, syncs: exec.syncs.map(([a, b]) => [map[a], map[b]]) };
}
