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
