import test from 'node:test';
import assert from 'node:assert';
import { emptyExecution, setNProcs, appendSync, removeLastSync } from '../src/execution-edits.mjs';

test('emptyExecution has the requested process count and no syncs', () => {
  assert.deepStrictEqual(emptyExecution(3), { n_procs: 3, syncs: [] });
  assert.deepStrictEqual(emptyExecution(), { n_procs: 2, syncs: [] });
});

test('appendSync adds a valid sync and rejects bad ones', () => {
  const e = appendSync({ n_procs: 3, syncs: [] }, 0, 2);
  assert.deepStrictEqual(e.syncs, [[0, 2]]);
  assert.throws(() => appendSync(e, 1, 1), /distinct/);
  assert.throws(() => appendSync(e, 0, 5), /out of range/);
});

test('removeLastSync drops the final sync only', () => {
  const e = removeLastSync({ n_procs: 2, syncs: [[0, 1], [1, 0]] });
  assert.deepStrictEqual(e.syncs, [[0, 1]]);
});

test('setNProcs drops syncs that fall out of range', () => {
  const e = setNProcs({ n_procs: 4, syncs: [[0, 1], [2, 3]] }, 2);
  assert.strictEqual(e.n_procs, 2);
  assert.deepStrictEqual(e.syncs, [[0, 1]]); // [2,3] dropped
});

test('ops do not mutate their input', () => {
  const e = { n_procs: 2, syncs: [[0, 1]] };
  appendSync(e, 1, 0);
  removeLastSync(e);
  setNProcs(e, 1);
  assert.deepStrictEqual(e, { n_procs: 2, syncs: [[0, 1]] });
});
