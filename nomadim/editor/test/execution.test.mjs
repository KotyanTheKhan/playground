import test from 'node:test';
import assert from 'node:assert';
import { emptyExecution, setNProcs, appendSync, removeLastSync, moveSync, removeSyncAt, reorderProcess } from '../src/execution-edits.mjs';
import { executionSvg } from '../src/execution-svg.mjs';

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

test('executionSvg renders one lane per process and one connector per sync', () => {
  const svg = executionSvg({ n_procs: 3, syncs: [[0, 1], [1, 2]] });
  assert.match(svg, /^<svg /);
  assert.match(svg, /data-procs="3"/);
  assert.match(svg, /data-syncs="2"/);
  assert.strictEqual((svg.match(/class="lane"/g) || []).length, 3);
  assert.strictEqual((svg.match(/class="sync"/g) || []).length, 2);
  // each sync carries its endpoints
  assert.match(svg, /data-sync="0" data-a="0" data-b="1"/);
  assert.match(svg, /data-sync="1" data-a="1" data-b="2"/);
});

test('executionSvg handles an empty execution', () => {
  const svg = executionSvg({ n_procs: 0, syncs: [] });
  assert.match(svg, /data-procs="0"/);
  assert.strictEqual((svg.match(/class="lane"/g) || []).length, 0);
  assert.strictEqual((svg.match(/class="sync"/g) || []).length, 0);
});

test('moveSync reorders syncs and is no-op-safe / clamped', () => {
  const e = { n_procs: 2, syncs: [[0, 1], [1, 0]] };
  assert.deepStrictEqual(moveSync(e, 0, 1).syncs, [[1, 0], [0, 1]]);
  assert.deepStrictEqual(moveSync(e, 0, 0).syncs, [[0, 1], [1, 0]]); // no-op
  assert.deepStrictEqual(moveSync(e, 0, 9).syncs, [[1, 0], [0, 1]]); // clamp to last
});

test('moveSync throws on out-of-range source', () => {
  assert.throws(() => moveSync({ n_procs: 2, syncs: [[0, 1]] }, 3, 0), /out of range/);
});

test('removeSyncAt drops the indexed sync and validates range', () => {
  const e = { n_procs: 3, syncs: [[0, 1], [1, 2], [0, 2]] };
  assert.deepStrictEqual(removeSyncAt(e, 1).syncs, [[0, 1], [0, 2]]);
  assert.throws(() => removeSyncAt(e, 5), /out of range/);
});

test('reorderProcess moves a column and remaps sync endpoints', () => {
  const e = { n_procs: 3, syncs: [[0, 1], [1, 2]] };
  const r = reorderProcess(e, 0, 2); // 0->2 ; old1->0, old2->1, old0->2
  assert.strictEqual(r.n_procs, 3);
  assert.deepStrictEqual(r.syncs, [[2, 0], [0, 1]]);
  assert.throws(() => reorderProcess(e, 0, 9), /out of range/);
});

test('the new ops do not mutate their input', () => {
  const e = { n_procs: 3, syncs: [[0, 1], [1, 2]] };
  moveSync(e, 0, 1); removeSyncAt(e, 0); reorderProcess(e, 0, 2);
  assert.deepStrictEqual(e, { n_procs: 3, syncs: [[0, 1], [1, 2]] });
});
