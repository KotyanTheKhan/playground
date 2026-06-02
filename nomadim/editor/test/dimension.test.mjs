import test from 'node:test';
import assert from 'node:assert';
import { dimensionText, realizerLines, isMetaStale } from '../src/dimension.mjs';

test('dimensionText summarises a result', () => {
  assert.strictEqual(dimensionText({ dimension: 3, hyperedges: [[0, 1, 2]] }),
                     'Dimension: 3 (1 hyperedge)');
  assert.strictEqual(dimensionText({ dimension: 2, hyperedges: [[0, 1], [2, 3]] }),
                     'Dimension: 2 (2 hyperedges)');
  assert.strictEqual(dimensionText({ error: 'too large' }), 'Dimension: too large');
});

test('realizerLines formats extensions', () => {
  assert.deepStrictEqual(realizerLines([[0, 1, 2], [2, 1, 0]]),
                         ['L1: [0, 1, 2]', 'L2: [2, 1, 0]']);
});

test('isMetaStale compares source hashes', () => {
  assert.strictEqual(isMetaStale({ source_hash: 'abc' }, 'abc'), false);
  assert.strictEqual(isMetaStale({ source_hash: 'abc' }, 'xyz'), true);
  assert.strictEqual(isMetaStale(null, 'abc'), true);     // no meta -> stale
  assert.strictEqual(isMetaStale({}, 'abc'), true);       // no hash -> stale
});
