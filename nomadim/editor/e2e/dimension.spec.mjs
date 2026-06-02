import { test, expect } from '@playwright/test';

const POSET_S3 = `poset:
  n_vertices: 6
  edges:
    - [0, 4]
    - [0, 5]
    - [1, 3]
    - [1, 5]
    - [2, 3]
    - [2, 4]
`;

test('shows dimension 3 and a 3-extension realizer for S_3', async ({ page }) => {
  await page.goto('/index.html');
  await page.waitForFunction(() => window.__editor !== undefined);
  await page.evaluate((yaml) => window.__editor.loadText(yaml), POSET_S3);
  await expect.poll(() => page.evaluate(() => window.__editor.dimensionText()))
    .toContain('Dimension: 3');
  const lines = await page.evaluate(() => window.__editor.realizerLineCount());
  expect(lines).toBe(3);
});

test('notes round-trip into saved YAML', async ({ page }) => {
  await page.goto('/index.html');
  await page.waitForFunction(() => window.__editor !== undefined);
  await page.evaluate(() => window.__editor.newPoset());
  await page.evaluate(() => window.__editor.setNotes('my note'));
  const yaml = await page.evaluate(() => window.__editor.currentYaml());
  expect(yaml).toContain('my note');
});
