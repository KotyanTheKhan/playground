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

test('dimension is blank until Compute, then shows 3 and a 3-extension realizer', async ({ page }) => {
  await page.goto('/index.html');
  await page.waitForFunction(() => window.__editor !== undefined);
  await page.evaluate((yaml) => window.__editor.loadText(yaml), POSET_S3);
  // Before compute: hint, no realizer lines.
  await expect(page.locator('#dimension')).toHaveText('Dimension: press Compute');
  expect(await page.evaluate(() => window.__editor.realizerLineCount())).toBe(0);
  // After compute: dimension 3 and 3 linear extensions.
  await page.click('#compute-dim');
  await expect.poll(() => page.evaluate(() => window.__editor.dimensionText()))
    .toContain('Dimension: 3');
  expect(await page.evaluate(() => window.__editor.realizerLineCount())).toBe(3);
});

test('editing the poset after Compute marks the dimension stale', async ({ page }) => {
  await page.goto('/index.html');
  await page.waitForFunction(() => window.__editor !== undefined);
  await page.evaluate((yaml) => window.__editor.loadText(yaml), POSET_S3);
  await page.click('#compute-dim');
  await expect.poll(() => page.evaluate(() => window.__editor.dimensionText()))
    .toContain('Dimension: 3');
  await page.evaluate(() => window.__editor.addVertex());
  await expect.poll(() => page.evaluate(() => window.__editor.dimensionText()))
    .toContain('(stale');
});

test('notes round-trip into saved YAML', async ({ page }) => {
  await page.goto('/index.html');
  await page.waitForFunction(() => window.__editor !== undefined);
  await page.evaluate(() => window.__editor.newPoset());
  await page.evaluate(() => window.__editor.setNotes('my note'));
  const yaml = await page.evaluate(() => window.__editor.currentYaml());
  expect(yaml).toContain('my note');
});
