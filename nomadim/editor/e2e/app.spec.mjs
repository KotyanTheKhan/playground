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

const CHAIN = `poset:
  n_vertices: 4
  edges:
    - [0, 1]
    - [1, 2]
    - [2, 3]
`;

test('app boots, loads the WASM version, and starts empty', async ({ page }) => {
  await page.goto('/index.html');
  await expect(page.locator('#version')).toContainText('libnomadim');
  await expect(page.locator('#verdict')).toContainText('No document loaded');
  await page.waitForFunction(() => window.__editor !== undefined);
});

test('loading the S3 poset renders 6 nodes and reports NOT dim-2', async ({ page }) => {
  await page.goto('/index.html');
  await page.waitForFunction(() => window.__editor !== undefined);
  await page.evaluate((yaml) => window.__editor.loadText(yaml), POSET_S3);
  await expect.poll(() => page.evaluate(() => window.__editor.nodeCount())).toBe(6);
  await expect(page.locator('#verdict')).toContainText('Dimension <= 2: NO');
});

test('loading a chain renders 4 nodes and reports dim-2 YES', async ({ page }) => {
  await page.goto('/index.html');
  await page.waitForFunction(() => window.__editor !== undefined);
  await page.evaluate((yaml) => window.__editor.loadText(yaml), CHAIN);
  await expect.poll(() => page.evaluate(() => window.__editor.nodeCount())).toBe(4);
  await expect(page.locator('#verdict')).toContainText('Dimension <= 2: YES');
});

test('applying invalid YAML shows an error and does not crash', async ({ page }) => {
  await page.goto('/index.html');
  await page.waitForFunction(() => window.__editor !== undefined);
  await page.fill('#yaml', 'this is not a valid document');
  await page.click('#apply');
  await expect(page.locator('#error')).toContainText('Invalid YAML');
});
