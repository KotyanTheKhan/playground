import { test, expect } from '@playwright/test';

async function boot(page) {
  await page.goto('/index.html');
  await page.waitForFunction(() => window.__editor !== undefined);
}

test('building a chain by editing yields dim-2 YES and a realizer', async ({ page }) => {
  await boot(page);
  await page.evaluate(() => window.__editor.newPoset());
  await page.evaluate(() => { window.__editor.addVertex(); window.__editor.addVertex();
                              window.__editor.addVertex(); window.__editor.addVertex(); });
  await expect.poll(() => page.evaluate(() => window.__editor.nodeCount())).toBe(4);
  await page.evaluate(() => { window.__editor.addEdge(0, 1); window.__editor.addEdge(1, 2);
                              window.__editor.addEdge(2, 3); });
  await expect(page.locator('#verdict')).toContainText('Dimension <= 2: YES');
  await expect(page.locator('#realizer')).toContainText('realizer');
});

test('an edge that would create a cycle is rejected with an error', async ({ page }) => {
  await boot(page);
  await page.evaluate(() => {
    window.__editor.newPoset();
    window.__editor.addVertex(); window.__editor.addVertex(); window.__editor.addVertex();
    window.__editor.addEdge(0, 1); window.__editor.addEdge(1, 2);
    window.__editor.addEdge(2, 0); // cycle
  });
  await expect(page.locator('#error')).toContainText('cycle');
  // the cycle edge was not added: 0<1, 1<2 only -> still dim-2
  await expect(page.locator('#verdict')).toContainText('Dimension <= 2: YES');
});

test('critical-pair toggle overlays edges on the S3 poset', async ({ page }) => {
  await boot(page);
  await page.evaluate(() => window.__editor.loadText(
    'poset:\n  n_vertices: 6\n  edges:\n    - [0, 4]\n    - [0, 5]\n    - [1, 3]\n    - [1, 5]\n    - [2, 3]\n    - [2, 4]\n'));
  await expect(page.locator('#verdict')).toContainText('Dimension <= 2: NO');
  await page.evaluate(() => window.__editor.setCritical(true));
  await expect.poll(() => page.evaluate(() => window.__editor.criticalCount())).toBeGreaterThan(0);
  await page.evaluate(() => window.__editor.setCritical(false));
  await expect.poll(() => page.evaluate(() => window.__editor.criticalCount())).toBe(0);
});

test('S3 shows no realizer text', async ({ page }) => {
  await boot(page);
  await page.evaluate(() => window.__editor.loadText(
    'poset:\n  n_vertices: 6\n  edges:\n    - [0, 4]\n    - [0, 5]\n    - [1, 3]\n    - [1, 5]\n    - [2, 3]\n    - [2, 4]\n'));
  await expect.poll(() => page.evaluate(() => window.__editor.realizerText())).toBe('');
});

test('Save downloads the current document as YAML', async ({ page }) => {
  await boot(page);
  await page.evaluate(() => { window.__editor.newPoset(); window.__editor.addVertex();
                              window.__editor.addVertex(); window.__editor.addEdge(0, 1); });
  // Headless Chromium exposes showSaveFilePicker on localhost but the picker
  // never resolves, so we remove it to let the <a download> fallback fire.
  await page.evaluate(() => { delete window.showSaveFilePicker; });
  const [download] = await Promise.all([
    page.waitForEvent('download'),
    page.click('#save'),
  ]);
  expect(download.suggestedFilename()).toBe('poset.yaml');
  const stream = await download.createReadStream();
  let text = '';
  for await (const chunk of stream) text += chunk;
  expect(text).toContain('poset:');
  expect(text).toContain('[0, 1]');
});
