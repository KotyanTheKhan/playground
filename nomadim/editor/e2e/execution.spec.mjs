import { test, expect } from '@playwright/test';

async function boot(page) {
  await page.goto('/index.html');
  await page.waitForFunction(() => window.__editor !== undefined);
}

const EXEC_DIM2 = `execution:
  n_procs: 2
  syncs:
    - [0, 1]
`;

test('loading an execution shows the execution view with lanes and a sync', async ({ page }) => {
  await boot(page);
  await page.evaluate((yaml) => window.__editor.loadText(yaml), EXEC_DIM2);
  await expect.poll(() => page.evaluate(() => window.__editor.currentView())).toBe('execution');
  await expect.poll(() => page.evaluate(() => window.__editor.laneCount())).toBe(2);
  await expect.poll(() => page.evaluate(() => window.__editor.syncCount())).toBe(1);
  await expect(page.locator('#verdict')).toContainText('2 processes, 1 syncs');
});

test('building an execution by editing updates the swimlane', async ({ page }) => {
  await boot(page);
  await page.evaluate(() => window.__editor.newExecution(3));
  await expect.poll(() => page.evaluate(() => window.__editor.laneCount())).toBe(3);
  await page.evaluate(() => { window.__editor.appendSync(0, 1); window.__editor.appendSync(1, 2); });
  await expect.poll(() => page.evaluate(() => window.__editor.syncCount())).toBe(2);
  await page.evaluate(() => window.__editor.removeLastSync());
  await expect.poll(() => page.evaluate(() => window.__editor.syncCount())).toBe(1);
});

test('an invalid sync is rejected with an error', async ({ page }) => {
  await boot(page);
  await page.evaluate(() => window.__editor.newExecution(2));
  await page.evaluate(() => window.__editor.appendSync(1, 1)); // same process
  await expect(page.locator('#error')).toContainText('distinct');
  await expect.poll(() => page.evaluate(() => window.__editor.syncCount())).toBe(0);
});

test('Show derived poset expands the execution and switches to the poset view', async ({ page }) => {
  await boot(page);
  await page.evaluate(() => { window.__editor.newExecution(2); window.__editor.appendSync(0, 1); });
  await page.evaluate(() => window.__editor.derivePoset());
  await expect.poll(() => page.evaluate(() => window.__editor.currentView())).toBe('poset');
  await expect.poll(() => page.evaluate(() => window.__editor.nodeCount())).toBeGreaterThan(0);
  // a single-sync 2-process execution expands to a dimension-2 poset
  await expect(page.locator('#verdict')).toContainText('Dimension <= 2: YES');
});
