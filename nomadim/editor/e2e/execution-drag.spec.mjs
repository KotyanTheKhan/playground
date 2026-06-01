import { test, expect } from '@playwright/test';

async function boot(page) {
  await page.goto('/index.html');
  await page.waitForFunction(() => window.__editor !== undefined);
}

// Center of a located element in page coordinates.
async function center(page, selector) {
  const box = await page.locator(selector).boundingBox();
  if (!box) throw new Error('no box for ' + selector);
  return { x: box.x + box.width / 2, y: box.y + box.height / 2 };
}

async function drag(page, from, to) {
  await page.mouse.move(from.x, from.y);
  await page.mouse.down();
  await page.mouse.move((from.x + to.x) / 2, (from.y + to.y) / 2, { steps: 4 });
  await page.mouse.move(to.x, to.y, { steps: 4 });
  await page.mouse.up();
}

test('dragging lane 0 to lane 1 creates a sync', async ({ page }) => {
  await boot(page);
  await page.evaluate(() => window.__editor.newExecution(3));
  await drag(page, await center(page, '.lane-hit[data-proc="0"]'),
                   await center(page, '.lane-hit[data-proc="1"]'));
  await expect.poll(() => page.evaluate(() => window.__editor.currentExecution().syncs)).toEqual([[0, 1]]);
});

test('dragging the first connector onto the second row reorders syncs', async ({ page }) => {
  await boot(page);
  await page.evaluate(() => {
    window.__editor.newExecution(3);
    window.__editor.appendSync(0, 1);
    window.__editor.appendSync(1, 2);
  });
  await drag(page, await center(page, '.sync[data-sync="0"]'),
                   await center(page, '.sync[data-sync="1"]'));
  await expect.poll(() => page.evaluate(() => window.__editor.currentExecution().syncs)).toEqual([[1, 2], [0, 1]]);
});

test('dragging a connector to the bottom deletes that sync', async ({ page }) => {
  await boot(page);
  await page.evaluate(() => {
    window.__editor.newExecution(3);
    window.__editor.appendSync(0, 1);
    window.__editor.appendSync(1, 2);
  });
  const svg = await page.locator('.exec-svg').boundingBox();
  const from = await center(page, '.sync[data-sync="0"]');
  await drag(page, from, { x: svg.x + svg.width / 2, y: svg.y + svg.height - 6 });
  await expect.poll(() => page.evaluate(() => window.__editor.currentExecution().syncs)).toEqual([[1, 2]]);
});

test('dragging a process header reorders processes and remaps syncs', async ({ page }) => {
  await boot(page);
  await page.evaluate(() => {
    window.__editor.newExecution(3);
    window.__editor.appendSync(0, 1);
    window.__editor.appendSync(1, 2);
  });
  await drag(page, await center(page, '.proc-label[data-proc="0"]'),
                   await center(page, '.lane-hit[data-proc="2"]'));
  await expect.poll(() => page.evaluate(() => window.__editor.currentExecution()))
    .toEqual({ n_procs: 3, syncs: [[2, 0], [0, 1]] });
});
