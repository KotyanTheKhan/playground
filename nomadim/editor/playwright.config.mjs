import { defineConfig } from '@playwright/test';

const PORT = 8732;

export default defineConfig({
  testDir: './e2e',
  timeout: 30000,
  use: { baseURL: `http://localhost:${PORT}` },
  webServer: {
    command: `python3 -m http.server ${PORT} --directory .`,
    url: `http://localhost:${PORT}/index.html`,
    reuseExistingServer: true,
    timeout: 30000,
  },
});
