// WASM.4a: юнит-тесты интерфейса — только чистые функции, без DOM и движка.
// Интерфейс (Vite) собирается из app/, проверки — npm run test.
import { defineConfig } from 'vitest/config'

export default defineConfig({
  test: {
    include: ['tests/**/*.test.ts'],
    environment: 'node',
  },
})
