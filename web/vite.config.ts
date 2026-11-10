// WASM.4a: сборка интерфейса. Точки входа — app/src/app.tsx и app/src/roundtrip.ts;
// результат кладётся рядом с index.html (web/app/*.js) и копируется в wwwroot/app публикацией .NET.
// bso5 и bso5-components остаются внешними: браузер берёт их из web/vendor по карте импортов.
import { defineConfig } from 'vite'

const external = [
  'bso5',
  'bso5/jsx-runtime',
  'bso5-components',
  'bso5-components/jsx-runtime',
]

export default defineConfig({
  root: 'app',
  build: {
    // web/app/dist — каталог сборки (исходники — web/app/src); публикация .NET копирует web/app/** в wwwroot/app
    outDir: 'dist',
    emptyOutDir: true,
    target: 'es2022',
    sourcemap: false,
    rollupOptions: {
      // пути точек входа Vite разрешает от каталога запуска (web/), а не от root
      input: { app: 'app/src/app.tsx', roundtrip: 'app/src/roundtrip.ts' },
      external,
      output: {
        entryFileNames: '[name].js',
        chunkFileNames: 'chunks/[name]-[hash].js',
        format: 'es',
      },
    },
  },
})
