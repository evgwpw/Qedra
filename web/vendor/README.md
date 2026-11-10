# Сторонние библиотеки интерфейса

Всё лежит локально; во время работы страница не ходит в сеть (CDN запрещён карточкой WASM.2).

## bso5

- Источник: https://github.com/evgwpw/BSO5 (MIT), ветка `main`.
- Коммит: **`9d46e83`** (обновление 2026-11-01: справочник GUIDE/API/TREE_GRID, рецепт «без сборщика»,
  `mount()`, `class` массивом и объектом, `$()` на вложенном прокси, `onDoubleClick` → `dblclick`).
- Сборка: `npm install --ignore-scripts` (политика блокирует запуск скриптов сторонних пакетов; для `tsc` их и не
  нужно) → `npm run build` → `packages/*/dist`; скопированы `*.js`, `*.d.ts`, `*.d.ts.map`, а также `README.md`
  и `LICENSE`.
- `bso5`: `index.js`, `reactive.js`, `dom.js`, `control.js`, `jsx-runtime.js` (версия **0.4.0**).
- `bso5-components`: `index.js`, `Grid.js`, `Tree.js`, `jsx-runtime.js` (версия **0.2.0**).
- **Типы (WASM.4a):** `*.d.ts` — из того же коммита; `web/tsconfig.json` направляет `paths` для `bso5`,
  `bso5/jsx-runtime`, `bso5-components`, `bso5-components/jsx-runtime` на эти файлы. Своих типов у приложения
  для библиотек нет.
- `bso5-components` импортирует `bso5` и `bso5/jsx-runtime` по голым именам — в приложении нужна карта импортов
  (`<script type="importmap">`) на `./vendor/bso5/index.js` и `./vendor/bso5/jsx-runtime.js`; сборка Vite
  оставляет их внешними (`rollupOptions.external`).
- Что задействовано в `web/app`: `mount`, `signal`, `computed`, `effect`, `$`, `For`, `Show`, компоненты `Grid`
  (каталог примеров: поиск, сортировка, группы по теме) и `Tree` (шаги решения: поиск, «развернуть/свернуть всё»).

## KaTeX

- Пакет: `katex` **0.16.11** (MIT), файлы — `katex.min.js`, `katex.min.css`, `fonts/` (60 файлов), `LICENSE`.
- Рендер формул: `katex.renderToString(latex, { throwOnError: false, displayMode: ... })`.

## MathLive

- Пакет: `mathlive` **0.111.4** (MIT), источник — npm (`npm pack mathlive@0.111.4`), файлы:
  `mathlive.min.mjs`, `fonts/` (20 шрифтов woff2), `sounds/` (5 wav), `LICENSE.txt`.
- Редактор формул: веб-компонент `<math-field>`; грузится **лениво** — только при первом открытии
  «Формулы» (`await import(new URL('../../vendor/mathlive/mathlive.min.mjs', import.meta.url))`), ~846 КБ.
- Формат обмена: `mf.setValue(latex, {format:'latex'})` → `mf.getValue('ascii-math')` → `web/app/src/mathjson.ts`.
  MathJSON в 0.111 не сериализуется без `@cortex-js/compute-engine` (26 МБ распакованных): `getValue('math-json')`
  отдаёт `""`, в 0.98.6 — `["Error","compute-engine-not-available"]`.

## Инструменты сборки интерфейса (WASM.4a, только devDependencies)

Точные версии — `web/package.json`, установка — `npm ci` по `package-lock.json`; в `web/dist` не попадают.

| пакет | версия | лицензия | зачем |
|---|---|---|---|
| `typescript` | 5.9.3 | Apache-2.0 | `npm run typecheck` (`strict`, `noUncheckedIndexedAccess`) |
| `vite` | 7.3.5 | MIT | `npm run build` — бандл `web/app/dist/*.js` |
| `vitest` | 5.0.5 | MIT | `npm run test` — 55 юнит-тестов чистых функций |
| `tsx` | 4.23.15 | MIT | запуск `web/tools/gen-functions.ts` (генератор каталога) |
| `@types/node` | 26.6.6 | MIT | типы Node для `tools/*.ts` и `vitest.config.ts` |
