/**
 * bso5-components — JSX runtime entry points.
 *
 * The runtime itself lives in `bso5`; this module only re-exports it under the
 * `bso5-components` import source, so a project can compile its JSX against
 * either package without touching tsconfig `jsxImportSource`. The `jsx()`
 * wrapper here additionally folds the JSX `key` prop back into props for
 * component calls (identical to the bso5 runtime).
 *
 * РУС: bso5-components — точки входа JSX-рантайма.
 *
 * РУС: Сам рантайм живёт в `bso5`; этот модуль лишь реэкспортирует его под
 * import source `bso5-components`, чтобы проект мог компилировать свой JSX
 * против любого из пакетов, не трогая `jsxImportSource` в tsconfig. Обёртка
 * `jsx()` здесь дополнительно складывает JSX-проп `key` обратно в props для
 * вызовов компонентов (идентично рантайму bso5).
 *
 * @module
 */
export { jsx, jsxs, jsxDEV, Fragment, createElement } from 'bso5/jsx-runtime';
//# sourceMappingURL=jsx-runtime.js.map