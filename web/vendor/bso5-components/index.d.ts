/**
 * bso5-components — reusable headless data components built on bso5.
 *
 * - `Grid<Row>` — generic filterable/sortable/groupable data grid;
 * - `Tree` — generic collapsible tree with search;
 * - both take any `ReactiveSource` data and render headless markup with
 *   stable class names (bring your own CSS);
 * - the JSX runtime is re-exported under `bso5-components/jsx-runtime`,
 *   so tsconfig can point `jsxImportSource` at either package.
 *
 * Requires `bso5` as a peer dependency (any single copy — the components
 * share its `REACTIVE_VALUE` symbol and must not duplicate the runtime).
 *
 * РУС: bso5-components — переиспользуемые headless-компоненты данных на bso5.
 *
 * РУС: - `Grid<Row>` — генерик-грид данных с фильтром/сортировкой/группировкой;
 * РУС: - `Tree` — генерик-сворачиваемое дерево с поиском;
 * РУС: - оба принимают любые данные `ReactiveSource` и рендерят headless-разметку
 *   со стабильными именами классов (CSS — ваш);
 * РУС: - JSX-рантайм реэкспортирован под `bso5-components/jsx-runtime`,
 *   поэтому tsconfig может направить `jsxImportSource` в любой из пакетов.
 *
 * РУС: Требует `bso5` как peer dependency (ровно одну копию — компоненты
 * делят его символ `REACTIVE_VALUE` и не должны дублировать рантайм).
 *
 * @module
 */
export { Grid } from './Grid.js';
export type { GridProps, Column } from './Grid.js';
export { Tree } from './Tree.js';
export type { TreeProps, TreeData } from './Tree.js';
export { createElement, Fragment, jsx, jsxs, jsxDEV, } from './jsx-runtime.js';
export type { JsxNode, JsxChild, Component, DOMAttributes } from 'bso5';
//# sourceMappingURL=index.d.ts.map