/**
 * BSO5 — Reactive DOM without the bloat. Just TypeScript.
 *
 * A tiny (~4.7 kB min+gzip) reactive DOM library with first-class JSX support
 * and zero dependencies:
 *
 * - `Signal` / `signal` / `effect` — atomic reactive primitives;
 * - `batch` / `untrack` — one effect run per write group / read without tracking;
 * - `Reactive` — deep reactive proxy for plain objects and classes;
 * - `watch` — subscribe to a Signal or a reactive property path;
 * - `$` — bind reactive values directly into JSX children/attributes;
 * - `For` / `Show` — reactive list and conditional JSX components;
 * - `h` — universal element factory with full HTML tag typing;
 * - `mount` — mount a view and get a `{ node, dispose }` handle;
 * - `createScope` / `dispose` / `runInScope` / `onScopeDispose` — effect ownership;
 * - `releaseBindings` — stop reactive DOM bindings of a detached subtree;
 * - JSX runtime — use plain TSX with the TypeScript automatic transform.
 *
 * РУС: BSO5 — реактивный DOM без лишнего веса. Просто TypeScript.
 *
 * РУС: Крошечная (~4.7 kB min+gzip) реактивная DOM-библиотека с первоклассной
 * поддержкой JSX и нулём зависимостей:
 *
 * РУС: - `Signal` / `signal` / `effect` — атомарные реактивные примитивы;
 * РУС: - `batch` / `untrack` — один прогон эффектов на группу записей / чтение без трекинга;
 * РУС: - `Reactive` — глубокий реактивный прокси для объектов и классов;
 * РУС: - `watch` — подписка на Signal или реактивный путь свойства;
 * РУС: - `$` — привязка реактивных значений прямо в детей/атрибуты JSX;
 * РУС: - `For` / `Show` — реактивные JSX-компоненты списка и условия;
 * РУС: - `h` — универсальная фабрика элементов с типизацией всех HTML-тегов;
 * РУС: - `mount` — монтирует вью и возвращает ручку `{ node, dispose }`;
 * РУС: - `createScope` / `dispose` / `runInScope` / `onScopeDispose` — владение эффектами;
 * РУС: - `releaseBindings` — остановка реактивных DOM-привязок отсоединённого поддерева;
 * РУС: - JSX-рантайм — пишите обычный TSX с автоматическим трансформом TypeScript.
 *
 * @module
 */
export { Signal, signal, effect, computed, batch, untrack, setEffectErrorHandler, Reactive, getPropertyName, isBoundValue, watch, $, REACTIVE_VALUE, createScope, dispose, runInScope, onScopeDispose, getCurrentScope, } from './reactive.js';
export { h, hEl, flattenChildren, boundTextNode, appendChildren, releaseBindings, mount, parseEventProp, applyAttr, classToString, } from './dom.js';
export { For, Show, resolveSource } from './control.js';
export { createElement, Fragment, jsx, jsxs, jsxDEV, } from './jsx-runtime.js';
//# sourceMappingURL=index.js.map