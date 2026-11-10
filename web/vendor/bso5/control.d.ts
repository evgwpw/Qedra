/**
 * BSO5 — reactive control-flow components.
 *
 * JSX evaluates once at mount time, so lists and conditionals need components
 * that own their reactivity. `For` and `Show` render between invisible comment
 * anchors, adding no wrapper elements to the DOM.
 *
 * ```tsx
 * <For each={$(state.value, x => x.items)}>
 *   {(item, i) => <li>{i}: {item}</li>}
 * </For>
 *
 * <Show when={() => state.value.count > 10}>
 *   <p class="alert">Too much!</p>
 * </Show>
 * ```
 *
 * РУС: BSO5 — реактивные компоненты управляющего потока.
 *
 * РУС: JSX вычисляется один раз при монтировании, поэтому спискам и условиям
 * нужны компоненты, владеющие своей реактивностью. `For` и `Show` рендерят
 * между невидимыми комментариями-анкорами, не добавляя обёрток в DOM.
 *
 * @module
 */
import { Signal, type BoundValue } from './reactive.js';
import type { JsxChild } from './jsx-runtime.js';
/**
 * Anything a control-flow `each`/`when` prop can be driven by:
 * a plain value, `() => value` (re-read and auto-tracked inside the effect),
 * a `Signal`, or a `$()`-bound value.
 *
 * РУС: Всё, чем может управляться проп `each`/`when` управляющего потока:
 * обычное значение, `() => value` (перечитывается и автотрекается внутри
 * эффекта), `Signal` или привязанное значение `$()`.
 */
export type ReactiveSource<T> = T | (() => T) | Signal<T> | BoundValue<T>;
/** Reads the current value of a reactive source; auto-tracks inside `effect()`. (РУС: Читает текущее значение реактивного источника; автотрекается внутри `effect()`.) */
export declare function resolveSource<T>(src: ReactiveSource<T>): T;
/** Props of `{@link For}`. (РУС: Пропсы {@link For}.) */
export interface ForProps<T> {
    /**
     * The list to render: a plain array, `() => array` (re-read, auto-tracked),
     * a `Signal` or a `$()`-bound value. Use `$()`/`() =>` when the array can be
     * replaced wholesale.
     *
     * РУС: Список для рендера: обычный массив, `() => array` (перечитывается,
     * автотрекается), `Signal` или привязанное значение `$()`. Используйте
     * `$()`/`() =>`, когда массив может быть заменён целиком.
     */
    each: ReactiveSource<readonly T[]>;
    /**
     * Optional stable item key. When provided, keyed reconciliation kicks in:
     * DOM nodes are reused and moved instead of being recreated, preserving
     * focus, caret, selection, media state and CSS transitions across reorders.
     * The key identifies the element — while it stays in the list, the item's
     * nodes are NOT re-rendered (bind item fields with `$()` instead); the
     * rendered index is captured at first render; duplicate keys collapse into
     * one group of nodes.
     *
     * РУС: Необязательный стабильный ключ элемента. Если задан — включается
     * keyed-реконсиляция: DOM-узлы переиспользуются и перемещаются вместо
     * пересоздания, сохраняя фокус, каретку, выделение, состояние медиа и
     * CSS-transition'ы при пересортировках. Ключ идентифицирует элемент — пока
     * он в списке, узлы элемента НЕ перерисовываются (привязывайте поля через
     * `$()`); отрисованный индекс фиксируется при первом рендере; дубликаты
     * ключей схлопываются в одну группу узлов.
     */
    key?: (item: T, index: number) => unknown;
    /** Item renderer, called with `(item, index)`. (РУС: Рендерер элемента, вызывается как `(item, index)`.) */
    children: (item: T, index: number) => JsxChild;
}
/**
 * Reactive list rendering between comment anchors (no wrapper element).
 * Without `key` the whole list re-renders on change — item functions are
 * expected to be cheap and pure; use `$()` inside them for fine-grained
 * bindings. With `key`, existing nodes are reused and reordered instead.
 *
 * РУС: Реактивный рендер списка между комментариями-анкорами (без обёртки).
 * Без `key` при изменении перерисовывается весь список — функции элементов
 * должны быть дешёвыми и чистыми; для тонких привязок используйте `$()` внутри
 * них. С `key` существующие узлы переиспользуются и переставляются.
 */
export declare function For<T>(props: ForProps<T>): DocumentFragment;
/** Props of `{@link Show}`. (РУС: Пропсы {@link Show}.) */
export interface ShowProps {
    /**
     * Condition: a boolean, `() => boolean` (re-evaluated, auto-tracked),
     * a `Signal` or a `$()`-bound value.
     *
     * РУС: Условие: boolean, `() => boolean` (пере-вычисляется, автотрекается),
     * `Signal` или привязанное значение `$()`.
     */
    when: ReactiveSource<boolean>;
    /**
     * Content shown while `when` is falsy. Static JSX is rendered once and
     * re-inserted on every toggle; a `() => JsxChild` function re-evaluates
     * each time the block is shown. Optional.
     *
     * РУС: Контент, показываемый пока `when` ложно. Статический JSX рендерится
     * один раз и пере-вставляется при каждом переключении; функция
     * `() => JsxChild` перевычисляется при каждом показе блока. Необязателен.
     */
    fallback?: JsxChild | (() => JsxChild);
    /**
     * Content shown while `when` is truthy. Static JSX is rendered once and
     * re-inserted on every toggle; a `() => JsxChild` function re-evaluates
     * each time the block is shown.
     *
     * РУС: Контент, показываемый пока `when` истинно. Статический JSX рендерится
     * один раз и пере-вставляется при каждом переключении; функция
     * `() => JsxChild` перевычисляется при каждом показе блока.
     */
    children: JsxChild | (() => JsxChild);
}
/** Reactive conditional rendering between comment anchors (no wrapper). (РУС: Реактивный условный рендер между комментариями-анкорами (без обёртки).) */
export declare function Show(props: ShowProps): DocumentFragment;
//# sourceMappingURL=control.d.ts.map