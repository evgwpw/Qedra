/**
 * BSO5 — automatic JSX runtime (TypeScript `react-jsx` mode).
 *
 * Set `"jsx": "react-jsx"` and `"jsxImportSource": "bso5"` (or a relative
 * source path) in tsconfig, then write plain JSX — no framework needed.
 *
 * ```tsx
 * import { Reactive, $ } from 'bso5';
 * const state = new Reactive({ count: 0 });
 * const ui = <button onClick={() => state.value.count++}>
 *   Count: {$(state.value, x => x.count)}
 * </button>;
 * ```
 *
 * РУС: BSO5 — автоматический JSX-рантайм (режим TypeScript `react-jsx`).
 *
 * РУС: Установите `"jsx": "react-jsx"` и `"jsxImportSource": "bso5"` (или
 * относительный путь к исходникам) в tsconfig и пишите обычный JSX — фреймворк
 * не нужен.
 *
 * @module
 */
import type { BoundValue } from './reactive.js';
import { type ClassValue } from './dom.js';
/** Anything JSX can render as a child. (РУС: Всё, что JSX может отрендерить как ребёнка.) */
export type JsxChild = string | number | boolean | null | undefined | Node | BoundValue<any> | JsxChild[];
/** Common attributes accepted by intrinsic elements. (РУС: Общие атрибуты, принимаемые интринсик-элементами.) */
export interface DOMAttributes {
    class?: AttrValue<ClassValue>;
    className?: AttrValue<ClassValue>;
    id?: string;
    title?: AttrValue<string>;
    style?: Partial<CSSStyleDeclaration> | string;
    dataset?: Record<string, string | number | boolean>;
    /** Receives the created element (no `ref` object needed). (РУС: Получает созданный элемент (объект `ref` не нужен).) */
    ref?: (el: HTMLElement) => void;
    hidden?: boolean;
    type?: string;
    value?: AttrValue<unknown>;
    checked?: AttrValue<boolean>;
    disabled?: AttrValue<boolean>;
    placeholder?: AttrValue<string>;
    href?: AttrValue<string>;
    src?: AttrValue<string>;
    alt?: string;
    for?: string;
    [key: `on${string}`]: ((event: Event) => void) | undefined;
    children?: JsxChild | JsxChild[];
}
/** An attribute value: either a plain `T` or a reactive bound value of `T`. (РУС: Значение атрибута: либо обычный `T`, либо реактивное привязанное значение `T`.) */
export type AttrValue<T> = T | BoundValue<T>;
/** A JSX component: a plain function from props to a DOM node. (РУС: JSX-компонент: обычная функция от пропсов к DOM-узлу.) */
export type Component<P = {}> = (props: P & {
    children?: JsxChild | JsxChild[];
}) => Node;
/** The node type produced by JSX expressions. (РУС: Тип узла, порождаемый JSX-выражениями.) */
export type JsxNode = Node;
export declare namespace JSX {
    /** Every standard HTML tag, accepting `DOMAttributes` (plus any extra
     *  attributes, passed through to the DOM).
     *  РУС: Каждый стандартный HTML-тег, принимающий `DOMAttributes` (плюс любые
     *  дополнительные атрибуты, передаваемые в DOM). */
    type IntrinsicElements = {
        [K in keyof HTMLElementTagNameMap]: DOMAttributes & Record<string, unknown>;
    };
    type Element = JsxNode;
    type ElementAttributes = DOMAttributes;
    type ElementChildrenAttribute = {
        children: {};
    };
}
/**
 * JSX createElement. Tag may be:
 * - a string → HTML element (`hEl`);
 * - a function → component, invoked with props (incl. children);
 * - `Fragment` → document fragment.
 *
 * Children may arrive both as trailing arguments (classic transform) and
 * inside `props.children` (automatic transform compiles `<div>a</div>` to
 * `jsx("div", { children: "a" })`).
 *
 * РУС: JSX createElement. Тег может быть:
 * РУС: - строкой → HTML-элемент (`hEl`);
 * РУС: - функцией → компонент, вызывается с пропсами (включая детей);
 * РУС: - `Fragment` → документ-фрагмент.
 *
 * РУС: Дети могут приходить и как хвостовые аргументы (классический трансформ),
 * и внутри `props.children` (автоматический трансформ компилирует `<div>a</div>`
 * в `jsx("div", { children: "a" })`).
 */
export declare function createElement(tag: string | Component<any> | typeof Fragment, props: Record<string, any> | null, ...restChildren: any[]): Node;
/** Groups children without a wrapper element. (РУС: Группирует детей без элемента-обёртки.) */
export declare function Fragment({ children }: {
    children: JsxChild | JsxChild[];
}): DocumentFragment;
export declare function jsx(tag: string | Component<any> | typeof Fragment, props: Record<string, any> | null, key?: unknown): Node;
export declare const jsxs: typeof jsx;
export declare const jsxDEV: typeof jsx;
export { Fragment as default };
//# sourceMappingURL=jsx-runtime.d.ts.map