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
import { appendChildren, flattenChildren, hEl } from './dom.js';
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
export function createElement(tag, props, ...restChildren) {
    const propsChildren = (props && 'children' in props) ? props.children : [];
    const children = [...(Array.isArray(propsChildren) ? propsChildren : [propsChildren]), ...restChildren];
    const flat = flattenChildren(children);
    const clean = flat.filter(c => c !== null && c !== undefined && typeof c !== 'boolean');
    if (typeof tag === 'function') {
        return tag({ ...(props || {}), children: clean });
    }
    if (typeof tag !== 'string') {
        throw new TypeError(`bso5: invalid JSX tag: ${String(tag)}`);
    }
    return hEl(tag, props, clean);
}
/** Groups children without a wrapper element. (РУС: Группирует детей без элемента-обёртки.) */
export function Fragment({ children }) {
    const frag = document.createDocumentFragment();
    const list = Array.isArray(children) ? children : [children];
    appendChildren(frag, flattenChildren(list));
    return frag;
}
// Automatic runtime entry points (JSX transform "react-jsx"). The transform
// reserves `key`: it never lands in `props` and is passed as a THIRD positional
// argument instead — fold it back so components (e.g. `<For key={…}>`) receive
// it as a prop. On intrinsic (string) tags `key` is consumed like React does
// rather than leaking into the children list.
// РУС: Точки входа автоматического рантайма (JSX-трансформ "react-jsx").
// Трансформ резервирует `key`: он никогда не попадает в `props` и передаётся
// ТРЕТЬИМ позиционным аргументом — складываем его обратно, чтобы компоненты
// (напр. `<For key={…}>`) получали его как проп. На интринсик (строковых) тегах
// `key` потребляется как в React, а не утекает в список детей.
export function jsx(tag, props, key) {
    if (key !== undefined && typeof tag !== 'string') {
        props = { ...(props || {}), key };
    }
    return createElement(tag, props);
}
export const jsxs = jsx;
export const jsxDEV = jsx;
export { Fragment as default };
//# sourceMappingURL=jsx-runtime.js.map