/**
 * BSO5 — DOM construction helpers.
 *
 * `h(tag, attrs, ...children)` is the universal element factory: strongly
 * typed for every HTML tag, supports nested arrays, `null`/`undefined`/`false`
 * (rendered as nothing), reactive bound values (`$()`) in attributes, style
 * objects, event handlers and data-/aria- attributes. Reactive bindings can
 * be stopped later with `releaseBindings(root)` when a view is detached.
 *
 * РУС: BSO5 — хелперы конструирования DOM.
 *
 * РУС: `h(tag, attrs, ...children)` — универсальная фабрика элементов:
 * сильно типизирована для каждого HTML-тега, поддерживает вложенные массивы,
 * `null`/`undefined`/`false` (рендерится как ничего), реактивные привязанные
 * значения (`$()`) в атрибутах, style-объекты, обработчики событий и
 * data-/aria- атрибуты. Реактивные привязки можно позже остановить через
 * `releaseBindings(root)`, когда вью отсоединяется.
 *
 * @module
 */
import { type BoundValue } from './reactive.js';
/** Anything that can be rendered as an element child. (РУС: Всё, что может быть отрендерено как ребёнок элемента.) */
export type Content = string | number | boolean | null | undefined | Node | BoundValue | Content[];
/**
 * Value of a single style property: CSS text, a number (rendered as `px`) or a
 * reactive bound value.
 * (РУС: Значение одного CSS-свойства: текст, число (рендерится как `px`) или
 * реактивное привязанное значение.)
 */
export type StyleValue = string | number | BoundValue<unknown>;
/** Style object accepted by `h()`/JSX. (РУС: Style-объект, принимаемый `h()`/JSX.) */
export type StyleObject = Partial<Record<keyof CSSStyleDeclaration, StyleValue>>;
/**
 * Value of `class`/`className`: a string, a nested array (falsy entries are
 * skipped) or a map of class names to flags.
 *
 * ```ts
 * h('div', { class: ['card', isActive && 'card--active'] });
 * h('div', { class: { card: true, 'card--active': isActive } });
 * ```
 *
 * РУС: Значение `class`/`className`: строка, вложенный массив (ложные элементы
 * пропускаются) или карта «имя класса → флаг».
 */
export type ClassValue = string | false | null | undefined | readonly ClassValue[] | Readonly<Record<string, unknown>>;
/** Normalizes any accepted class value into a space-separated string. (РУС: Приводит любое допустимое значение класса к строке через пробел.) */
export declare function classToString(value: ClassValue): string;
/** Attribute object for `h()`; values may be reactive bound values. (РУС: Объект атрибутов для `h()`; значения могут быть реактивными привязанными.) */
export type Attrs = Record<string, unknown> & {
    class?: ClassValue | BoundValue<unknown>;
    className?: ClassValue | BoundValue<unknown>;
    style?: StyleObject | string;
    /** Receives the created element — the only supported way to grab a node. (РУС: Получает созданный элемент — единственный способ получить узел.) */
    ref?: (el: HTMLElement) => void;
    /** Event handlers keep their `Event` context so `e.target` is not `any`. (РУС: Обработчики сохраняют контекст `Event`, чтобы `e.target` не был `any`.) */
    [key: `on${string}`]: ((event: Event) => void) | undefined;
};
/** Normalizes any Content into a flat list of renderable Nodes. (РУС: Нормализует любой Content в плоский список рендерабельных узлов.) */
export declare function flattenChildren(children: Content[]): Array<Node | string | number | BoundValue>;
/**
 * Stops every reactive binding under `root` — `$()`-driven text nodes,
 * attributes and style properties. Call it when a view is detached from the
 * document so removed nodes stop receiving updates. Idempotent.
 *
 * РУС: Останавливает все реактивные привязки под `root` — текстовые узлы,
 * атрибуты и style-свойства, управляемые `$()`. Вызывайте, когда вью
 * отсоединяется от документа, чтобы удалённые узлы перестали получать
 * обновления. Идемпотентна.
 */
export declare function releaseBindings(root: Node): void;
/** Creates a live-updating text node bound to a reactive value. (РУС: Создаёт живо-обновляющийся текстовый узел, привязанный к реактивному значению.) */
export declare function boundTextNode(value: unknown): Text;
/** Applies an attribute/property to an element, supporting reactive values. (РУС: Применяет атрибут/свойство к элементу, поддерживая реактивные значения.) */
declare function applyAttr(el: HTMLElement, key: string, value: unknown): void;
/**
 * Maps a JSX handler prop to a DOM event name and phase.
 * `onClick` → `click`, `onDoubleClick` → `dblclick`, `onInputCapture` →
 * `input` in the capture phase.
 *
 * РУС: Переводит проп-обработчик в имя DOM-события и фазу: `onClick` → `click`,
 * `onDoubleClick` → `dblclick`, `onInputCapture` → `input` в фазе перехвата.
 */
export declare function parseEventProp(key: string): {
    event: string;
    capture: boolean;
};
/**
 * The universal element factory.
 *
 * ```ts
 * h('div', { class: 'card', style: { color: 'red' } },
 *   h('span', null, 'Hello'),
 *   [h('br'), items.map(i => h('li', null, i))],
 * )
 * ```
 *
 * РУС: Универсальная фабрика элементов.
 */
export declare function h<K extends keyof HTMLElementTagNameMap>(tag: K, attrs?: Attrs | ((el: HTMLElementTagNameMap[K]) => void) | null, ...children: Content[]): HTMLElementTagNameMap[K];
/** Shared implementation used by both `h()` and the JSX runtime. (РУС: Общая реализация, используемая и `h()`, и JSX-рантаймом.) */
export declare function hEl(tag: string, attrs: Attrs | ((el: any) => void) | null | undefined, children: Content[]): HTMLElement;
/** Recursively appends flattened children (bound values become text nodes). (РУС: Рекурсивно добавляет сплющенных детей (привязанные значения становятся текстовыми узлами).) */
export declare function appendChildren(parent: Node, children: Content[]): void;
export { applyAttr };
/** The handle returned by `mount()`. (РУС: Ручка, которую возвращает `mount()`.) */
export interface Mounted {
    /** The mounted node. (РУС: Смонтированный узел.) */
    readonly node: Node;
    /** Stops bindings and effects of the view and detaches it. Idempotent. (РУС: Останавливает привязки и эффекты вью и отсоединяет его. Идемпотентна.) */
    readonly dispose: () => void;
}
/**
 * Mounts a view into `target` and returns a handle that tears it down:
 * reactive DOM bindings are released, owned effects are stopped, the node is
 * removed.
 *
 * Pass a **thunk** (`() => <App />`) — not a ready node — to hand ownership of
 * the view's effects to `mount()`: a view built before the call has already
 * created its effects outside any scope, and those cannot be stopped later.
 *
 * ```ts
 * const app = mount(document.body, () => <App />);
 * app.dispose(); // bindings stopped, effects stopped, node removed
 * ```
 *
 * РУС: Монтирует вью в `target` и возвращает ручку для снятия: реактивные
 * DOM-привязки освобождаются, эффекты останавливаются, узел удаляется.
 *
 * Передавайте **танку** (`() => <App />`), а не готовый узел: вью, построенный
 * до вызова, уже создал свои эффекты вне области, и остановить их потом нельзя.
 */
export declare function mount(target: Element | DocumentFragment, view: Node | (() => Node)): Mounted;
//# sourceMappingURL=dom.d.ts.map