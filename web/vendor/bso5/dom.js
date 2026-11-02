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
import { createScope, dispose, isBoundValue, runInScope } from './reactive.js';
/** Normalizes any accepted class value into a space-separated string. (РУС: Приводит любое допустимое значение класса к строке через пробел.) */
export function classToString(value) {
    if (!value)
        return ''; // false, '', null, undefined
    if (typeof value === 'string')
        return value.trim();
    if (Array.isArray(value)) {
        return value.map(item => classToString(item)).filter(Boolean).join(' ');
    }
    const out = [];
    for (const [name, on] of Object.entries(value)) {
        if (on)
            out.push(name);
    }
    return out.join(' ');
}
/** Normalizes any Content into a flat list of renderable Nodes. (РУС: Нормализует любой Content в плоский список рендерабельных узлов.) */
export function flattenChildren(children) {
    const out = [];
    const walk = (c) => {
        if (c === null || c === undefined || c === false || c === true)
            return;
        if (Array.isArray(c)) {
            c.forEach(walk);
            return;
        }
        out.push(c);
    };
    children.forEach(walk);
    return out;
}
/** Cleanups of reactive DOM bindings, keyed by the node they update. (РУС: Очистки реактивных DOM-привязок, ключ — обновляемый ими узел.) */
const domBindings = new WeakMap();
/** Registers a binding cleanup for a node (used by `releaseBindings()`). (РУС: Регистрирует очистку привязки для узла (используется `releaseBindings()`).) */
function registerBinding(node, stop) {
    let set = domBindings.get(node);
    if (!set)
        domBindings.set(node, (set = new Set()));
    set.add(stop);
}
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
export function releaseBindings(root) {
    const stops = domBindings.get(root);
    if (stops) {
        for (const stop of [...stops])
            stop();
        domBindings.delete(root);
    }
    root.childNodes.forEach(releaseBindings);
}
/** Creates a live-updating text node bound to a reactive value. (РУС: Создаёт живо-обновляющийся текстовый узел, привязанный к реактивному значению.) */
export function boundTextNode(value) {
    const read = () => (isBoundValue(value) ? value.value : value);
    const node = document.createTextNode(stringify(read()));
    if (isBoundValue(value)) {
        registerBinding(node, value.subscribe(() => { node.textContent = stringify(read()); }));
    }
    return node;
}
function stringify(v) {
    if (v === null || v === undefined)
        return '';
    if (typeof v === 'object') {
        const str = String(v);
        return str === '[object Object]' ? JSON.stringify(v) : str;
    }
    return String(v);
}
/** Sets a single style property, supporting reactive bound values. (РУС: Устанавливает одно style-свойство, поддерживая реактивные привязанные значения.) */
function setStyleProp(el, prop, v) {
    if (isBoundValue(v)) {
        el.style[prop] = stringify(v.value);
        registerBinding(el, v.subscribe(() => { el.style[prop] = stringify(v.value); }));
        return;
    }
    el.style[prop] = typeof v === 'number' ? `${v}px` : stringify(v);
}
/** Applies an attribute/property to an element, supporting reactive values. (РУС: Применяет атрибут/свойство к элементу, поддерживая реактивные значения.) */
function applyAttr(el, key, value) {
    if (isBoundValue(value)) {
        // Reactive attribute: apply now and keep it updated.
        // РУС: Реактивный атрибут: применяем сразу и держим обновлённым.
        applyAttrRaw(el, key, value.value);
        registerBinding(el, value.subscribe(() => applyAttrRaw(el, key, value.value)));
        return;
    }
    applyAttrRaw(el, key, value);
}
/** Applies a plain (non-reactive) attribute value. (РУС: Применяет обычное (нереактивное) значение атрибута.) */
function applyAttrRaw(el, key, value) {
    // `ref` is not an attribute: it is the element itself, handed to the caller.
    // РУС: `ref` — не атрибут, а сам элемент, отданный вызывающему.
    if (key === 'ref') {
        if (typeof value === 'function')
            value(el);
        return;
    }
    if (value === null || value === undefined || value === false) {
        el.removeAttribute(key);
        return;
    }
    if (key === 'class' || key === 'className') {
        // Arrays and objects are normalized here: `['a', cond && 'b']` and
        // `{ a: true, b: false }` are the two forms a template usually produces.
        // РУС: Массивы и объекты нормализуются здесь: `['a', cond && 'b']` и
        // `{ a: true, b: false }` — две формы, которые обычно и получаются в разметке.
        const text = classToString(value);
        if (text)
            el.className = text;
        else
            el.removeAttribute('class'); // пустой список не оставляет `class=""`
        return;
    }
    if (key === 'style') {
        if (typeof value === 'object' && value !== null) {
            // Style object: each property may itself be a reactive bound value.
            // РУС: Style-объект: каждое свойство само может быть реактивным привязанным значением.
            for (const [prop, v] of Object.entries(value)) {
                setStyleProp(el, prop, v);
            }
        }
        else if (value) {
            el.setAttribute('style', String(value));
        }
        return;
    }
    if (key === 'dataset' && typeof value === 'object') {
        Object.entries(value).forEach(([k, v]) => {
            el.dataset[k] = String(v);
        });
        return;
    }
    if (key.startsWith('on') && typeof value === 'function') {
        const { event, capture } = parseEventProp(key);
        el.addEventListener(event, value, capture ? { capture: true } : undefined);
        return;
    }
    if (key === 'value' || key === 'checked' || key === 'selected' || key === 'disabled') {
        // Live properties that must not be stringified.
        // РУС: Живые свойства, которые нельзя строковывать.
        el[key] = value;
        return;
    }
    if (key in el && typeof value !== 'object') {
        // Known DOM property (id, title, href, ...).
        // РУС: Известное DOM-свойство (id, title, href, ...).
        el[key] = value;
        return;
    }
    // Fallback: attribute (data-*, aria-*, custom).
    // РУС: Фолбэк: атрибут (data-*, aria-*, кастомные).
    el.setAttribute(key, typeof value === 'object' ? stringify(value) : String(value));
}
/**
 * Maps a JSX handler prop to a DOM event name and phase.
 * `onClick` → `click`, `onDoubleClick` → `dblclick`, `onInputCapture` →
 * `input` in the capture phase.
 *
 * РУС: Переводит проп-обработчик в имя DOM-события и фазу: `onClick` → `click`,
 * `onDoubleClick` → `dblclick`, `onInputCapture` → `input` в фазе перехвата.
 */
export function parseEventProp(key) {
    let raw = key.slice(2);
    const capture = raw.endsWith('Capture');
    if (capture)
        raw = raw.slice(0, -'Capture'.length);
    raw = raw.toLowerCase();
    // В DOM событие называется `dblclick`, а не `doubleclick`: без этой
    // перекладки `onDoubleClick` молча не срабатывает никогда.
    // РУС: в DOM событие называется `dblclick` — без перекладки обработчик молчит.
    return { event: raw === 'doubleclick' ? 'dblclick' : raw, capture };
}
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
export function h(tag, attrs, ...children) {
    return hEl(tag, attrs, children);
}
/** Shared implementation used by both `h()` and the JSX runtime. (РУС: Общая реализация, используемая и `h()`, и JSX-рантаймом.) */
export function hEl(tag, attrs, children) {
    const el = document.createElement(tag);
    // `<select>.value` must be applied after its <option> children exist,
    // otherwise the assignment is silently dropped by the browser.
    // РУС: `<select>.value` надо применять после появления <option>, иначе
    // браузер молча отбрасывает присваивание.
    let deferredValue;
    let hasDeferredValue = false;
    if (typeof attrs === 'function') {
        attrs(el);
    }
    else if (attrs) {
        for (const [key, value] of Object.entries(attrs)) {
            if (key === 'children')
                continue; // handled separately by JSX runtime
            // РУС: обрабатывается отдельно JSX-рантаймом
            if (tag === 'select' && key === 'value') {
                deferredValue = value;
                hasDeferredValue = true;
                continue;
            }
            applyAttr(el, key, value);
        }
    }
    appendChildren(el, children);
    if (hasDeferredValue)
        applyAttr(el, 'value', deferredValue);
    return el;
}
/** Recursively appends flattened children (bound values become text nodes). (РУС: Рекурсивно добавляет сплющенных детей (привязанные значения становятся текстовыми узлами).) */
export function appendChildren(parent, children) {
    for (const child of children) {
        if (isBoundValue(child)) {
            parent.appendChild(boundTextNode(child));
        }
        else if (child === null || child === undefined || typeof child === 'boolean') {
            continue;
        }
        else if (Array.isArray(child)) {
            appendChildren(parent, child);
        }
        else if (typeof child === 'string' || typeof child === 'number') {
            parent.appendChild(document.createTextNode(String(child)));
        }
        else {
            parent.appendChild(child);
        }
    }
}
export { applyAttr };
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
export function mount(target, view) {
    const scope = createScope();
    const node = typeof view === 'function' ? runInScope(scope, view) : view;
    target.appendChild(node);
    let disposed = false;
    const disposeView = () => {
        if (disposed)
            return;
        disposed = true;
        releaseBindings(node);
        dispose(scope);
        node.parentNode?.removeChild(node);
    };
    return { node, dispose: disposeView };
}
//# sourceMappingURL=dom.js.map