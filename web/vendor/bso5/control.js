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
import { Signal, createScope, dispose, effect, isBoundValue, onScopeDispose, runInScope } from './reactive.js';
import { boundTextNode, flattenChildren, releaseBindings } from './dom.js';
/** Reads the current value of a reactive source; auto-tracks inside `effect()`. (РУС: Читает текущее значение реактивного источника; автотрекается внутри `effect()`.) */
export function resolveSource(src) {
    if (typeof src === 'function')
        return src();
    if (src instanceof Signal)
        return src.value;
    if (isBoundValue(src))
        return src.value;
    return src;
}
/** Normalizes any JsxChild into concrete DOM nodes. (РУС: Нормализует любой JsxChild в конкретные DOM-узлы.) */
function toNodes(child) {
    return flattenChildren([child]).map(c => {
        if (typeof c === 'string' || typeof c === 'number')
            return document.createTextNode(String(c));
        if (isBoundValue(c))
            return boundTextNode(c);
        return c;
    });
}
/**
 * Unwraps `[fn]` — the shape the JSX runtime delivers for a function child —
 * into the bare function.
 *
 * РУС: Разворачивает `[fn]` — форму, которую JSX-рантайм доставляет для
 * ребёнка-функции — в саму функцию.
 */
function unwrapChild(children) {
    return Array.isArray(children) && children.length === 1 && typeof children[0] === 'function'
        ? children[0]
        : children;
}
/** Requires a function child, with a helpful error message. (РУС: Требует ребёнка-функцию с понятным сообщением об ошибке.) */
function childFn(children, what) {
    const fn = Array.isArray(children) ? children[0] : children;
    if (typeof fn !== 'function') {
        throw new TypeError(`bso5: <${what}> requires a function child, e.g. {(item, i) => <li />}`);
    }
    return fn;
}
/** Removes every node rendered between the two anchors. (РУС: Удаляет все узлы, отрендеренные между двумя анкорами.) */
function clearBetween(start, end) {
    const host = end.parentNode;
    if (!host)
        return;
    let node = start.nextSibling;
    while (node && node !== end) {
        const next = node.nextSibling;
        host.removeChild(node);
        node = next;
    }
}
/** Inserts `nodes` right before the end anchor (fragments and live parents). (РУС: Вставляет `nodes` прямо перед конечным анкором (фрагменты и живые родители).) */
function insertAll(nodes, end) {
    const host = end.parentNode;
    if (!host)
        return;
    for (const n of nodes)
        host.insertBefore(n, end);
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
export function For(props) {
    const start = document.createComment('for');
    const end = document.createComment('/for');
    const frag = document.createDocumentFragment();
    frag.append(start, end);
    const render = childFn(unwrapChild(props.children), 'For');
    const keyOf = props.key;
    // Unkeyed: full re-render — simple and correct.
    // РУС: Без ключа: полный ре-рендер — просто и корректно.
    if (!keyOf) {
        // Every pass owns its effects; the previous pass is torn down before the
        // new nodes go in, so nothing from a removed render keeps running.
        // РУС: Каждый проход владеет своими эффектами; предыдущий проход сносится
        // до вставки новых узлов, поэтому снятый рендер ничего не продолжает.
        let passScope = createScope();
        let mounted = [];
        const stop = effect(() => {
            const items = resolveSource(props.each) ?? [];
            const scope = createScope();
            const nodes = [];
            runInScope(scope, () => {
                for (let i = 0; i < items.length; i++) {
                    nodes.push(...toNodes(render(items[i], i)));
                }
            });
            // Tear down the previous pass: effects, then DOM bindings, then nodes.
            // РУС: Снимаем предыдущий проход: эффекты, затем DOM-привязки, затем узлы.
            dispose(passScope);
            for (const n of mounted)
                releaseBindings(n);
            passScope = scope;
            mounted = nodes;
            clearBetween(start, end);
            insertAll(nodes, end);
        });
        onScopeDispose(() => {
            stop();
            dispose(passScope);
        });
        return frag;
    }
    let prev = new Map();
    const stopKeyed = effect(() => {
        const items = resolveSource(props.each) ?? [];
        const host = end.parentNode;
        if (!host)
            return;
        // Collect the new group order, reusing nodes by key. Checking `next`
        // first also collapses duplicate keys in one batch without a wasted
        // second render (first occurrence wins).
        // РУС: Собираем новый порядок групп, переиспользуя узлы по ключу. Проверка
        // `next` первой также схлопывает дубликаты ключей в одном батче без
        // потерянного второго рендера (побеждает первое вхождение).
        const next = new Map();
        for (let i = 0; i < items.length; i++) {
            const k = keyOf(items[i], i);
            const existing = next.get(k) ?? prev.get(k);
            if (existing) {
                next.set(k, existing);
                continue;
            }
            const scope = createScope();
            const nodes = runInScope(scope, () => toNodes(render(items[i], i)));
            next.set(k, { nodes, scope });
        }
        // Place the groups in list order before `end`. Moving only the nodes that
        // are actually out of place keeps a no-op update (same order, new array)
        // free: Node.prototype.insertBefore on a node that is already in position
        // is the single most expensive DOM call in the whole render.
        // РУС: Расставляем группы в порядке списка перед `end`. Двигаем только
        // узлы, стоящие не на своём месте: обновление «тот же порядок, новый
        // массив» тогда ничего не стоит, а insertBefore для узла на месте —
        // самый дорогой DOM-вызов всего рендера.
        let cursor = start;
        for (const group of next.values()) {
            for (const n of group.nodes) {
                if (n.parentNode !== host || n.previousSibling !== cursor)
                    host.insertBefore(n, end);
                cursor = n;
            }
        }
        // Drop the groups whose keys left the list: stop their effects, release
        // their DOM bindings, then remove the nodes.
        // РУС: Удаляем группы, чьи ключи исчезли из списка: останавливаем их
        // эффекты, снимаем DOM-привязки, затем убираем узлы.
        for (const [k, group] of prev) {
            if (next.has(k))
                continue;
            dispose(group.scope);
            for (const n of group.nodes) {
                if (n.parentNode === host) {
                    releaseBindings(n);
                    host.removeChild(n);
                }
            }
        }
        prev = next;
    });
    onScopeDispose(() => {
        stopKeyed();
        for (const group of prev.values())
            dispose(group.scope);
        prev = new Map();
    });
    return frag;
}
/** Reactive conditional rendering between comment anchors (no wrapper). (РУС: Реактивный условный рендер между комментариями-анкорами (без обёртки).) */
export function Show(props) {
    const start = document.createComment('show');
    const end = document.createComment('/show');
    const frag = document.createDocumentFragment();
    frag.append(start, end);
    const child = unwrapChild(props.children);
    const fallback = props.fallback ?? null;
    // A thunk branch is rebuilt on every show and torn down on every hide, so a
    // hidden tab stops reacting to model writes. A ready-made node cannot be
    // resurrected once its bindings are released (they live in a WeakMap keyed
    // by that very node), so node branches are cached and keep their
    // subscriptions until the Show is disposed: pass a thunk when the branch
    // must really be torn down.
    // РУС: Ветка-танка строится заново при каждом показе и снимается при
    // скрытии, поэтому скрытая вкладка перестаёт реагировать на записи. Готовый
    // узел после снятия привязок «оживить» нельзя (они лежат в WeakMap по самому
    // узлу), поэтому узловые ветки кешируются и держат подписки до сноса Show:
    // если нужен настоящий снос — передавайте танку.
    let branchScope = null;
    let branchNodes = [];
    /** True when the mounted branch was built from a thunk (and can be rebuilt). (РУС: Истинно, когда смонтированная ветка построена из танки и её можно пересобрать.) */
    let branchIsThunk = false;
    /** Node branches are single-use: cached, never re-bound. (РУС: Узловые ветки одноразовые: кешируются, но не перепривязываются.) */
    const cache = { main: null, fallback: null };
    /** Last rendered decision; `null` before the first render. (РУС: Последнее отрендеренное решение; `null` до первого рендера.) */
    let shown = null;
    /** Tears down a thunk branch (a node branch is kept for reuse). (РУС: Снимает ветку-танку; узловая ветка остаётся для повторного показа.) */
    const releaseThunkBranch = () => {
        if (!branchIsThunk)
            return;
        if (branchScope) {
            dispose(branchScope);
            branchScope = null;
        }
        for (const n of branchNodes)
            releaseBindings(n);
        branchNodes = [];
        branchIsThunk = false;
    };
    const stop = effect(() => {
        const show = !!resolveSource(props.when);
        const branch = show ? child : fallback;
        const isFunction = typeof branch === 'function';
        // A cached (node) branch only changes when the decision flips: re-running
        // the effect for `when={() => count > 10}` must not rebuild the DOM on
        // every `count` write. Thunks are re-evaluated on every run, because they
        // may read reactive values themselves.
        // РУС: Закешированная (узловая) ветка меняется только при смене решения:
        // перезапуск эффекта у `when={() => count > 10}` не должен перестраивать
        // DOM на каждую запись `count`. Танки перевычисляются на каждый прогон,
        // так как сами могут читать реактивные значения.
        if (!isFunction && shown === show)
            return;
        shown = show;
        releaseThunkBranch();
        if (branch === null || branch === undefined || branch === false) {
            clearBetween(start, end);
            return;
        }
        if (isFunction) {
            const scope = createScope();
            const nodes = runInScope(scope, () => toNodes(branch()));
            branchScope = scope;
            branchNodes = nodes;
            branchIsThunk = true;
            clearBetween(start, end);
            insertAll(nodes, end);
            return;
        }
        const cacheKey = show ? 'main' : 'fallback';
        let nodes = cache[cacheKey];
        if (!nodes) {
            nodes = toNodes(branch);
            cache[cacheKey] = nodes;
        }
        branchNodes = nodes;
        clearBetween(start, end);
        insertAll(nodes, end);
    });
    onScopeDispose(() => {
        stop();
        releaseThunkBranch();
        for (const nodes of [cache.main, cache.fallback]) {
            for (const n of nodes ?? [])
                releaseBindings(n);
        }
        cache.main = null;
        cache.fallback = null;
    });
    return frag;
}
//# sourceMappingURL=control.js.map