import { jsx as _jsx, jsxs as _jsxs } from "bso5/jsx-runtime";
/**
 * bso5-components — a generic collapsible Tree on top of the bso5 runtime.
 *
 * `Tree` renders a hierarchy of `TreeData` nodes (label + optional children +
 * optional meta) between comment anchors. It ships its own search box: while
 * the query is non-empty the tree is filtered (nodes whose label matches or
 * that have a matching descendant stay) and auto-expanded so the matches are
 * visible. Expansion state and the query live inside the component instance,
 * so two `<Tree>`s are fully independent.
 *
 * The data source is any `ReactiveSource<TreeData | null>` — a plain object,
 * `() => object` thunk, `Signal` or a `$()`-bound value. Transformations
 * (sorting, deriving a tree from flat data, async loads into a signal) are the
 * consumer's job: feed the *final* tree in.
 *
 * The component is **headless**: it renders semantic markup with stable class
 * names (`tree`, `toolbar`, `search`, `node`, `row`, `caret`, `name`, `meta`,
 * `kids`, `empty`, …) and leaves all styling to the consumer.
 *
 * РУС: bso5-components — генерик-сворачиваемое дерево поверх рантайма bso5.
 *
 * РУС: `Tree` рендерит иерархию узлов `TreeData` (метка + опциональные дети +
 * опциональная мета) между комментариями-анкорами. Со своей строкой поиска:
 * пока запрос непуст, дерево фильтруется (остаются узлы с совпадением в метке
 * или совпадающим потомком) и авто-раскрывается, чтобы совпадения были видны.
 * Состояние раскрытия и запрос живут внутри инстанса компонента, поэтому два
 * `<Tree>` полностью независимы.
 *
 * РУС: Источник данных — любой `ReactiveSource<TreeData | null>` — обычный
 * объект, `() => object`-танка, `Signal` или `$()`-значение. Трансформации
 * (сортировка, постройка дерева из плоских данных, асинхронные загрузки в
 * сигнал) — задача потребителя: подавайте на вход *финальное* дерево.
 *
 * РУС: Компонент **headless**: рендерит семантическую разметку со стабильными
 * именами классов (`tree`, `toolbar`, `search`, `node`, `row`, `caret`,
 * `name`, `meta`, `kids`, `empty`, …) и оставляет стилизацию потребителю.
 *
 * @module
 */
import { For, $, effect, resolveSource, signal } from 'bso5';
/* ── helpers ───────────────────────────────────────────────── */
/* РУС: хелперы */
/** Keeps only nodes whose label or meta matches, or that have a matching descendant. */
/** РУС: Оставляет только узлы, чья метка или мета совпадает либо у которых есть совпадающий потомок. */
function filterTree(node, q) {
    const hit = node.label.toLowerCase().includes(q) || (node.meta?.toLowerCase().includes(q) ?? false);
    const kids = (node.children ?? [])
        .map(k => filterTree(k, q))
        .filter((k) => k !== null);
    if (!hit && kids.length === 0)
        return null;
    return kids.length > 0 ? { ...node, children: kids } : { ...node, children: null };
}
function countNodes(node) {
    if (!node)
        return 0;
    return 1 + (node.children ?? []).reduce((s, k) => s + countNodes(k), 0);
}
/* ── Tree ──────────────────────────────────────────────────── */
/* РУС: дерево */
/**
 * Generic collapsible tree with search: the internal `effect()` builds an
 * immutable `TreeView` snapshot (filter → capture expansion state); the whole
 * tree is then rendered from it, so `TreeItem` stays a pure function of
 * static data.
 *
 * РУС: Генерик-сворачиваемое дерево с поиском: внутренний `effect()` строит
 * иммутабельный снапшот `TreeView` (фильтр → захват состояния раскрытия);
 * затем всё дерево рендерится из него, поэтому `TreeItem` остаётся чистой
 * функцией статичных данных.
 */
export function Tree(props) {
    const { root, searchPlaceholder, nodeKey, renderLabel, searchDebounce, searchDebounceMinItems, showExpandAll = false, labels, empty = 'Nothing matches this filter.', class: rootClass = '', } = props;
    /* Подписи: явные `labels` важнее старых одиночных пропсов и умолчаний. */
    const ui = {
        search: labels?.search ?? searchPlaceholder ?? 'Search',
        placeholder: labels?.searchPlaceholder ?? searchPlaceholder ?? 'Search…',
        matched: labels?.matched ?? 'matched:',
        expandAll: labels?.expandAll ?? 'Expand all',
        collapseAll: labels?.collapseAll ?? 'Collapse all',
    };
    /* Курсор фокуса для клавиатуры: перерисовка дерева пересоздаёт узлы, и без
     * возврата фокуса навигация стрелками обрывалась бы после первого раскрытия. */
    // РУС: ключ узла, на который надо вернуть фокус после перерисовки.
    const focus = { pending: null };
    let treeEl = null;
    /* Instance state: fresh signals per component call — two Trees are
     * independent.
     * РУС: Состояние инстанса: свежие сигналы на каждый вызов компонента —
     * два дерева независимы. */
    const query = signal('');
    const expanded = signal(new Set());
    const matchCount = signal(0);
    /* ── derived snapshot: filter → capture expansion state ──── */
    /* РУС: производный снапшот: фильтр → захват состояния раскрытия */
    const treeView = signal({ root: null, query: '', expanded: new Set() });
    effect(() => {
        const src = resolveSource(root);
        const q = query.value.trim().toLowerCase();
        let r = src ? { ...src } : null;
        if (r && q)
            r = filterTree(r, q);
        treeView.value = { root: r, query: q, expanded: expanded.value };
        matchCount.value = countNodes(r);
    });
    /* ── render ──────────────────────────────────────────────── */
    /* РУС: рендер */
    /* Крупные деревья получают дебаунс поиска: перерисовка всего дерева на
     * каждый символ — O(N). Порог и задержка — пропсы. */
    // РУС: дебаунс поиска для крупных деревьев.
    let queryTimer = null;
    const debounceMs = searchDebounce === false ? 0 : (searchDebounce ?? 120);
    const debounceMinItems = searchDebounceMinItems ?? 200;
    function onSearchInput(value) {
        if (queryTimer) {
            clearTimeout(queryTimer);
            queryTimer = null;
        }
        if (debounceMs <= 0 || countNodes(resolveSource(root)) < debounceMinItems) {
            query.value = value;
            return;
        }
        queryTimer = setTimeout(() => { queryTimer = null; query.value = value; }, debounceMs);
    }
    /** Expand every directory, or collapse the tree back to the root. (РУС: Раскрыть все папки либо свернуть дерево до корня.) */
    function setAllExpanded(open) {
        if (!open) {
            expanded.value = new Set();
            return;
        }
        const src = resolveSource(root);
        expanded.value = new Set(src ? collectKeys(src, [], nodeKey) : []);
    }
    // The JSX expression is typed as Node; the root is always a div, so the
    // downcast is safe (the same pattern the bso5 examples use).
    // РУС: JSX-выражение типизировано как Node; корень всегда div, поэтому
    // даункаст безопасен (тот же паттерн, что в примерах bso5).
    const rootEl = (_jsxs("div", { children: [_jsxs("div", { class: "toolbar", children: [_jsx("input", { type: "text", class: "search", "aria-label": ui.search, placeholder: ui.placeholder, onInput: e => { onSearchInput(e.target.value); } }), showExpandAll ? (_jsxs("span", { class: "bulk", children: [_jsx("button", { type: "button", class: "expand-all", onClick: () => setAllExpanded(true), children: ui.expandAll }), _jsx("button", { type: "button", class: "collapse-all", onClick: () => setAllExpanded(false), children: ui.collapseAll })] })) : null, _jsxs("span", { class: "chip", children: [ui.matched ? `${ui.matched} ` : '', _jsx("b", { children: $(matchCount) })] })] }), _jsx(For, { each: () => [treeView.value], children: (v) => v.root !== null
                    ? _jsx("div", { class: `tree ${rootClass}`, role: "tree", "aria-label": v.root.label, ref: el => { treeEl = el; }, children: _jsx(TreeItem, { node: v.root, path: [], view: v, nodeKey: nodeKey, renderLabel: renderLabel, expanded: expanded, focus: focus, isRoot: true }) })
                    : _jsx("div", { class: "empty", children: empty }) })] }));
    /* Возврат фокуса после перерисовки: снапшот пересоздаёт узлы, а навигация
     * стрелками держится именно на текущем узле. Эффект создаётся после `<For>`,
     * поэтому выполняется уже по готовому DOM. */
    // РУС: эффект создан после <For> — срабатывает после перестройки дерева.
    effect(() => {
        treeView.value; // зависимость: любое изменение снапшота
        const pending = focus.pending;
        if (pending === null || !treeEl)
            return;
        focus.pending = null;
        const rows = [...treeEl.querySelectorAll('.row')];
        rows.find(row => row.dataset.key === pending)?.focus();
    });
    return rootEl;
}
/** A single node row; reads the frozen snapshot only, never signals. */
/** РУС: Строка одного узла; читает только замороженный снапшот, никогда сигналы. */
function TreeItem(props) {
    const { node, path, view, nodeKey, renderLabel, expanded, focus, isRoot } = props;
    // Ключ раскрытия: nodeKey вызывающего кода, иначе путь по меткам.
    // РУС: ключ раскрытия — nodeKey вызывающего, иначе путь по меткам.
    const key = nodeKey ? String(nodeKey(node, path)) : [...path, node.label].join('/');
    const isDir = (node.children ?? []).length > 0;
    // While filtering, everything is expanded so matches are visible; otherwise
    // expansion comes from the snapshot's captured expansion state.
    // РУС: При фильтрации всё раскрыто, чтобы совпадения были видны; иначе
    // раскрытие берётся из захваченного состояния раскрытия снапшота.
    const open = isDir && (view.query.length > 0 || view.expanded.has(key));
    const match = view.query.length > 0
        && (node.label.toLowerCase().includes(view.query) || (node.meta?.toLowerCase().includes(view.query) ?? false));
    /* Любое изменение раскрытия перерисовывает дерево, поэтому ключ узла
     * запоминается до записи, а возвращается уже после рендера. */
    // РУС: запоминаем узел до перерисовки, фокус вернётся после неё.
    const markFocus = () => { focus.pending = key; };
    const toggle = () => {
        if (!isDir)
            return;
        markFocus();
        const next = new Set(expanded.value);
        if (next.has(key))
            next.delete(key);
        else
            next.add(key);
        expanded.value = next; // → new snapshot → full tree re-render
        // РУС: → новый снапшот → полный ре-рендер дерева
    };
    const expand = () => {
        if (!isDir || open)
            return;
        markFocus();
        const next = new Set(expanded.value);
        next.add(key);
        expanded.value = next;
    };
    const collapse = () => {
        if (!isDir || !open)
            return;
        markFocus();
        const next = new Set(expanded.value);
        next.delete(key);
        expanded.value = next;
    };
    /** Moves focus to the neighbouring row in DOM order. (РУС: Переводит фокус на соседнюю строку в порядке DOM.) */
    const moveFocus = (row, delta) => {
        const tree = row.closest('.tree');
        if (!tree)
            return;
        const rows = [...tree.querySelectorAll('.row')];
        const next = rows[rows.indexOf(row) + delta];
        next?.focus();
    };
    return (_jsxs("div", { class: "node", role: "treeitem", "aria-expanded": isDir ? String(open) : undefined, children: [_jsxs("div", { class: "row", "data-key": key, tabindex: isRoot ? '0' : '-1', onClick: toggle, onKeydown: e => {
                    const k = e.key;
                    if (k === 'Enter' || k === ' ') {
                        e.preventDefault();
                        toggle();
                        return;
                    }
                    if (k === 'ArrowRight') {
                        e.preventDefault();
                        expand();
                        return;
                    }
                    if (k === 'ArrowLeft') {
                        e.preventDefault();
                        collapse();
                        return;
                    }
                    if (k === 'ArrowDown') {
                        e.preventDefault();
                        moveFocus(e.currentTarget, 1);
                        return;
                    }
                    if (k === 'ArrowUp') {
                        e.preventDefault();
                        moveFocus(e.currentTarget, -1);
                    }
                }, children: [_jsx("span", { class: `caret ${isDir ? '' : 'leaf'}`, children: isDir ? (open ? '▾' : '▸') : '·' }), _jsx("span", { class: `name ${isDir ? 'dir' : ''} ${match ? 'match' : ''}`, children: renderLabel ? renderLabel(node) : node.label }), node.meta ? _jsx("span", { class: "meta", children: node.meta }) : null] }), open ? (_jsx("div", { class: "kids", role: "group", children: _jsx(For, { each: node.children ?? [], children: (kid) => _jsx(TreeItem, { node: kid, path: [...path, node.label], view: view, nodeKey: nodeKey, renderLabel: renderLabel, expanded: expanded, focus: focus }) }) })) : null] }));
}
/** Every directory key of the tree, using the same key function as `TreeItem`. (РУС: Все ключи папок дерева, той же функцией, что и `TreeItem`.) */
function collectKeys(node, path, nodeKey) {
    const key = nodeKey ? String(nodeKey(node, path)) : [...path, node.label].join('/');
    const kids = node.children ?? [];
    if (kids.length === 0)
        return [];
    return [key, ...kids.flatMap(kid => collectKeys(kid, [...path, node.label], nodeKey))];
}
//# sourceMappingURL=Tree.js.map