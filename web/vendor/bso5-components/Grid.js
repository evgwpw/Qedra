import { jsx as _jsx, jsxs as _jsxs } from "bso5/jsx-runtime";
/**
 * bso5-components — a generic data Grid on top of the bso5 runtime.
 *
 * `Grid<Row>` renders any list of rows with a search box, sortable columns,
 * optional grouping with collapsible group rows and an empty state. The data
 * source is any `ReactiveSource` (plain array, `() => array` thunk, `Signal`
 * or a `$()`-bound value) — the grid re-derives filter → sort → group on every
 * change. All UI state (query, sort key/direction, collapsed groups) lives
 * inside the component instance, so two `<Grid>`s are fully independent.
 *
 * The component is **headless**: it renders semantic markup with stable class
 * names (`grid`, `toolbar`, `search`, `group-row`, `empty`, …) and leaves all
 * styling to the consumer.
 *
 * РУС: bso5-components — генерик-грид данных поверх рантайма bso5.
 *
 * РУС: `Grid<Row>` рендерит любой список строк с поиском, сортируемыми
 * колонками, опциональной группировкой со сворачиваемыми групповыми строками
 * и пустым состоянием. Источник данных — любой `ReactiveSource` (обычный
 * массив, `() => array`-танка, `Signal` или `$()`-значение) — грид
 * пересчитывает фильтр → сортировку → группировку при каждом изменении. Всё
 * UI-состояние (запрос, ключ/направление сортировки, свёрнутые группы) живёт
 * внутри инстанса компонента, поэтому два `<Grid>` полностью независимы.
 *
 * РУС: Компонент **headless**: он рендерит семантическую разметку со
 * стабильными именами классов (`grid`, `toolbar`, `search`, `group-row`,
 * `empty`, …) и оставляет всю стилизацию потребителю.
 *
 * @module
 */
import { For, Show, $, effect, resolveSource, signal } from 'bso5';
/* ── Grid ──────────────────────────────────────────────────── */
/* РУС: грид */
/**
 * Generic data grid: filter → sort → group, computed by an internal `effect()`
 * into a snapshot signal; the body renders it with a (keyed) `<For>`.
 *
 * РУС: Генерик-грид данных: фильтр → сортировка → группировка, вычисляемые
 * внутренним `effect()` в сигнал-снапшот; тело рендерит его (keyed-)`<For>`-ом.
 */
export function Grid(props) {
    const { rows, columns, filter, groupBy, initialSort, rowKey, searchPlaceholder, searchDebounce, searchDebounceMinItems, labels, empty = 'No rows match the current filter.', class: rootClass = 'grid', } = props;
    /* UI strings: explicit `labels` win, then the legacy single-purpose props,
     * then English defaults. Kept as plain strings, not signals: they are
     * static per instance and baked into once-built markup.
     * РУС: Подписи: явные `labels` важнее старых одиночных пропсов, затем
     * английские значения по умолчанию. Это обычные строки, не сигналы:
     * они статичны для инстанса и вшиваются в однократно построенную разметку. */
    const ui = {
        search: labels?.search ?? searchPlaceholder ?? 'Search',
        placeholder: labels?.searchPlaceholder ?? searchPlaceholder ?? 'Search…',
        sortDirection: labels?.sortDirection ?? 'Sort direction',
        descending: labels?.descending ?? '↓ desc',
        ascending: labels?.ascending ?? '↑ asc',
        rows: labels?.rows ?? 'rows:',
    };
    /* Instance state: fresh signals per component call — two Grids are
     * independent; note that static markup (headers, toolbar) is built once
     * and reads these signals through reactive `$()`/`Show` bindings only.
     * РУС: Состояние инстанса: свежие сигналы на каждый вызов компонента —
     * два грида независимы; статичная разметка (заголовки, тулбар) строится
     * один раз и читает эти сигналы только через реактивные `$()`/`Show`. */
    const query = signal('');
    const sortKey = signal(initialSort?.key ?? '');
    const sortDir = signal(initialSort?.dir ?? 'desc');
    const collapsedGroups = signal(new Set());
    /* ── derived snapshot: filter → sort → group ─────────────── */
    /* РУС: производный снапшот: фильтр → сортировка → группировка */
    const view = signal([]);
    const itemCount = signal(0);
    effect(() => {
        const all = resolveSource(rows) ?? [];
        const q = query.value.trim().toLowerCase();
        let list = q
            ? all.filter(row => filter
                ? filter(row, q)
                : columns.some(col => String(col.sort(row)).toLowerCase().includes(q)))
            : all.slice();
        const col = columns.find(c => c.key === sortKey.value);
        if (col) {
            const dir = sortDir.value === 'asc' ? 1 : -1;
            list = list.slice().sort((a, b) => {
                const va = col.sort(a);
                const vb = col.sort(b);
                return (va < vb ? -1 : va > vb ? 1 : 0) * dir;
            });
        }
        if (!groupBy) {
            view.value = list.map((row, index) => ({ kind: 'item', row, index }));
            itemCount.value = list.length;
            return;
        }
        const groups = new Map();
        const ungrouped = [];
        for (const row of list) {
            const key = groupBy(row);
            if (key === null)
                ungrouped.push(row);
            else {
                if (!groups.has(key))
                    groups.set(key, []);
                groups.get(key).push(row);
            }
        }
        const out = [];
        for (const row of ungrouped)
            out.push({ kind: 'item', row, index: 0 });
        const closed = collapsedGroups.value;
        for (const [key, rowsInGroup] of groups) {
            out.push({ kind: 'group', key, rows: rowsInGroup });
            if (!closed.has(key))
                rowsInGroup.forEach((row, gi) => out.push({ kind: 'item', row, index: gi }));
        }
        view.value = out;
        itemCount.value = list.length;
    });
    function toggleGroup(key) {
        const next = new Set(collapsedGroups.value);
        if (next.has(key))
            next.delete(key);
        else
            next.add(key);
        collapsedGroups.value = next;
    }
    /* Большие источники получают дебаунс: перерисовка таблицы на каждый символ
     * заметна уже на 300–400 строках, а на малых данных задержка только мешает
     * (и ломала бы «мгновенный» отклик в тестах). Порог и задержка — пропсы. */
    let queryTimer = null;
    const debounceMs = searchDebounce === false ? 0 : (searchDebounce ?? 120);
    const debounceMinItems = searchDebounceMinItems ?? 200;
    function onSearchInput(value) {
        const total = (resolveSource(rows) ?? []).length;
        if (queryTimer) {
            clearTimeout(queryTimer);
            queryTimer = null;
        }
        if (debounceMs <= 0 || total < debounceMinItems) {
            query.value = value;
            return;
        }
        queryTimer = setTimeout(() => { queryTimer = null; query.value = value; }, debounceMs);
    }
    // The JSX expression is typed as Node; the root is always a div, so the
    // downcast is safe (the same pattern the bso5 examples use).
    // РУС: JSX-выражение типизировано как Node; корень всегда div, поэтому
    // даункаст безопасен (тот же паттерн, что в примерах bso5).
    const root = (_jsxs("div", { class: rootClass, children: [_jsxs("div", { class: "toolbar", children: [_jsx("input", { type: "text", class: "search", "aria-label": ui.search, placeholder: ui.placeholder, onInput: e => { onSearchInput(e.target.value); } }), _jsxs("select", { class: "dir", "aria-label": ui.sortDirection, value: $(sortDir), onChange: e => { sortDir.value = e.target.value; }, children: [_jsx("option", { value: "desc", children: ui.descending }), _jsx("option", { value: "asc", children: ui.ascending })] }), _jsxs("span", { class: "chip", children: [ui.rows ? `${ui.rows} ` : '', _jsx("b", { children: $(itemCount) })] })] }), _jsxs("table", { children: [_jsx("thead", { children: _jsx("tr", { children: columns.map(col => (_jsxs("th", { scope: "col", class: col.headerClass ?? '', onClick: () => {
                                    if (col.sortable === false)
                                        return;
                                    if (sortKey.value === col.key)
                                        sortDir.value = sortDir.value === 'asc' ? 'desc' : 'asc';
                                    else {
                                        sortKey.value = col.key;
                                        sortDir.value = 'desc';
                                    }
                                }, children: [col.header, _jsx(Show, { when: () => sortKey.value === col.key, children: _jsx("span", { class: "arrow", children: _jsx(Show, { when: () => sortDir.value === 'asc', fallback: "\u2193", children: "\u2191" }) }) })] }))) }) }), _jsx("tbody", { children: _jsx(For, { each: view, children: (gridRow) => gridRow.kind === 'group' ? (_jsx("tr", { class: "group-row", "data-group": gridRow.key, tabindex: "0", onClick: () => toggleGroup(gridRow.key), onKeydown: e => {
                                    const k = e.key;
                                    if (k !== 'Enter' && k !== ' ')
                                        return;
                                    e.preventDefault();
                                    toggleGroup(gridRow.key);
                                }, children: _jsxs("td", { colspan: columns.length, children: [_jsx("span", { class: "toggle", children: _jsx(Show, { when: () => collapsedGroups.value.has(gridRow.key), fallback: "\u25BE", children: "\u25B8" }) }), gridRow.key, _jsxs("span", { class: "count", children: ["(", gridRow.rows.length, ")"] })] }) })) : (_jsx("tr", { children: columns.map(col => (_jsx("td", { class: col.class ?? '', children: col.cell(gridRow.row) }))) })) }, rowKey ? rowKeyFor : undefined) })] }), _jsx(Show, { when: () => itemCount.value === 0, children: _jsx("div", { class: "empty", children: empty }) })] }));
    /* A11y-состояние, которое нельзя выразить атрибутом в разметке (узлы
     * переиспользуются): aria-sort у заголовков и aria-expanded у групп. */
    // РУС: aria-sort и aria-expanded синхронизируются отдельным эффектом.
    const headCells = [...root.querySelectorAll('thead th')];
    effect(() => {
        const activeKey = sortKey.value;
        const dir = sortDir.value;
        headCells.forEach((th, i) => {
            const col = columns[i];
            if (!col)
                return;
            if (col.key === activeKey)
                th.setAttribute('aria-sort', dir === 'asc' ? 'ascending' : 'descending');
            else
                th.removeAttribute('aria-sort');
        });
        const closed = collapsedGroups.value;
        root.querySelectorAll('tr.group-row').forEach(tr => {
            const key = tr.dataset.group;
            if (key === undefined)
                return;
            tr.setAttribute('aria-expanded', String(!closed.has(key)));
        });
    });
    return root;
    /** Groups are keyed by their label; items — by the caller-supplied key. */
    /** РУС: Группы ключуются меткой; элементы — ключом, заданным вызывающим. */
    function rowKeyFor(gridRow) {
        if (!rowKey)
            return undefined;
        return gridRow.kind === 'group' ? `group:${gridRow.key}` : rowKey(gridRow.row);
    }
}
//# sourceMappingURL=Grid.js.map