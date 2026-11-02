import type { ReactiveSource, JsxChild } from 'bso5';
/**
 * A single tree node: label, optional meta line (sizes, counts, …) and
 * optional children. `children === null`/omitted means a leaf.
 *
 * РУС: Узел дерева: метка, опциональная мета-строка (размеры, счётчики, …) и
 * опциональные дети. `children === null`/отсутствует — лист.
 */
export interface TreeData {
    /** Node label. (РУС: Метка узла.) */
    label: string;
    /** Secondary text rendered next to the label. Optional. (РУС: Вторичный текст рядом с меткой. Необязателен.) */
    meta?: string;
    /** Child nodes; `null`/omitted — this node is a leaf. (РУС: Дочерние узлы; `null`/нет — этот узел лист.) */
    children?: readonly TreeData[] | null;
    /** Extra class for the label `span`. Optional. (РУС: Дополнительный класс для `span`-метки. Необязателен.) */
    labelClass?: string;
}
/** UI strings of {@link Tree}; every field has an English default. (РУС: Подписи интерфейса {@link Tree}; у каждого поля есть английское значение по умолчанию.) */
export interface TreeLabels {
    /** Accessible name of the search box. (РУС: Доступное имя поля поиска.) */
    search?: string;
    /** Placeholder of the search box; defaults to `search`. (РУС: Плейсхолдер поиска; по умолчанию равен `search`.) */
    searchPlaceholder?: string;
    /** Prefix of the match counter; empty string hides it. (РУС: Префикс счётчика совпадений; пустая строка его скрывает.) */
    matched?: string;
    /** Text of the "expand all" button. (РУС: Текст кнопки «развернуть всё».) */
    expandAll?: string;
    /** Text of the "collapse all" button. (РУС: Текст кнопки «свернуть всё».) */
    collapseAll?: string;
}
/** Props of {@link Tree}. (РУС: Пропсы {@link Tree}.) */
export interface TreeProps {
    /** Data source: tree object, thunk, `Signal` or `$()`-bound value. (РУС: Источник данных: объект-дерево, танка, `Signal` или `$()`-значение.) */
    root: ReactiveSource<TreeData | null>;
    /** Search box placeholder. (РУС: Плейсхолдер строки поиска.) */
    searchPlaceholder?: string;
    /** Text shown when the tree is empty or filtered to nothing. Optional. (РУС: Текст, когда дерево пустое или отфильтровано в ноль. Необязательно.) */
    empty?: string;
    /** Stable node key for keyed rendering. Defaults to the node path. (РУС: Стабильный ключ узла для keyed-рендеринга. По умолчанию — путь узла.) */
    nodeKey?: (node: TreeData, path: string[]) => unknown;
    /**
     * Search debounce in ms; applies from `searchDebounceMinItems` nodes up.
     * `false` disables it. Default: 120.
     *
     * РУС: Задержка поиска в мс; действует от `searchDebounceMinItems` узлов.
     * `false` отключает. По умолчанию 120.
     */
    searchDebounce?: number | false;
    /** Node count from which the debounce kicks in. Default: 200. (РУС: Число узлов, с которого включается задержка. По умолчанию 200.) */
    searchDebounceMinItems?: number;
    /** Show "expand all" / "collapse all" buttons in the toolbar. Default: false. (РУС: Показывать кнопки «развернуть всё»/«свернуть всё». По умолчанию false.) */
    showExpandAll?: boolean;
    /** UI labels (placeholders, aria labels, counters, buttons). (РУС: Подписи интерфейса (плейсхолдеры, aria-метки, счётчики, кнопки).) */
    labels?: Partial<TreeLabels>;
    /** Extra class for the root element. (РУС: Дополнительный класс корневого элемента.) */
    class?: string;
    /** Node label renderer; defaults to `node.label`. (РУС: Рендер метки узла; по умолчанию `node.label`.) */
    renderLabel?: (node: TreeData) => JsxChild;
}
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
export declare function Tree(props: TreeProps): HTMLElement;
//# sourceMappingURL=Tree.d.ts.map