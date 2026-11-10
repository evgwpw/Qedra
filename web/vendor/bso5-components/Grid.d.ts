import type { ReactiveSource, JsxChild } from 'bso5';
/**
 * Column definition: header label, per-cell renderer and the value used for
 * sorting (and, optionally, plain-text filtering).
 *
 * РУС: Определение колонки: заголовок, рендер ячейки и значение для
 * сортировки (и, опционально, текстовой фильтрации).
 */
export interface Column<Row> {
    /** Stable column id, used to remember which column is sorted. (РУС: Стабильный id колонки — по нему помнится, что отсортировано.) */
    key: string;
    /** Header cell label. (РУС: Надпись в заголовке.) */
    header: string;
    /** Cell renderer; may return reactive bound values. (РУС: Рендер ячейки; может возвращать реактивные привязанные значения.) */
    cell: (row: Row) => JsxChild;
    /** Sort accessor: the value to compare rows by. (РУС: Аксессор сортировки: значение для сравнения строк.) */
    sort: (row: Row) => string | number;
    /** Extra class for the `td`. Optional. (РУС: Дополнительный класс для `td`. Необязателен.) */
    class?: string;
    /** Extra class for the `th`. Optional. (РУС: Дополнительный класс для `th`. Необязателен.) */
    headerClass?: string;
    /** Whether clicking the header sorts by this column (default: true). (РУС: Сортирует ли клик по заголовку по этой колонке (по умолчанию: true).) */
    sortable?: boolean;
}
/** UI strings of {@link Grid}; every field has an English default. (РУС: Подписи интерфейса {@link Grid}; у каждого поля есть английское значение по умолчанию.) */
export interface GridLabels {
    /** Accessible name of the search box. (РУС: Доступное имя поля поиска.) */
    search?: string;
    /** Placeholder of the search box; defaults to `search`. (РУС: Плейсхолдер поиска; по умолчанию равен `search`.) */
    searchPlaceholder?: string;
    /** Accessible name of the sort-direction control. (РУС: Доступное имя контрола направления сортировки.) */
    sortDirection?: string;
    /** Text of the descending option. (РУС: Текст варианта «по убыванию».) */
    descending?: string;
    /** Text of the ascending option. (РУС: Текст варианта «по возрастанию».) */
    ascending?: string;
    /** Prefix of the row counter; empty string hides the counter text. (РУС: Префикс счётчика строк; пустая строка скрывает текст счётчика.) */
    rows?: string;
}
/** Props of {@link Grid}. (РУС: Пропсы {@link Grid}.) */
export interface GridProps<Row> {
    /** Data source: array, thunk, `Signal` or `$()`-bound value. (РУС: Источник данных: массив, танка, `Signal` или `$()`-значение.) */
    rows: ReactiveSource<readonly Row[]>;
    /** Column definitions. (РУС: Определения колонок.) */
    columns: readonly Column<Row>[];
    /**
     * Plain-text filter predicate. The default searches `sort(row)` values.
     * (РУС: Предикат текстового фильтра. По умолчанию ищет по значениям `sort(row)`.)
     */
    filter?: (row: Row, loweredQuery: string) => boolean;
    /**
     * Groups rows by the returned label; return `null` for no grouping for that
     * row (it lands in an ungrouped bucket rendered before the groups).
     * (РУС: Группирует строки по возвращённой метке; `null` — строка без группы,
     * попадает в негруппированный бакет, рендеримый перед группами.)
     */
    groupBy?: (row: Row) => string | null;
    /** Initial sort column key and direction. Optional. (РУС: Начальная колонка сортировки и направление. Необязательно.) */
    initialSort?: {
        key: string;
        dir: 'asc' | 'desc';
    };
    /**
     * Stable row key for keyed `<For>` (DOM-node reuse). Optional. Called with
     * the row only: the rendered index is deliberately not part of the key, so
     * sorting reorders existing nodes instead of recreating them.
     *
     * РУС: Стабильный ключ строки для keyed-`<For>` (переиспользование
     * DOM-узлов). Необязателен. Вызывается только со строкой: индекс намеренно
     * не входит в ключ, иначе сортировка пересоздавала бы все узлы.
     */
    rowKey?: (row: Row) => unknown;
    /** Search box placeholder. (РУС: Плейсхолдер строки поиска.) */
    searchPlaceholder?: string;
    /**
     * Search debounce in ms. Applies only to sources of at least
     * `searchDebounceMinItems` rows (small tables must react instantly).
     * `false` disables it. Default: 120.
     *
     * РУС: Задержка поиска в мс. Действует только на источники от
     * `searchDebounceMinItems` строк (маленькие таблицы должны отвечать сразу).
     * `false` отключает. По умолчанию 120.
     */
    searchDebounce?: number | false;
    /** Row count from which the debounce kicks in. Default: 200. (РУС: Число строк, с которого включается задержка. По умолчанию 200.) */
    searchDebounceMinItems?: number;
    /** Text shown when no rows match. Optional. (РУС: Текст при отсутствии строк. Необязательно.) */
    empty?: string;
    /** UI labels (placeholders, aria labels, counter prefix). (РУС: Подписи интерфейса (плейсхолдеры, aria-метки, префикс счётчика).) */
    labels?: Partial<GridLabels>;
    /** Extra class for the root element. (РУС: Дополнительный класс корневого элемента.) */
    class?: string;
}
/**
 * Generic data grid: filter → sort → group, computed by an internal `effect()`
 * into a snapshot signal; the body renders it with a (keyed) `<For>`.
 *
 * РУС: Генерик-грид данных: фильтр → сортировка → группировка, вычисляемые
 * внутренним `effect()` в сигнал-снапшот; тело рендерит его (keyed-)`<For>`-ом.
 */
export declare function Grid<Row>(props: GridProps<Row>): HTMLElement;
//# sourceMappingURL=Grid.d.ts.map