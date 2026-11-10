# bso5-components

> Переиспользуемые UI-компоненты для [bso5](https://www.npmjs.com/package/bso5) — грид с
> фильтром/сортировкой/группировкой и рекурсивное дерево с поиском. Без CSS-фреймворка:
> компоненты headless, стили за вами.

**~2.5 kB min+gzip** · ноль зависимостей (кроме peer `bso5`)

[English version](./README.en.md)

## Установка

```bash
npm install bso5 bso5-components
```

`bso5` — peer-зависимость: она должна быть установлена один раз в вашем
приложении (две копии в бандле = два разных символа `REACTIVE_VALUE` =
`$()`-привязки молча ломаются).

Для разработки самого пакета нужен Node ≥ 22.12 (требование vitest 5).

## `<Grid>` — генерик-грид

```tsx
import { signal } from 'bso5';
import { Grid } from 'bso5-components';
import type { Column } from 'bso5-components';

interface Issue { id: number; title: string; severity: string; project: string }

const COLS: Column<Issue>[] = [
  { key: 'id',    header: 'ID',    sort: it => it.id,    cell: it => it.id },
  { key: 'title', header: 'Title', sort: it => it.title, cell: it => it.title },
  {
    key: 'severity',
    header: 'Sev',
    sort: it => it.severity,
    cell: it => <span class="sev">{it.severity}</span>,
    class: 'sev-cell',
  },
];

const issues = signal<Issue[]>(ISSUES);

<Grid
  rows={issues}                                  // массив | () => массив | Signal | $()
  columns={COLS}
  groupBy={it => it.project}                     // опционально, null — без группы
  initialSort={{ key: 'id', dir: 'desc' }}        // опционально
  rowKey={it => it.id}                           // опционально, включает keyed-режим
  searchPlaceholder="Поиск…"
  empty="Ничего не найдено."
/>
```

**Что умеет:** поиск по всем строкам (или по своему предикату), сортировка кликом
по заголовку, группировка со сворачиваемыми группами, счётчик строк, пустое
состояние. Состояние (запрос, сортировка, свёрнутые группы) живёт **внутри**
компонента — экземпляры независимы.

**Свойства `GridProps<Row>`:**

| Проп | Тип | Описание |
| --- | --- | --- |
| `rows` | `ReactiveSource<readonly Row[]>` | Источник данных: массив, `() => массив` (перечитывается, автотрекается), `Signal` или `$()` |
| `columns` | `readonly Column<Row>[]` | Колонки — см. таблицу ниже |
| `filter?` | `(row: Row, loweredQuery: string) => boolean` | Свой матчер поиска; `loweredQuery` уже приведён к нижнему регистру. По умолчанию ищется подстрока в значениях `sort(row)` всех колонок |
| `groupBy?` | `(row: Row) => string \| null` | Метка группы; `null` — строка без группы (рендерится перед группами) |
| `initialSort?` | `{ key: string; dir: 'asc' \| 'desc' }` | Начальная сортировка; отражается в контроле направления |
| `rowKey?` | `(row: Row) => unknown` | Стабильный ключ строки: включает keyed-`<For>`. Вызывается **только со строкой** — индекс в ключ не входит, иначе сортировка пересоздавала бы узлы |
| `searchPlaceholder?` | `string` | Плейсхолдер поиска (он же `aria-label`) |
| `empty?` | `string` | Текст пустого состояния |
| `class?` | `string` | Доп. класс корневого элемента (по умолчанию `grid`) |

**Колонка `Column<Row>`:**

| Поле | Тип | Обязательно | Описание |
| --- | --- | --- | --- |
| `key` | `string` | да | Стабильный id: по нему запоминается активная сортировка |
| `header` | `string` | да | Надпись в `th` |
| `cell` | `(row: Row) => JsxChild` | да | Рендер ячейки; может возвращать `$()`-значения |
| `sort` | `(row: Row) => string \| number` | да | Значение для сортировки (и для текстового поиска по умолчанию) |
| `sortable?` | `boolean` | нет | Клик по заголовку сортирует (по умолчанию `true`) |
| `class?` | `string` | нет | Доп. класс `td` |
| `headerClass?` | `string` | нет | Доп. класс `th` |

**Клавиатура и ARIA:** заголовки получают `scope="col"` и `aria-sort`
(`ascending`/`descending` только у активной колонки), строка группы —
`tabindex="0"`, `aria-expanded` и переключение по Enter/Space, поле поиска —
`aria-label`.

## `<Tree>` — рекурсивное дерево

```tsx
import { signal } from 'bso5';
import { Tree } from 'bso5-components';
import type { TreeData } from 'bso5-components';

// Дерево — просто данные: label + meta + дети.
const tree = signal<TreeData>({
  label: 'bso5',
  meta: '7 items',
  children: [
    { label: 'src', meta: '6 items', children: [
      { label: 'index.ts', meta: '412 B', children: null },
    ]},
  ],
});

<Tree root={tree} searchPlaceholder="Фильтр…" />
```

**Что умеет:** поиск по метке и мете с авто-раскрытием совпадений, раскрытие
узлов, счётчик совпадений, пустое состояние. Раскрытие и запрос живут внутри
экземпляра.

**Свойства `TreeProps`:**

| Проп | Тип | Описание |
| --- | --- | --- |
| `root` | `ReactiveSource<TreeData \| null>` | Корень: объект, `() => объект`, `Signal` или `$()` |
| `searchPlaceholder?` | `string` | Плейсхолдер поиска (он же `aria-label`, если не задан `labels.search`) |
| `searchDebounce?` | `number \| false` | Задержка поиска в мс; действует от `searchDebounceMinItems` узлов, `false` отключает (по умолчанию 120) |
| `searchDebounceMinItems?` | `number` | Порог узлов, с которого включается задержка (по умолчанию 200) |
| `showExpandAll?` | `boolean` | Кнопки «развернуть всё» / «свернуть всё» в панели (по умолчанию `false`) |
| `labels?` | `Partial<TreeLabels>` | Подписи интерфейса — см. таблицу ниже |
| `empty?` | `string` | Текст, когда дерево пусто или отфильтровано в ноль |
| `nodeKey?` | `(node: TreeData, path: string[]) => unknown` | Ключ узла для состояния раскрытия. По умолчанию — путь `label/label/…` |
| `renderLabel?` | `(node: TreeData) => JsxChild` | Свой рендер метки (иконки, ссылки, обработчики) |
| `class?` | `string` | Доп. класс корневого `.tree` |

**`TreeData`:** `label: string`, `meta?: string`, `children?: readonly TreeData[] | null`,
`labelClass?: string`.

**Клавиатура и ARIA:** корень — `role="tree"`, узел — `role="treeitem"` +
`aria-expanded`, дети — `role="group"`. По Tab дерево — одна остановка (корневая
строка, `tabindex="0"`), дальше `ArrowDown`/`ArrowUp` двигают фокус по видимым
строкам, Enter/Space переключают узел, `ArrowRight` раскрывает, `ArrowLeft`
сворачивает. Фокус возвращается на тот же узел после перерисовки.

### Подписи интерфейса

Все строки по умолчанию английские; переопределяются через `labels`.

| `GridLabels` | По умолчанию | Где видно |
| --- | --- | --- |
| `search` | `'Search'` | `aria-label` поля поиска |
| `searchPlaceholder` | как `search` + `…` | плейсхолдер |
| `sortDirection` | `'Sort direction'` | `aria-label` контрола направления |
| `descending` / `ascending` | `'↓ desc'` / `'↑ asc'` | варианты `<option>` |
| `rows` | `'rows:'` | префикс счётчика; `''` оставляет только число |

| `TreeLabels` | По умолчанию | Где видно |
| --- | --- | --- |
| `search` / `searchPlaceholder` | `'Search'` / `'Search…'` | поле поиска |
| `matched` | `'matched:'` | префикс счётчика; `''` скрывает его |
| `expandAll` / `collapseAll` | `'Expand all'` / `'Collapse all'` | кнопки при `showExpandAll` |

```tsx
<Grid rows={rows} columns={cols} labels={{ search: 'Поиск', rows: 'строк:', descending: 'убыв', ascending: 'возр' }} />
<Tree root={tree} showExpandAll labels={{ matched: 'найдено:', expandAll: 'Развернуть', collapseAll: 'Свернуть' }} />
```

## Headless-подход и CSS

Компоненты рендерят семантический DOM со стабильными классами:

- `Grid`: `grid`, `toolbar`, `search`, `dir`, `chip`, `arrow`, `group-row`,
  `toggle`, `count`, `empty`;
- `Tree`: `tree`, `toolbar`, `search`, `bulk`, `expand-all`, `collapse-all`,
  `chip`, `node`, `row`, `caret`, `leaf`, `name`, `dir`, `match`, `meta`, `kids`,
  `empty`.

Готовый CSS — [`examples/dataview/style.css`](../../examples/dataview/style.css),
разбор разметки и рецепты — [`docs/TREE_GRID.md`](../../docs/TREE_GRID.md).

## Keyed-режим: «ключ = идентичность»

Если задан `rowKey`, `<For>` переиспользует DOM-узлы: пока ключ в списке, узел
**не перерисовывается**. Значит, изменения данных в существующей строке сами по
себе не появятся на экране. Два рабочих рецепта:

```tsx
// 1) привязка поля через $() — обновляется точечно, узел живёт
{ key: 'title', header: 'Title', sort: r => r.title, cell: r => <b>{$(r, x => x.title)}</b> }

// 2) ключ с отпечатком — узел пересоздаётся только при реальном изменении
rowKey={r => `${r.id}:${r.updated}`}
```

Первое дешевле и сохраняет фокус в `<input>`; второе проще, но теряет состояние
узла при каждой смене данных. Без `rowKey` грид перерисовывает строки целиком —
это корректно, но дороже.

## Разработка

```bash
npm ci              # в корне монорепо
npm test            # 200 тестов (ядро + компоненты)
npm run typecheck
npm run build
npm run bench       # замеры грида и дерева
```

## Лицензия

MIT
