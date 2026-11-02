/**
 * BSO5 — reactive DOM runtime without the bloat. Just TypeScript.
 * (РУС: BSO5 — реактивный DOM-рантайм без лишнего веса. Просто TypeScript.)
 *
 * - `Signal<T>` — atomic reactive primitive (get/set + subscriptions).
 *   (РУС: `Signal<T>` — атомарный реактивный примитив (чтение/запись + подписки).)
 * - `Reactive<T>` — deep reactive proxy with property-path tracking.
 *   (РУС: `Reactive<T>` — глубокий реактивный прокси с трекингом путей к свойствам.)
 * - `effect()`, `watch()`, `$()` — fine-grained binding helpers for UI code.
 *   (РУС: `effect()`, `watch()`, `$()` — хелперы тонких привязок для UI-кода.)
 *
 * @module
 */
/** A callback invoked when a tracked dependency changes. (РУС: Колбэк, вызываемый при изменении отслеживаемой зависимости.) */
export type WatchCallback = () => void;
/** A function of the form `x => x.some.path` used to statically address a property. (РУС: Функция вида `x => x.some.path` для статической адресации свойства.) */
export type PathAccessor<T, R> = (t: T) => R;
/** Marker symbol carried by every value returned from `$()`. (РУС: Символ-маркер, который несёт каждое значение, возвращаемое `$()`.) */
export declare const REACTIVE_VALUE: unique symbol;
/**
 * Extracts the property path from an accessor such as `x => x.user.name` or
 * `x => x.items[0].title` by running it over a Proxy marker instead of parsing
 * the function source. Returns the dotted path ("items.0.title") — array
 * indices become numeric string segments — or `null` when the accessor is not
 * a plain property chain: computed expressions (`x => x.a + 1`) throw on the
 * marker, method calls (`x.items.map(...)`) and async functions are rejected.
 *
 * The accessor is executed once per call to trace the path, so it must be pure
 * and side-effect-free.
 *
 * РУС: Извлекает путь свойства из аксессора вида `x => x.user.name` или
 * `x => x.items[0].title`, прогоняя его над Proxy-маркером вместо разбора
 * исходника функции. Возвращает точечный путь ("items.0.title") — индексы
 * массива становятся числовыми строковыми сегментами — либо `null`, если
 * аксессор не является простой цепочкой свойств: вычисляемые выражения
 * (`x => x.a + 1`) бросают исключение на маркере, вызовы методов
 * (`x.items.map(...)`) и async-функции отвергаются.
 *
 * РУС: Аксессор выполняется один раз при каждом вызове для трассировки пути,
 * поэтому он должен быть чистым и без побочных эффектов.
 */
export declare function getPropertyName(fn: Function): string | null;
/**
 * A single reactive value.
 *
 * - Reading `value` inside `effect()` registers the effect as a dependency.
 * - Writing `value` notifies subscribers synchronously (only on real change,
 *   compared with `Object.is`).
 *
 * РУС: Единичное реактивное значение.
 *
 * РУС: - Чтение `value` внутри `effect()` регистрирует эффект как зависимость.
 * РУС: - Запись `value` синхронно уведомляет подписчиков (только при реальном
 *   изменении, сравнение через `Object.is`).
 */
export declare class Signal<T> {
    private current;
    private readonly listeners;
    constructor(initial: T);
    /** Reads the current value and, inside `effect()`, tracks it. (РУС: Читает текущее значение и, внутри `effect()`, трекает его.) */
    get value(): T;
    /** Writes a new value, notifying listeners when it actually changed. (РУС: Записывает новое значение, уведомляя слушателей, когда оно действительно изменилось.) */
    set value(next: T);
    /** Reads the current value without registering a dependency. (РУС: Читает текущее значение без регистрации зависимости.) */
    peek(): T;
    /**
     * Updates the value from the current one: `count.update(n => n + 1)`.
     * Reads the current value untracked, so it is safe to call inside
     * `effect()` without creating a self-triggering loop.
     *
     * РУС: Обновляет значение от текущего: `count.update(n => n + 1)`.
     * Читает текущее значение без трекинга, поэтому его безопасно вызывать
     * внутри `effect()` без создания само-триггерящегося цикла.
     */
    update(fn: (current: T) => T): void;
    /** Subscribes to value changes. Returns an unsubscription function. (РУС: Подписывается на изменения значения. Возвращает функцию отписки.) */
    subscribe(cb: WatchCallback): () => void;
}
/** Creates a `Signal` without `new`: `signal(0)`. (РУС: Создаёт `Signal` без `new`: `signal(0)`.) */
export declare function signal<T>(initial: T): Signal<T>;
/**
 * An ownership scope: collects stop functions of every `effect()` created
 * while it was current, so `dispose()` tears the whole subtree down at once.
 * `For`, `Show` and `mount()` create scopes per render pass / per view.
 *
 * РУС: Область владения: собирает функции остановки каждого `effect()`,
 * созданного пока она была текущей, чтобы `dispose()` снял всё поддерево
 * разом. `For`, `Show` и `mount()` создают области на проход рендера / на вью.
 */
export interface Scope {
    /** Stop functions of the effects owned by this scope. (РУС: Функции остановки эффектов этой области.) */
    readonly stops: Set<() => void>;
    /** Once disposed, the scope accepts no new effects. (РУС: После dispose область не принимает новых эффектов.) */
    disposed: boolean;
}
/** Creates an empty ownership scope. (РУС: Создаёт пустую область владения.) */
export declare function createScope(): Scope;
/**
 * Stops every effect owned by `scope` and rejects further registration.
 * Idempotent.
 *
 * РУС: Останавливает все эффекты области и запрещает дальнейшую регистрацию.
 * Идемпотентна.
 */
export declare function dispose(scope: Scope): void;
/** Runs `fn` with `scope` as the owner of any effect it creates. (РУС: Выполняет `fn`, назначая `scope` владельцем создаваемых эффектов.) */
export declare function runInScope<T>(scope: Scope, fn: () => T): T;
/**
 * Registers a cleanup for the current scope, called by `dispose()`. Outside a
 * scope the call is a no-op. This is not a per-run `onCleanup`: it fires on
 * scope teardown only.
 *
 * РУС: Регистрирует очистку в текущей области, вызываемую `dispose()`. Вне
 * области вызов ничего не делает. Это не `onCleanup` на каждый перезапуск
 * эффекта — очистка срабатывает только при сносе области.
 */
export declare function onScopeDispose(cleanup: () => void): void;
/** Returns the currently active scope, if any. (РУС: Возвращает текущую активную область, если есть.) */
export declare function getCurrentScope(): Scope | null;
/**
 * Groups writes so dependent effects run once at the end instead of once per
 * write. Signal listeners are batched too and deduplicated by identity.
 *
 * ```ts
 * batch(() => { a.value = 1; b.value = 2; }); // один прогон эффекта, а не два
 * ```
 *
 * РУС: Группирует записи: зависимые эффекты выполняются один раз в конце, а не
 * на каждую запись. Слушатели сигналов тоже батчатся и дедуплицируются.
 */
export declare function batch<T>(fn: () => T): T;
/**
 * Runs `fn` without registering anything it reads as a dependency. Useful
 * inside `effect()` when a value must be read but must not retrigger it.
 *
 * РУС: Выполняет `fn`, не регистрируя прочитанное как зависимость. Полезно
 * внутри `effect()`, когда значение нужно прочитать, но не хочется
 * перезапускаться от него.
 */
export declare function untrack<T>(fn: () => T): T;
/**
 * Derives a value from reactive sources: recomputes when a dependency changes
 * and notifies readers only when the result differs (`Object.is`). Returns a
 * `Signal`, so it can be used anywhere a signal is expected — `$()`, `<For>`,
 * `each`, plain reads inside `effect()`.
 *
 * Recomputation is **eager** (on dependency change, not on read): there is no
 * lazy cache, which keeps the dependency graph simple and ordering obvious.
 * Inside a scope (`mount()`, `<For>`, `<Show>`) the underlying effect is owned
 * by that scope and stops with it.
 *
 * ```ts
 * const count = signal(2);
 * const doubled = computed(() => count.value * 2);
 * effect(() => console.log(doubled.value)); // 4, затем 6 — но не дважды
 * count.value = 3;
 * ```
 *
 * РУС: Выводит значение из реактивных источников: пересчитывается при
 * изменении зависимости и уведомляет читателей только если результат реально
 * изменился (`Object.is`). Возвращает `Signal`, поэтому подходит везде, где
 * ждут сигнал — `$()`, `<For>`, `each`, обычное чтение в `effect()`.
 *
 * Пересчёт **энергичный** (на изменение зависимости, не на чтение): ленивого
 * кеша нет, зато граф зависимостей простой и порядок очевиден. Внутри области
 * (`mount()`, `<For>`, `<Show>`) эффект принадлежит ей и останавливается вместе с ней.
 */
export declare function computed<T>(fn: () => T): Signal<T>;
/**
 * Replaces the default `console.error` sink for errors thrown inside
 * `effect()`. Pass `null` to restore the default. Per-effect `onError`
 * (second argument of `effect()`) wins over this handler.
 *
 * РУС: Заменяет `console.error` как приёмник ошибок из `effect()`. Передайте
 * `null`, чтобы вернуть поведение по умолчанию. `onError` конкретного эффекта
 * (второй аргумент `effect()`) важнее этого обработчика.
 */
export declare function setEffectErrorHandler(handler: ((error: unknown) => void) | null): void;
/** Options of {@link effect}. (РУС: Опции {@link effect}.) */
export interface EffectOptions {
    /** Receives exceptions thrown by the effect body instead of `console.error`. (РУС: Принимает исключения тела эффекта вместо `console.error`.) */
    onError?: (error: unknown) => void;
}
/**
 * Runs `fn` immediately and re-runs it whenever any `Signal` it read — or any
 * property it read through a `Reactive` proxy — changes.
 * Returns a stop function that detaches the effect permanently.
 *
 * РУС: Выполняет `fn` немедленно и перезапускает при изменении любого
 * прочитанного `Signal` — или любого свойства, прочитанного через прокси
 * `Reactive`. Возвращает функцию остановки, навсегда отсоединяющую эффект.
 */
export declare function effect(fn: () => void, options?: EffectOptions): () => void;
/**
 * Deep reactive wrapper around a plain object.
 *
 * - `.value` returns a Proxy tree; nested objects are wrapped lazily on read.
 * - Writes through the proxy notify path subscribers:
 *   `watch(x => x.user.name, cb)` fires on `x.user.name = '…'` **and** on
 *   `x.user = { … }` (nested paths re-bind to the new nested object).
 * - Arrays and class instances are supported; DOM Nodes and Dates pass through.
 *
 * РУС: Глубокая реактивная обёртка над обычным объектом.
 *
 * РУС: - `.value` возвращает дерево Proxy; вложенные объекты оборачиваются
 *   лениво при чтении.
 * РУС: - Записи через прокси уведомляют подписчиков путей:
 *   `watch(x => x.user.name, cb)` срабатывает на `x.user.name = '…'` **и** на
 *   `x.user = { … }` (вложенные пути перепривязываются к новому вложенному объекту).
 * РУС: - Поддерживаются массивы и инстансы классов; DOM-узлы и Date проходят насквозь.
 */
export declare class Reactive<T extends object> {
    private readonly proxy;
    private readonly raw;
    constructor(raw: T);
    /** The reactive (proxied) view of the target. (РУС: Реактивное (проксированное) представление цели.) */
    get value(): T;
    /** The underlying raw object, untouched by reactivity. (РУС: лежащий в основе сырой объект, не затронутый реактивностью.) */
    get target(): T;
    /**
     * Subscribes `cb` to changes of the property addressed by `path`
     * (an accessor like `x => x.user.name`, or a `'user.name'` string).
     * Returns an unsubscription function.
     *
     * РУС: Подписывает `cb` на изменения свойства, адресуемого `path`
     * (аксессором вида `x => x.user.name` или строкой `'user.name'`).
     * Возвращает функцию отписки.
     */
    watch(path: PathAccessor<T, any> | string, cb: WatchCallback): () => void;
    /** Subscriptions: raw owner object -> leaf property -> callbacks. (РУС: Подписки: сырой объект-владелец -> конечное свойство -> колбэки.) */
    private subs;
    /** Nested-path subscriptions: full path -> callbacks + current owner. (РУС: Подписки на вложенные пути: полный путь -> колбэки + текущий владелец.) */
    private readonly pathSubs;
    /** Set by `dispose()`; makes the proxy inert for reactivity. (РУС: Устанавливается `dispose()`; делает прокси инертным для реактивности.) */
    private disposed;
    private subscribe;
    private unsubscribe;
    /** Resolves the raw object owning the last segment of `segments`. (РУС: Резолвит сырой объект, владеющий последним сегментом `segments`.) */
    private resolveOwner;
    /** Wraps `obj` in a reactive proxy (non-objects pass through as-is). */
    private wrap;
    /** Per-instance proxy cache: raw object -> its proxy. */
    private readonly proxyCache;
    private readonly proxyHandler;
    /**
     * Notifies subscribers for `prop` on raw `owner`:
     * - callbacks watching exactly `prop` on that object;
     * - nested-path subscribers whose path owner changed (an ancestor was
     *   replaced): they are notified and re-bound to the new owner.
     *
     * РУС: Уведомляет подписчиков `prop` на сыром `owner`:
     * РУС: - колбэки, следящие ровно за `prop` на этом объекте;
     * РУС: - подписчиков вложенных путей, у которых сменился владелец пути
     *   (предок был заменён): они уведомляются и перепривязываются к новому владельцу.
     */
    private notify;
    /**
     * Stops every subscription and notification: watchers, `$()` DOM bindings
     * and effects that read through this model stop updating. Reads and writes
     * through the proxy keep working — they just stop being reactive.
     *
     * РУС: Останавливает все подписки и уведомления: вотчеры, `$()`-привязки DOM
     * и эффекты, читающие через эту модель, перестают обновляться. Чтения и
     * записи через прокси продолжают работать — просто перестают быть реактивными.
     */
    dispose(): void;
}
/** The shape returned by `$()`. (РУС: Форма значения, возвращаемого `$()`.) */
export interface BoundValue<T = unknown> {
    readonly [REACTIVE_VALUE]: true;
    /** Current value of the bound source. (РУС: Текущее значение источника привязки.) */
    readonly value: T;
    subscribe(cb: WatchCallback): () => void;
}
/** Type guard for values created by `$()`. (РУС: Тайп-гард для значений, созданных `$()`.) */
export declare function isBoundValue(v: unknown): v is BoundValue;
/**
 * Creates a bound reactive value usable as a JSX child, attribute or style
 * property. Accepts either a `Signal` or an object (raw root or any nested
 * proxy) wrapped by `Reactive`:
 *
 * ```tsx
 * <p>Count: {$(count, x => x.deep.value)}</p>
 * <input value={$(state, x => x.name)} />
 * ```
 *
 * The bound value updates automatically after writes to the source.
 *
 * РУС: Создаёт привязанное реактивное значение, пригодное как ребёнок JSX,
 * атрибут или свойство style. Принимает либо `Signal`, либо объект (сырой
 * корень или любой вложенный прокси), обёрнутый `Reactive`:
 *
 * РУС: Привязанное значение обновляется автоматически после записей в источник.
 */
export declare function $<T>(source: Signal<T>): BoundValue<T>;
export declare function $<T extends object, R>(source: T, path: (t: T) => R): BoundValue<R>;
/**
 * Free `watch()`: subscribes to a `Signal` or to a path of a `Reactive` object
 * (root or any nested proxy). Returns an unsubscription function.
 *
 * РУС: Свободный `watch()`: подписывается на `Signal` или путь объекта
 * `Reactive` (корня или любого вложенного прокси). Возвращает функцию отписки.
 */
export declare function watch(source: Signal<unknown> | object, path: string | ((t: any) => any), cb: WatchCallback): () => void;
//# sourceMappingURL=reactive.d.ts.map