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
/** Marker symbol carried by every value returned from `$()`. (РУС: Символ-маркер, который несёт каждое значение, возвращаемое `$()`.) */
export const REACTIVE_VALUE = Symbol('bso5.reactiveValue');
/** Maps any proxy produced by a `Reactive` back to that instance. (РУС: Отображает любой прокси, созданный `Reactive`, обратно в этот инстанс.) */
const proxyToReactor = new WeakMap();
/**
 * Maps any proxy produced by any `Reactive` (root or nested) back to the raw
 * object it wraps. Global, so writes can unwrap proxies owned by another
 * `Reactive` instance instead of storing the proxy itself.
 *
 * РУС: Отображает любой прокси, созданный любым `Reactive` (корневым или
 * вложенным), обратно в сырой объект, который он оборачивает. Глобальный,
 * чтобы записи могли разворачивать прокси, принадлежащие другому инстансу
 * `Reactive`, вместо хранения самого прокси.
 */
const proxyToRaw = new WeakMap();
/**
 * Maps a raw object to the `Reactive` instance that owns it. Exactly one
 * Reactive may wrap a given raw object.
 *
 * РУС: Отображает сырой объект в инстанс `Reactive`, который им владеет.
 * Данный сырой объект может быть обёрнут ровно одним Reactive.
 */
const reactorRegistry = new WeakMap();
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
export function getPropertyName(fn) {
    // Async accessors read `.then` during promise assimilation and settle in a
    // microtask — reject up-front (the old regex-based parser rejected them too).
    // РУС: Async-аксессоры читают `.then` при ассимиляции промиса и завершаются
    // в микротаске — отвергаем сразу (старый regex-парсер тоже их отвергал).
    if (Object.prototype.toString.call(fn) === '[object AsyncFunction]')
        return null;
    const segments = [];
    let touched = false;
    let applied = false;
    const marker = new Proxy(function () { }, {
        get(_t, prop) {
            // toPrimitive and friends: not a path segment.
            // РУС: toPrimitive и прочие — не сегменты пути.
            if (typeof prop === 'symbol')
                return marker;
            touched = true;
            // array indices land here as '0', '1', ...
            // РУС: индексы массива попадают сюда как '0', '1', ...
            segments.push(String(prop));
            return marker;
        },
        apply() { applied = true; return marker; },
        has() { return true; },
    });
    try {
        fn(marker);
    }
    catch {
        // arithmetic over the marker (`x => x.a + 1`) throws
        // РУС: арифметика над маркером (`x => x.a + 1`) бросает исключение
        return null;
    }
    // something was called over the marker: not a plain chain
    // РУС: по маркеру что-то вызвали — это не простая цепочка
    if (applied)
        return null;
    return touched ? segments.join('.') : null;
}
/** Splits a dot-separated path into its segments. (РУС: Разбивает точечный путь на сегменты.) */
function splitPath(path) {
    return path.split('.');
}
// ─────────────────────────────────────────────────────────────────────────────
// Signal: atomic reactive primitive
// (РУС: Signal — атомарный реактивный примитив)
// ─────────────────────────────────────────────────────────────────────────────
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
export class Signal {
    constructor(initial) {
        this.listeners = new Set();
        this.current = initial;
    }
    /** Reads the current value and, inside `effect()`, tracks it. (РУС: Читает текущее значение и, внутри `effect()`, трекает его.) */
    get value() {
        trackSignal(this);
        return this.current;
    }
    /** Writes a new value, notifying listeners when it actually changed. (РУС: Записывает новое значение, уведомляя слушателей, когда оно действительно изменилось.) */
    set value(next) {
        if (Object.is(this.current, next))
            return;
        this.current = next;
        for (const cb of [...this.listeners])
            scheduleCallback(cb);
        notifyEffects(this);
    }
    /** Reads the current value without registering a dependency. (РУС: Читает текущее значение без регистрации зависимости.) */
    peek() {
        return this.current;
    }
    /**
     * Updates the value from the current one: `count.update(n => n + 1)`.
     * Reads the current value untracked, so it is safe to call inside
     * `effect()` without creating a self-triggering loop.
     *
     * РУС: Обновляет значение от текущего: `count.update(n => n + 1)`.
     * Читает текущее значение без трекинга, поэтому его безопасно вызывать
     * внутри `effect()` без создания само-триггерящегося цикла.
     */
    update(fn) {
        this.value = fn(this.current);
    }
    /** Subscribes to value changes. Returns an unsubscription function. (РУС: Подписывается на изменения значения. Возвращает функцию отписки.) */
    subscribe(cb) {
        this.listeners.add(cb);
        return () => this.listeners.delete(cb);
    }
}
/** Creates a `Signal` without `new`: `signal(0)`. (РУС: Создаёт `Signal` без `new`: `signal(0)`.) */
export function signal(initial) {
    return new Signal(initial);
}
/** The scope that owns effects created right now, if any. (РУС: Область, владеющая создаваемыми сейчас эффектами, если есть.) */
let currentScope = null;
/** Creates an empty ownership scope. (РУС: Создаёт пустую область владения.) */
export function createScope() {
    return { stops: new Set(), disposed: false };
}
/**
 * Stops every effect owned by `scope` and rejects further registration.
 * Idempotent.
 *
 * РУС: Останавливает все эффекты области и запрещает дальнейшую регистрацию.
 * Идемпотентна.
 */
export function dispose(scope) {
    if (scope.disposed)
        return;
    scope.disposed = true;
    for (const stop of [...scope.stops])
        stop();
    scope.stops.clear();
}
/** Runs `fn` with `scope` as the owner of any effect it creates. (РУС: Выполняет `fn`, назначая `scope` владельцем создаваемых эффектов.) */
export function runInScope(scope, fn) {
    const prev = currentScope;
    currentScope = scope;
    try {
        return fn();
    }
    finally {
        currentScope = prev;
    }
}
/**
 * Registers a cleanup for the current scope, called by `dispose()`. Outside a
 * scope the call is a no-op. This is not a per-run `onCleanup`: it fires on
 * scope teardown only.
 *
 * РУС: Регистрирует очистку в текущей области, вызываемую `dispose()`. Вне
 * области вызов ничего не делает. Это не `onCleanup` на каждый перезапуск
 * эффекта — очистка срабатывает только при сносе области.
 */
export function onScopeDispose(cleanup) {
    const scope = currentScope;
    if (!scope || scope.disposed)
        return;
    scope.stops.add(cleanup);
}
/** Returns the currently active scope, if any. (РУС: Возвращает текущую активную область, если есть.) */
export function getCurrentScope() {
    return currentScope;
}
// ─────────────────────────────────────────────────────────────────────────────
// batch() / untrack(): control over when effects run and what they track
// (РУС: batch() / untrack() — контроль над моментом прогона эффектов и трекингом)
// ─────────────────────────────────────────────────────────────────────────────
/** Depth of nested `batch()` calls; jobs accumulate while it is > 0. (РУС: Глубина вложенных `batch()`; пока > 0, задачи накапливаются.) */
let batchDepth = 0;
/** Queued signal listeners and effects waiting for the batch to end. (РУС: Отложенные слушатели сигналов и эффекты, ждущие конца батча.) */
const pendingCallbacks = new Set();
const pendingEffects = new Set();
/** Runs `job` now, or defers it to the end of the current batch. (РУС: Выполняет `job` сразу либо откладывает до конца текущего батча.) */
function scheduleCallback(job) {
    if (batchDepth === 0)
        job();
    else
        pendingCallbacks.add(job);
}
/** Drains the queue; effects may enqueue more work, so loop until stable. (РУС: Разбирает очередь; эффекты могут добавить работу — крутим до стабилизации.) */
function flushBatch() {
    let guard = 0;
    while ((pendingCallbacks.size > 0 || pendingEffects.size > 0) && guard++ < 1000) {
        const callbacks = [...pendingCallbacks];
        pendingCallbacks.clear();
        for (const cb of callbacks)
            cb();
        const records = [...pendingEffects];
        pendingEffects.clear();
        for (const rec of records)
            runEffect(rec);
    }
}
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
export function batch(fn) {
    batchDepth++;
    try {
        return fn();
    }
    finally {
        batchDepth--;
        if (batchDepth === 0)
            flushBatch();
    }
}
/**
 * Runs `fn` without registering anything it reads as a dependency. Useful
 * inside `effect()` when a value must be read but must not retrigger it.
 *
 * РУС: Выполняет `fn`, не регистрируя прочитанное как зависимость. Полезно
 * внутри `effect()`, когда значение нужно прочитать, но не хочется
 * перезапускаться от него.
 */
export function untrack(fn) {
    const prev = runningEffect;
    runningEffect = null;
    try {
        return fn();
    }
    finally {
        runningEffect = prev;
    }
}
// ─────────────────────────────────────────────────────────────────────────────
// computed(): derived value that only notifies when it actually changed
// (РУС: computed() — производное значение, уведомляющее только при реальном изменении)
// ─────────────────────────────────────────────────────────────────────────────
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
export function computed(fn) {
    const out = signal(undefined);
    effect(() => {
        // Writing an equal value is a no-op (Signal compares with Object.is),
        // so downstream effects do not re-run on unrelated recomputations.
        // РУС: Запись равного значения ничего не делает (Signal сравнивает через
        // Object.is), поэтому нижестоящие эффекты не перезапускаются зря.
        out.value = fn();
    });
    return out;
}
/** Global fallback for effect errors; `null` means "log to console". (РУС: Глобальный обработчик ошибок эффектов; `null` — писать в console.) */
let effectErrorHandler = null;
/**
 * Replaces the default `console.error` sink for errors thrown inside
 * `effect()`. Pass `null` to restore the default. Per-effect `onError`
 * (second argument of `effect()`) wins over this handler.
 *
 * РУС: Заменяет `console.error` как приёмник ошибок из `effect()`. Передайте
 * `null`, чтобы вернуть поведение по умолчанию. `onError` конкретного эффекта
 * (второй аргумент `effect()`) важнее этого обработчика.
 */
export function setEffectErrorHandler(handler) {
    effectErrorHandler = handler;
}
/** Currently running effect, if any. (РУС: Выполняющийся в данный момент эффект, если есть.) */
let runningEffect = null;
/** Signals each effect depends on (inverse index for fast unsubscribe). (РУС: Сигналы, от которых зависит каждый эффект (обратный индекс для быстрой отписки).) */
const signalDeps = new WeakMap();
/** Reactive property reads by effect: raw owner -> prop -> effects. (РУС: Реактивные чтения свойств по эффектам: сырой владелец -> свойство -> эффекты.) */
const reactiveDeps = new WeakMap();
/** Notifies all effects that depend on `sig`. (РУС: Уведомляет все эффекты, зависящие от `sig`.) */
function notifyEffects(sig) {
    const records = signalDeps.get(sig);
    if (!records)
        return;
    for (const rec of [...records])
        scheduleEffect(rec);
}
/** Notifies all effects that read `owner.prop` through a Reactive proxy. (РУС: Уведомляет все эффекты, читавшие `owner.prop` через прокси Reactive.) */
function notifyReactiveEffects(owner, prop) {
    const records = reactiveDeps.get(owner)?.get(prop);
    if (!records)
        return;
    for (const rec of [...records])
        scheduleEffect(rec);
}
/** Runs the effect now, or defers it to the end of the current batch. (РУС: Запускает эффект сразу либо откладывает до конца текущего батча.) */
function scheduleEffect(rec) {
    if (batchDepth === 0)
        runEffect(rec);
    else
        pendingEffects.add(rec);
}
/** Registers `sig` as a dependency of the running effect. (РУС: Регистрирует `sig` как зависимость выполняющегося эффекта.) */
function trackSignal(sig) {
    if (!runningEffect)
        return;
    runningEffect.deps.add(sig);
    let records = signalDeps.get(sig);
    if (!records)
        signalDeps.set(sig, (records = new Set()));
    records.add(runningEffect);
}
/** Registers a reactive object property as a dependency of the running effect. (РУС: Регистрирует свойство реактивного объекта как зависимость выполняющегося эффекта.) */
function trackReactiveProp(owner, prop) {
    if (!runningEffect)
        return;
    let props = runningEffect.reactiveDeps.get(owner);
    if (!props)
        runningEffect.reactiveDeps.set(owner, (props = new Set()));
    props.add(prop);
    let byProp = reactiveDeps.get(owner);
    if (!byProp)
        reactiveDeps.set(owner, (byProp = new Map()));
    let records = byProp.get(prop);
    if (!records)
        byProp.set(prop, (records = new Set()));
    records.add(runningEffect);
}
function runEffect(rec) {
    if (!rec.active || rec.running)
        return;
    // Drop previous dependencies so unused ones stop re-triggering the effect.
    // РУС: Сбрасываем прежние зависимости, чтобы неиспользуемые перестали
    // перезапускать эффект.
    detachDeps(rec);
    const prev = runningEffect;
    runningEffect = rec;
    rec.running = true;
    try {
        rec.fn();
    }
    catch (err) {
        // Effects are background computations: a throw inside must not propagate
        // into the code that wrote the signal. Surface it, keep the app alive.
        // The per-effect `onError` wins; then the global handler; then console.
        // РУС: Эффекты — фоновые вычисления: исключение внутри не должно попадать
        // в код, записавший сигнал. Показываем его, приложение продолжает жить.
        // Обработчик конкретного эффекта важнее глобального, глобальный — важнее console.
        const handler = rec.onError ?? effectErrorHandler;
        if (handler) {
            try {
                handler(err);
            }
            catch (handlerErr) {
                // A broken error handler must not take down the reactive graph.
                // РУС: Сломанный обработчик ошибок не должен ронять реактивный граф.
                console.error('bso5: error handler threw', handlerErr);
            }
        }
        else {
            console.error('bso5: unhandled error in effect()', err);
        }
    }
    finally {
        rec.running = false;
        runningEffect = prev;
    }
}
/** Detaches every tracked dependency of `rec` (before a re-run or on stop). (РУС: Отсоединяет все отслеженные зависимости `rec` (перед перезапуском или при остановке).) */
function detachDeps(rec) {
    for (const sig of rec.deps)
        signalDeps.get(sig)?.delete(rec);
    rec.deps.clear();
    for (const [owner, props] of rec.reactiveDeps) {
        const byProp = reactiveDeps.get(owner);
        if (!byProp)
            continue;
        for (const prop of props)
            byProp.get(prop)?.delete(rec);
    }
    rec.reactiveDeps.clear();
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
export function effect(fn, options) {
    const rec = {
        fn,
        deps: new Set(),
        reactiveDeps: new Map(),
        active: true,
        running: false,
        onError: options?.onError,
    };
    const stop = () => {
        rec.active = false;
        detachDeps(rec);
    };
    // An effect created during a scoped render is owned by that scope, so
    // disposing the view stops it without any manual bookkeeping.
    // РУС: Эффект, созданный во время рендера внутри области, принадлежит этой
    // области: снос вью останавливает его без ручного учёта.
    const scope = currentScope;
    if (scope && !scope.disposed)
        scope.stops.add(stop);
    runEffect(rec);
    return stop;
}
// ─────────────────────────────────────────────────────────────────────────────
// Reactive<T>: deep reactive proxy with property-path subscriptions
// (РУС: Reactive<T> — глубокий реактивный прокси с подписками на пути свойств)
// ─────────────────────────────────────────────────────────────────────────────
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
export class Reactive {
    constructor(raw) {
        /** Subscriptions: raw owner object -> leaf property -> callbacks. (РУС: Подписки: сырой объект-владелец -> конечное свойство -> колбэки.) */
        this.subs = new WeakMap();
        /** Nested-path subscriptions: full path -> callbacks + current owner. (РУС: Подписки на вложенные пути: полный путь -> колбэки + текущий владелец.) */
        this.pathSubs = new Map();
        /** Set by `dispose()`; makes the proxy inert for reactivity. (РУС: Устанавливается `dispose()`; делает прокси инертным для реактивности.) */
        this.disposed = false;
        /** Per-instance proxy cache: raw object -> its proxy. */
        this.proxyCache = new WeakMap();
        this.proxyHandler = {
            get: (target, prop, receiver) => {
                const value = Reflect.get(target, prop, receiver);
                // Track property reads made by a running effect (until disposed).
                // Only string keys: symbols are read by built-ins (iteration, coercion),
                // not by a user-facing property path, so tracking them is pure noise.
                // РУС: Трекаем чтения свойств выполняющимся эффектом (пока не disposed).
                // Только строковые ключи: символы читают встроенные механизмы, а не путь
                // пользователя, — трекать их значит копить мусорные зависимости.
                if (!this.disposed && typeof prop === 'string')
                    trackReactiveProp(target, prop);
                // Leave DOM nodes and exotic objects untouched for speed/safety.
                // РУС: DOM-узлы и экзотические объекты оставляем нетронутыми ради скорости/безопасности.
                if (value !== null && typeof value === 'object' && shouldProxy(value)) {
                    return this.wrap(value);
                }
                return value;
            },
            set: (target, prop, value, receiver) => {
                const oldValue = Reflect.get(target, prop, receiver);
                // Unwrap any reactive proxy (from this or another Reactive instance)
                // back to its raw target before storing.
                // РУС: Разворачиваем любой реактивный прокси (этого или другого инстанса
                // Reactive) обратно в сырую цель перед сохранением.
                const rawValue = proxyToRaw.get(value) ?? value;
                // Arrays auto-update `length` inside their index [[DefineOwnProperty]],
                // so capture it before the write to detect a silent change.
                // РУС: Массивы автообновляют `length` внутри своего индексного
                // [[DefineOwnProperty]], поэтому фиксируем её до записи, чтобы заметить
                // скрытое изменение.
                const isArray = Array.isArray(target);
                const oldLength = isArray ? target.length : undefined;
                // Always write to the raw target (passing the proxy as receiver would
                // re-route data-property writes through the proxy, breaking array
                // built-ins such as `push`, which update `length` internally).
                // РУС: Всегда пишем в сырую цель (передача прокси как receiver
                // перенаправила бы записи свойств-данных через прокси, ломая встроенные
                // методы массивов вроде `push`, которые обновляют `length` внутренне).
                const result = Reflect.set(target, prop, rawValue);
                if (result) {
                    if (!Object.is(oldValue, rawValue))
                        this.notify(target, String(prop));
                    if (isArray && prop !== 'length' && target.length !== oldLength)
                        this.notify(target, 'length');
                }
                return result;
            },
            defineProperty: (target, prop, descriptor) => {
                const had = Reflect.has(target, prop);
                const oldValue = Reflect.get(target, prop);
                const result = Reflect.defineProperty(target, prop, descriptor);
                if (result && (!had || !Object.is(oldValue, descriptor.value))) {
                    this.notify(target, String(prop));
                }
                return result;
            },
            deleteProperty: (target, prop) => {
                const had = Reflect.has(target, prop);
                const result = Reflect.deleteProperty(target, prop);
                if (result && had)
                    this.notify(target, String(prop));
                return result;
            },
        };
        if (raw === null || typeof raw !== 'object') {
            throw new TypeError('bso5: Reactive requires an object target');
        }
        if (reactorRegistry.has(raw)) {
            throw new Error('bso5: this object is already wrapped in a Reactive');
        }
        this.raw = raw;
        reactorRegistry.set(raw, this);
        this.proxy = this.wrap(raw);
    }
    /** The reactive (proxied) view of the target. (РУС: Реактивное (проксированное) представление цели.) */
    get value() {
        return this.proxy;
    }
    /** The underlying raw object, untouched by reactivity. (РУС: лежащий в основе сырой объект, не затронутый реактивностью.) */
    get target() {
        return this.raw;
    }
    /**
     * Subscribes `cb` to changes of the property addressed by `path`
     * (an accessor like `x => x.user.name`, or a `'user.name'` string).
     * Returns an unsubscription function.
     *
     * РУС: Подписывает `cb` на изменения свойства, адресуемого `path`
     * (аксессором вида `x => x.user.name` или строкой `'user.name'`).
     * Возвращает функцию отписки.
     */
    watch(path, cb) {
        const pathStr = typeof path === 'string' ? path : getPropertyName(path);
        if (!pathStr) {
            throw new Error('bso5: watch() requires a plain property path (e.g. x => x.user.name)');
        }
        const segments = splitPath(pathStr);
        const owner = this.resolveOwner(this.raw, segments);
        if (owner === null || owner === undefined || typeof owner !== 'object') {
            throw new Error(`bso5: cannot resolve path "${pathStr}"`);
        }
        const leaf = segments[segments.length - 1];
        this.subscribe(owner, leaf, cb);
        if (segments.length > 1) {
            // Register the nested path so replacing an intermediate object
            // (`model.user = {...}`) can find, notify and re-bind this subscription.
            // РУС: Регистрируем вложенный путь, чтобы замена промежуточного объекта
            // (`model.user = {...}`) могла найти, уведомить и перепривязать эту подписку.
            let entry = this.pathSubs.get(pathStr);
            if (!entry)
                this.pathSubs.set(pathStr, (entry = { callbacks: new Set(), owner, segments }));
            entry.callbacks.add(cb);
        }
        return () => {
            // Detach from the owner the subscription was created with…
            // РУС: Отсоединяемся от владельца, с которым была создана подписка…
            this.unsubscribe(owner, leaf, cb);
            // …and from the current one, if an intermediate object was replaced.
            // РУС: …и от текущего, если промежуточный объект был заменён.
            const entry = this.pathSubs.get(pathStr);
            if (entry) {
                if (entry.owner !== undefined && entry.owner !== owner) {
                    this.unsubscribe(entry.owner, leaf, cb);
                }
                entry.callbacks.delete(cb);
                if (entry.callbacks.size === 0)
                    this.pathSubs.delete(pathStr);
            }
        };
    }
    subscribe(owner, leaf, cb) {
        let byLeaf = this.subs.get(owner);
        if (!byLeaf)
            this.subs.set(owner, (byLeaf = new Map()));
        let set = byLeaf.get(leaf);
        if (!set)
            byLeaf.set(leaf, (set = new Set()));
        set.add(cb);
    }
    unsubscribe(owner, leaf, cb) {
        this.subs.get(owner)?.get(leaf)?.delete(cb);
    }
    /** Resolves the raw object owning the last segment of `segments`. (РУС: Резолвит сырой объект, владеющий последним сегментом `segments`.) */
    resolveOwner(root, segments) {
        let current = root;
        for (let i = 0; i < segments.length - 1; i++) {
            if (current === null || current === undefined)
                return undefined;
            current = current[segments[i]];
        }
        return current;
    }
    /** Wraps `obj` in a reactive proxy (non-objects pass through as-is). */
    wrap(obj) {
        if (obj === null || typeof obj !== 'object')
            return obj;
        const cached = this.proxyCache.get(obj);
        if (cached)
            return cached;
        const proxy = new Proxy(obj, this.proxyHandler);
        this.proxyCache.set(obj, proxy);
        proxyToRaw.set(proxy, obj);
        proxyToReactor.set(proxy, this);
        return proxy;
    }
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
    notify(owner, prop) {
        if (this.disposed)
            return;
        // 1) Direct subscribers of this leaf property.
        // РУС: 1) Прямые подписчики этого конечного свойства.
        const direct = this.subs.get(owner)?.get(prop);
        if (direct)
            for (const cb of [...direct])
                cb();
        // 2) Effects that read this property through the proxy.
        // РУС: 2) Эффекты, читавшие это свойство через прокси.
        notifyReactiveEffects(owner, prop);
        // 3) Nested subscribers after an ancestor object was replaced. Only
        //    paths containing `prop` can have changed owner, so skip the rest.
        // РУС: 3) Вложенные подписчики после замены объекта-предка. Сменить
        //    владельца могли только пути, содержащие `prop`, — остальные пропускаем.
        for (const entry of [...this.pathSubs.values()]) {
            if (!entry.segments.includes(prop))
                continue;
            const newOwner = this.resolveOwner(this.raw, entry.segments);
            if (Object.is(newOwner, entry.owner))
                continue;
            // Detach callbacks from the previous owner, then re-bind.
            // РУС: Отсоединяем колбэки от прежнего владельца, затем перепривязываем.
            const leaf = entry.segments[entry.segments.length - 1];
            if (entry.owner !== undefined) {
                for (const cb of entry.callbacks)
                    this.unsubscribe(entry.owner, leaf, cb);
            }
            entry.owner = newOwner !== null && typeof newOwner === 'object' ? newOwner : undefined;
            if (entry.owner !== undefined) {
                for (const cb of entry.callbacks)
                    this.subscribe(entry.owner, leaf, cb);
            }
            for (const cb of [...entry.callbacks])
                cb();
        }
    }
    /**
     * Stops every subscription and notification: watchers, `$()` DOM bindings
     * and effects that read through this model stop updating. Reads and writes
     * through the proxy keep working — they just stop being reactive.
     *
     * РУС: Останавливает все подписки и уведомления: вотчеры, `$()`-привязки DOM
     * и эффекты, читающие через эту модель, перестают обновляться. Чтения и
     * записи через прокси продолжают работать — просто перестают быть реактивными.
     */
    dispose() {
        this.disposed = true;
        this.subs = new WeakMap();
        this.pathSubs.clear();
    }
}
/** Decides whether a nested value should itself become reactive. (РУС: Решает, должно ли вложенное значение само стать реактивным.) */
function shouldProxy(value) {
    // DOM-узлы: прокси ломает их внутренние слоты.
    // РУС: DOM-узлы — прокси ломает их внутренние слоты.
    if (typeof Node !== 'undefined' && value instanceof Node)
        return false;
    if (value instanceof Date || value instanceof RegExp)
        return false;
    // Встроенные объекты с внутренними слотами: метод, вызванный через прокси,
    // получает прокси как receiver и бросает TypeError
    // («called on incompatible receiver»). Оборачивать их нельзя.
    // РУС: встроенные объекты с внутренними слотами — метод через прокси
    // получает прокси как receiver и бросает TypeError.
    if (value instanceof Map || value instanceof Set)
        return false;
    if (value instanceof WeakMap || value instanceof WeakSet)
        return false;
    if (value instanceof Promise || value instanceof Error)
        return false;
    if (value instanceof ArrayBuffer || ArrayBuffer.isView(value))
        return false;
    if (typeof Blob !== 'undefined' && value instanceof Blob)
        return false;
    if (typeof AbortController !== 'undefined' && value instanceof AbortController)
        return false;
    if (typeof AbortSignal !== 'undefined' && value instanceof AbortSignal)
        return false;
    if (typeof FormData !== 'undefined' && value instanceof FormData)
        return false;
    if (typeof URL !== 'undefined' && (value instanceof URL || value instanceof URLSearchParams))
        return false;
    return true;
}
/** Type guard for values created by `$()`. (РУС: Тайп-гард для значений, созданных `$()`.) */
export function isBoundValue(v) {
    return typeof v === 'object' && v !== null && v[REACTIVE_VALUE] === true;
}
export function $(obj, path) {
    if (obj instanceof Signal) {
        const sig = obj;
        return {
            [REACTIVE_VALUE]: true,
            get value() { return sig.value; },
            subscribe: (cb) => sig.subscribe(cb),
        };
    }
    if (typeof path !== 'function') {
        throw new TypeError('bso5: $() requires a path accessor (e.g. x => x.user.name)');
    }
    const reactor = reactorOf(obj);
    if (!reactor) {
        // Plain object without reactivity: resolve once, never update.
        // РУС: Обычный объект без реактивности: резолвим один раз, не обновляем.
        return {
            [REACTIVE_VALUE]: true,
            get value() { return path(obj); },
            subscribe: () => () => { },
        };
    }
    const pathStr = getPropertyName(path);
    if (!pathStr) {
        throw new Error('bso5: $() requires a plain property path (e.g. x => x.user.name)');
    }
    // The root has a real path from the tree root, so the subscription can also
    // survive replacement of an intermediate object (`model.user = {...}`).
    // A nested proxy has no root path, so it binds to that object: later writes to
    // its fields are seen, while replacing its slot in the parent is not — bind
    // from the root (`$(model.value, x => x.rows[0].title)`) when that matters.
    // РУС: У корня есть настоящий путь от корня дерева, поэтому подписка переживает
    // и замену промежуточного объекта (`model.user = {…}`). У вложенного прокси
    // пути от корня нет, поэтому он привязывается к самому объекту: записи в его
    // поля видны, а замена его слота в родителе — нет (для этого привязывайтесь
    // от корня: `$(model.value, x => x.rows[0].title)`).
    const isRoot = obj === reactor.target || obj === reactor.value;
    return {
        [REACTIVE_VALUE]: true,
        get value() { return path(obj); },
        subscribe: (cb) => isRoot
            ? reactor.watch(pathStr, cb)
            : subscribeToAccessor(obj, path, cb),
    };
}
/** Returns the Reactive that produced `obj`, if any. (РУС: Возвращает Reactive, породивший `obj`, если есть.) */
function reactorOf(obj) {
    if (obj instanceof Signal)
        return undefined;
    const direct = proxyToReactor.get(obj);
    if (direct)
        return direct;
    // `obj` may be the raw root registered in the constructor.
    // РУС: `obj` может быть сырым корнем, зарегистрированным в конструкторе.
    return reactorRegistry.get(obj);
}
/**
 * Subscribes `cb` to `path(obj)`, tracking the property chain **through the
 * given proxy**. Unlike `Reactive.watch`, which resolves paths from the root,
 * this works for the root object and for any nested proxy alike.
 *
 * РУС: Подписывает `cb` на `path(obj)`, отслеживая цепочку свойств **через
 * переданный прокси**. В отличие от `Reactive.watch`, который разрешает путь от
 * корня, работает и для корня, и для любого вложенного прокси.
 */
function subscribeToAccessor(obj, path, cb) {
    const holder = signal(path(obj));
    const stop = effect(() => { holder.value = path(obj); });
    const off = holder.subscribe(cb);
    return () => {
        off();
        stop();
    };
}
/**
 * Free `watch()`: subscribes to a `Signal` or to a path of a `Reactive` object
 * (root or any nested proxy). Returns an unsubscription function.
 *
 * РУС: Свободный `watch()`: подписывается на `Signal` или путь объекта
 * `Reactive` (корня или любого вложенного прокси). Возвращает функцию отписки.
 */
export function watch(source, path, cb) {
    if (source instanceof Signal)
        return source.subscribe(cb);
    const reactor = reactorOf(source);
    if (!reactor) {
        throw new TypeError('bso5: watch() source must be a Signal or a Reactive value/proxy');
    }
    if (typeof path === 'string')
        return reactor.watch(path, cb);
    // An expression accessor has no path: reject early, as Reactive.watch does.
    // РУС: У аксессора-выражения нет пути — отвергаем сразу, как Reactive.watch.
    const pathStr = getPropertyName(path);
    if (!pathStr) {
        throw new Error('bso5: watch() requires a plain property path (e.g. x => x.user.name)');
    }
    // Root paths keep the re-binding behaviour of Reactive.watch; a nested proxy
    // binds to its own object (see the note in `$()`).
    // РУС: Пути от корня сохраняют перепривязку из Reactive.watch; вложенный прокси
    // привязывается к своему объекту (см. пояснение в `$()`).
    const isRoot = source === reactor.target || source === reactor.value;
    return isRoot
        ? reactor.watch(pathStr, cb)
        : subscribeToAccessor(source, path, cb);
}
//# sourceMappingURL=reactive.js.map