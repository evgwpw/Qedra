// Подшаг 22.4: флаг отмены вычисления (таймаут, отмена запроса клиентом MCP, предел памяти).
// Флаг поднимает сторож из другого потока (McpHost); интерпретатор и долгие циклы алгебры проверяют его в дешёвых местах —
// одно чтение статического поля:
//   * Debug.checkStack — каждый нехвостовой вызов Lisp-функции и каждый уровень рекурсии упрощателя (Simplify);
//   * трамплин хвостовых вызовов (Compiler.runBody) — бесконечный хвостовой цикл;
//   * алгебра на F#: внешняя итерация Бухбергера и шаг редукции (Groebner), перебор комбинаций факторизации (UniFactor),
//     попытки подстановок многомерной факторизации (PolyFactor).
// Флаг «липкий»: остаётся поднятым до конца запроса (опускает его владелец — сторож McpHost/AgentApi), поэтому исключение,
// проглоченное где-то catch-all кодом F# или Lisp, возникает снова на следующей проверке. Lisp-форма try исключение отмены
// не перехватывает, unwind-protect выполняет очистку с временно опущенным флагом (suspended) — assuming восстанавливает декларации.
module Cancel

open System.Threading

// Исключение прерывания; Message — «Прервано: причина»
type CancelledException(reason: string) =
    inherit System.Exception("Прервано: " + reason)
    member _.Reason = reason

// Поднят ли флаг (читается в горячем пути — обычное поле; пишет поток сторожа).
// Замечание ревью WASM.1): без Volatile.Write(&поле) — адрес модульного поля, встроенный компилятором в другую
// сборку (Release), ссылается на служебный тип <StartupCode$Cas-Algebra>.$Cas.Algebra с неверно разбитым именем:
// «Could not load type» в Release и WASM. Порядок «причина, затем флаг» держит Thread.MemoryBarrier.
let mutable requested : bool = false

// Причина прерывания («таймаут 60 с», «запрос отменён клиентом», «превышен предел памяти ...»)
let mutable reason : string = ""

// Бюджет времени (call-with-time-limit): дедлайн вместо таймера на другом потоке. В WASM колбэк
// System.Threading.Timer не выполняется, пока интерпретатор синхронно занят, поэтому бюджет там не срабатывал
// и вычисление висело навсегда. Дедлайн читают те же дешёвые проверки, что и флаг отмены.
let mutable deadlineTicks : int64 = 0L
let mutable deadlineReason : string = ""
let mutable tickCounter : int = 0

// Поставить бюджет на seconds. Действует более ранний из двух дедлайнов: вложенный бюджет не продлевает внешний
// (замечание ревью WASM.1: внешний 0,5 с с внутренним 10 с шёл 10 с). Возвращает (прежний дедлайн, прежняя
// причина, свой дедлайн) — для popDeadline и ownExpired
let pushDeadline (seconds: float) : int64 * string * int64 =
    let prev = deadlineTicks
    let prevReason = deadlineReason
    let own = System.Diagnostics.Stopwatch.GetTimestamp() + int64 (max 0.0 seconds * float System.Diagnostics.Stopwatch.Frequency)
    if prev = 0L || own < prev then
        deadlineReason <- sprintf "бюджет времени %g с" seconds
        deadlineTicks <- own
    (prev, prevReason, own)

let popDeadline (prev: int64, prevReason: string, _own: int64) : unit =
    deadlineTicks <- prev
    deadlineReason <- (if prev = 0L then "" else prevReason)

// Истёк ли СВОЙ бюджет вызова (а не внешний, более ранний)
let ownExpired (_prev: int64, _prevReason: string, own: int64) : bool =
    System.Diagnostics.Stopwatch.GetTimestamp() >= own

// Поднять флаг (из любого потока)
let request (why: string) : unit =
    reason <- why
    Thread.MemoryBarrier()
    requested <- true
    Thread.MemoryBarrier()

let clear () : unit =
    requested <- false
    Thread.MemoryBarrier()

// Редкий путь: бросить исключение (отдельная функция — проверка check остаётся маленькой и встраивается)
[<System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)>]
let throwCancelled () : unit = raise (CancelledException reason)

// Редкий путь проверки дедлайна — отдельной функцией (check остаётся маленькой)
[<System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.NoInlining)>]
let checkDeadline () : unit =
    tickCounter <- tickCounter + 1
    if tickCounter &&& 63 = 0 && System.Diagnostics.Stopwatch.GetTimestamp() >= deadlineTicks then
        request deadlineReason
        throwCancelled ()

// Проверка: флаг поднят или истёк бюджет — CancelledException. Дедлайн смотрим не на каждом вызове
// (Stopwatch.GetTimestamp ≈ 20 нс), а раз в 64 проверки — задержка реакции остаётся микроскопической.
let inline check () : unit =
    if requested then throwCancelled ()
    elif deadlineTicks <> 0L then checkDeadline ()

// Выполнить f с временно опущенным флагом (очистка после прерывания: unwind-protect, конец перехвата print);
// флаг, поднятый до входа, восстанавливается. Бюджет на время очистки тоже снимается — иначе очистка
// сразу прервётся истёкшим дедлайном.
let suspended (f: unit -> 'a) : 'a =
    let was = requested
    let wasDeadline = deadlineTicks
    if was then requested <- false
    deadlineTicks <- 0L
    try f ()
    finally
        deadlineTicks <- wasDeadline
        if was then requested <- true
