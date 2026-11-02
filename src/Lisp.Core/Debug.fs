// Шаг 15b: инструменты отладки — стек вызовов Lisp, форматирование ошибок, trace
//
// Состояние модульное (глобальное): интерпретатор однопоточный (тесты идут непараллельно).
// Стек хранится в двух массивах (имена и аргументы), кадр-запись создаётся только при снимке ошибки —
// обычное выполнение платит за push/pop лишь запись в массивы.
module Debug

#nowarn "9" "51"   // адрес локальной переменной (checkStack): указатель стека

open System
open System.Collections.Generic
open System.IO
open Types

// --- Стек кадров ---

// Слот стека: struct-массив — запись без проверки ковариантности ссылочных массивов
[<Struct>]
// Шаг 17b: аргументы — либо список, либо первые SN элементов массива-фрейма вызываемой функции
// (без выделения списка на каждый вызов); при снимке стека массив превращается в список
// Шаг 21d: SPos — номер (SrcPos.Id) позиции вызывающей формы в исходнике, 0 — неизвестна. Именно int, а не ссылка:
// влезает в дополнение структуры рядом с SN и не требует барьера записи GC
// Шаг 21i' (b): список и массив — в одном поле SArgs (LispValue list | LispValue[]). У кадра-массива (вызов
// скомпилированной функции) SName = null: имя берётся при снимке из последнего элемента фрейма (вызванная функция,
// см. Types.Node). Кадр пишет одну ссылку вместо трёх: каждая ссылка в долгоживущий массив слотов — барьер записи GC
// (≈ 4 нс на вызов); запись null барьера не требует
type private Slot = { SName: string; SArgs: obj; SN: int; SPos: int }

let mutable private slots : Slot[] = Array.zeroCreate 1024

// Текущая глубина стека (число кадров); eval/apply запоминают её на входе и восстанавливают при выходе
let mutable depth : int = 0

// Логический лимит глубины (set-max-depth)
let mutable maxDepth : int = 100000

// Аргументы кадра списком
let private slotArgs (s: Slot) : LispValue list =
    match s.SArgs with
    | :? (LispValue[]) as a -> List.ofArray (Array.sub a 0 s.SN)
    | :? (LispValue list) as l -> l
    | _ -> []

// Имя кадра: записанное или (кадр-массив) имя функции из последнего элемента фрейма
let private slotName (s: Slot) : string =
    if not (isNull s.SName) then s.SName
    else
        match s.SArgs with
        | :? (LispValue[]) as a when a.Length > 0 ->
            match a.[a.Length - 1] with
            | LispFunc u | LispMacro u -> u.Name
            | _ -> "<builtin>"
        | _ -> "<builtin>"

// Снимок стека: самый глубокий кадр — первый
let snapshot () : Frame list =
    let mutable acc = []
    for i in 0 .. depth - 1 do
        let s = slots.[i]
        acc <- { Name = slotName s; Args = slotArgs s; Pos = SrcPos.ById s.SPos } :: acc
    acc

// Ошибка превышения глубины рекурсии
let private depthExceeded () : exn =
    LispError (sprintf "Превышена глубина рекурсии %d" maxDepth, snapshot (), LispNil)

// Редкий путь кадра: лимит глубины (ошибка) или расширение массива слотов
let private pushSlow (name: string) (args: obj) (n: int) (pos: int) : unit =
    let d = depth
    if d >= maxDepth then raise (depthExceeded ())
    if d >= slots.Length then Array.Resize(&slots, max (d * 2) 16)
    slots.[d] <- { SName = name; SArgs = args; SN = n; SPos = pos }
    depth <- d + 1

// Положить кадр. Шаг 21i' (b): быстрый путь — две проверки и запись; маленький, чтобы JIT встраивал его в вызывающего
[<System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)>]
let push (name: string) (args: LispValue list) (pos: int) : unit =
    let d = depth
    let sl = slots
    if d < maxDepth && d < sl.Length then
        sl.[d] <- { SName = name; SArgs = args; SN = 0; SPos = pos }
        depth <- d + 1
    else pushSlow name args 0 pos

// Кадр вызова скомпилированной функции: аргументы — первые n элементов фрейма arr, имя — по последнему элементу
// фрейма (вызванная функция); без построения списка
[<System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)>]
let pushArr (arr: LispValue[]) (n: int) (pos: int) : unit =
    let d = depth
    let sl = slots
    if d < maxDepth && d < sl.Length then
        sl.[d] <- { SName = null; SArgs = arr; SN = n; SPos = pos }
        depth <- d + 1
    else pushSlow null arr n pos

// Хвостовой вызов: заменить верхний кадр
let replaceTop (name: string) (args: LispValue list) (pos: int) : unit =
    let d = depth
    if d = 0 then push name args pos
    else slots.[d - 1] <- { SName = name; SArgs = args; SN = 0; SPos = pos }

[<System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)>]
let replaceTopArr (arr: LispValue[]) (n: int) (pos: int) : unit =
    let d = depth
    if d = 0 then pushSlow null arr n pos
    else slots.[d - 1] <- { SName = null; SArgs = arr; SN = n; SPos = pos }

// --- Преобразование исключений ---

// Шаг 21i' (b): граница «проверенного» системного стека потока. RuntimeHelpers.TryEnsureSufficientExecutionStack
// (вызов в среду выполнения, ≈ 5 нс) делается, только когда указатель стека опустился ниже границы, запомненной при
// последней успешной проверке; граница = место той проверки минус StackSlack. Проверка гарантирует ≥ 128 КБ (64-бит)
// свободного стека ниже места проверки, так что выше границы свободно ≥ 128 − 32 = 96 КБ. Поле — на поток
// (тесты и хосты могут вычислять в разных потоках); 0 — ещё не проверялось
type StackGuard() =
    [<ThreadStatic; DefaultValue>]
    static val mutable private limit : nativeint
    static member Limit with get () = StackGuard.limit and set (v: nativeint) = StackGuard.limit <- v

let private stackSlack = 32768n

let private checkStackSlow (sp: nativeint) : unit =
    Cancel.check ()
    if not (System.Runtime.CompilerServices.RuntimeHelpers.TryEnsureSufficientExecutionStack()) then
        raise (LispError (sprintf "Переполнение стека (глубина %d)" depth, snapshot (), LispNil))
    StackGuard.Limit <- sp - stackSlack

// Проверка остатка системного стека: бросает LispError ДО реального переполнения.
// Бросаем сами (а не InsufficientExecutionStackException): тогда на каждом уровне eval не нужен catch —
// catch-обработчики .NET выполняются поверх глубокого стека, а повторный rethrow на каждом уровне его исчерпывает.
// Подшаг 22.4: здесь же — проверка флага отмены (Cancel.requested: таймаут/отмена запроса MCP) — одно чтение поля
// на вызов; редкий путь (checkStackSlow) бросает Cancel.CancelledException
let checkStack () : unit =
    let mutable probe = 0
    let sp = NativeInterop.NativePtr.toNativeInt &&probe
    let lim = StackGuard.Limit
    if sp < lim || lim = 0n || Cancel.requested then checkStackSlow sp


// Любое не-LispError исключение при первом пересечении eval/apply → LispError со снимком стека
let wrap (ex: exn) : exn =
    match ex with
    | LispError _ -> ex
    | :? InsufficientExecutionStackException ->
        LispError (sprintf "Переполнение стека (глубина %d)" depth, snapshot (), LispNil)
    // подшаг 22.4: прерывание — данные (timeout "причина") (AgentApi.classifyError → status timeout)
    | :? Cancel.CancelledException as c -> LispError (c.Message, snapshot (), LispList [ LispSym "timeout"; LispStr c.Reason ])
    | _ -> LispError (ex.Message, snapshot (), LispNil)

// Идёт ли вычисление (самый внешний eval/apply уже охраняет исключения)
let mutable active : bool = false

// --- Форматирование ---

let private maxLen = 60
let private maxFrames = 20

let truncate (s: string) : string =
    if s.Length > maxLen then s.Substring(0, maxLen - 3) + "..." else s

// Печать значения с усечением; ошибка печати (например, в Lisp-методе print) не должна ронять отчёт
let showValue (v: LispValue) : string =
    try truncate (Printer.prettyPrint v) with _ -> "#<?>"

// Шаг 21d: для кадров с известной позицией — « — файл:строка» (где находится вызывающая форма)
let formatFrame (f: Frame) : string =
    "  в " + f.Name + " (" + String.concat " " (List.map showValue f.Args) + ")"
    + (if isNull f.Pos then "" else " — " + f.Pos.ToString())

// Строки кадров (не более maxFrames, затем «... ещё N»)
let frameLines (stack: Frame list) : string list =
    let shown = stack |> List.truncate maxFrames |> List.map formatFrame
    let rest = stack.Length - maxFrames
    if rest > 0 then shown @ [ sprintf "  ... ещё %d" rest ] else shown

let formatError (ex: exn) : string =
    match ex with
    | LispError (msg, stack, _) -> String.concat "\n" (msg :: frameLines stack)
    | _ -> ex.Message

// --- Объект ошибки (значение для try) ---

// Поля: сообщение, стек (список строк), данные
let errorObject (ex: exn) : LispValue =
    let msg, lines, data =
        match ex with
        | LispError (m, st, d) -> m, frameLines st, d
        | _ -> ex.Message, [], LispNil
    LispObject
        { Type = "error"
          Fields = [| LispStr msg
                      (if lines.IsEmpty then LispNil else LispList (lines |> List.map LispStr))
                      data |] }

// Последняя ошибка REPL/AgentApi (объект ошибки) — для (backtrace)
let mutable lastError : LispValue = LispNil

// --- Шаг D3c: отладочный режим проглоченных ошибок ---
// LISP_DEBUG=1 (переменная окружения) или (set-debug! #t): каждая ошибка, перехваченная try
// с обработчиком, печатается в stderr одной строкой (сообщение + верх стека) и пишется в
// warnings ответа MCP/JSON (Debug.swallowed). По умолчанию выключено — поведение не меняется.
// Флаг и буфер — на поток (ThreadLocal): параллельные тесты/запросы не видят чужих проглоченных ошибок;
// LISP_DEBUG задаёт начальное значение для каждого потока, set-debug! — только для текущего.
let private envDebug : bool =
    match Environment.GetEnvironmentVariable "LISP_DEBUG" with
    | null | "" -> false
    | v -> v <> "0" && v.ToLower() <> "false"
let private debugFlag = new System.Threading.ThreadLocal<bool>(fun () -> envDebug)
let swallowedDebug () : bool = debugFlag.Value

// проглоченные ошибки (сообщения одной строкой) для warnings; ограничено (кольцо по отсечению головы)
let private swallowedBuf = new System.Threading.ThreadLocal<ResizeArray<string>>(fun () -> ResizeArray<string>())
let private swallowedMax = 100

// зафиксировать проглоченную ошибку: печать в stderr + запись в буфер (только при включённом режиме)
let swallow (ex: exn) : unit =
    if debugFlag.Value then
        let line =
            match ex with
            | LispError (m, st, _) ->
                // «где»: верхняя строка стека, если есть
                match st with
                | f :: _ -> m + " | в " + f.Name
                | [] -> m
            | other -> other.Message
        try eprintfn "[проглочено] %s" line with _ -> ()
        let buf = swallowedBuf.Value
        buf.Add line
        if buf.Count > swallowedMax then buf.RemoveAt 0

// снимок и очистка буфера проглоченных ошибок (AgentApi: в начало запроса — очистка, в конец — в warnings)
let swallowed () : string list = List.ofSeq swallowedBuf.Value
let swallowedClear () : unit = swallowedBuf.Value.Clear()

// включить/выключить отладочный режим (текущий поток); при выключении буфер очищается
let setSwallowedDebug (on: bool) : unit =
    debugFlag.Value <- on
    if not on then swallowedClear ()

// --- Вывод отладочных сообщений (trace, describe, backtrace, explain-dispatch) ---

// Приёмник вывода: null — текущий Console.Out (тесты подставляют StringWriter)
let mutable writer : TextWriter = null
let out () : TextWriter = if isNull writer then Console.Out else writer

// --- Шаг 21d: трассировка упрощения (trace-simplify / simplify-steps) ---
// Точки в Simplify.fs проверяют ОДИН флаг (simpTracing) и только при включённой трассировке строят формы «до»/«после»
// и вызывают simpStep: выключенная трассировка не выделяет память и не меняет результаты. Шаг = (имя преобразования, до, после),
// в порядке выполнения (вложенные упрощения — раньше объемлющих). Длина ограничена simpMaxSteps, затем simpTruncated

// Шаг S.1: второй потребитель — журнал шагов в режиме trace (StepLog.Journal.TraceSimplify): каждое преобразование
// пишется шагом level detail, rule "simplify:имя". simpTracing = идёт сбор simplify-steps ИЛИ кто-то пишет trace
let mutable simpTracing : bool = false
let private simpSteps = ResizeArray<string * LispValue * LispValue>()
let mutable simpTruncated : bool = false
let simpMaxSteps = 500
let mutable private simpCollecting : bool = false
let mutable private simpJournalUsers : int = 0
let private refreshSimpTracing () = simpTracing <- simpCollecting || simpJournalUsers > 0

// Заголовок шага упрощателя по-русски (имена преобразований — docs\math-language.md, trace_simplify)
let simpStepTitle (name: string) : string =
    match name with
    | "collect-terms" -> "приведение подобных"
    | "merge-powers" -> "объединение степеней"
    | "exact-value" -> "точное значение функции"
    | "combinatorial-value" -> "значение комбинаторной функции"
    | "exact-root" -> "точное значение корня"
    | "extract-root" -> "вынесение множителя из-под корня"
    | "exp-merge" -> "произведение экспонент"
    | "exp-power" -> "степень экспоненты"
    | "power-of-product" -> "степень произведения"
    | "power-of-power" -> "степень степени"
    | "imaginary-power" -> "степень мнимой единицы"
    | "distribute-minus" -> "раскрытие минуса"
    | "pythagorean" -> "основное тригонометрическое тождество"
    | "trig-rules" -> "тригонометрическое тождество"
    | "sqrt-rational" -> "корень из рационального числа"
    | "sqrt-negative" -> "корень из отрицательного числа"
    | "ln-to-log" -> "ln как log"
    | n when n.StartsWith "rule:" -> "правило " + n.Substring 5
    | n when n.StartsWith "method:" -> "метод " + n.Substring 7
    | n -> "упрощение: " + n

// comment — пояснение шага (Шаг AC.3: привязки AC-правила); "" — без пояснения
// title — заголовок вместо стандартного ("" — стандартный; правила defrule с :title)
let simpStepT (name: string) (title: string) (comment: string) (before: LispValue) (after: LispValue) : unit =
    if StepLog.Journal.TraceSimplify && StepLog.Journal.Enabled then
        StepLog.Journal.Record("simplify:" + name, (if title = "" then simpStepTitle name else title), comment, box before, box after, StepLog.Detail)
    if simpCollecting then
        if simpSteps.Count >= simpMaxSteps then simpTruncated <- true
        else simpSteps.Add((name, before, after))

let simpStepC (name: string) (comment: string) (before: LispValue) (after: LispValue) : unit =
    simpStepT name "" comment before after

let simpStep (name: string) (before: LispValue) (after: LispValue) : unit = simpStepC name "" before after

// Выполнить f с включённой трассировкой: шаги (и признак усечения). Вложенный вызов (уже идёт трассировка)
// просто выполняет f — шаги копятся в общий журнал внешнего
let collectSimpSteps (f: unit -> LispValue) : LispValue * (string * LispValue * LispValue) list * bool =
    if simpCollecting then
        let r = f ()
        r, [], false
    else
        simpSteps.Clear()
        simpTruncated <- false
        simpCollecting <- true
        refreshSimpTracing ()
        try
            let r = f ()
            r, List.ofSeq simpSteps, simpTruncated
        finally
            simpCollecting <- false
            refreshSimpTracing ()
            simpSteps.Clear()

// Шаг S.1: выполнить f, записывая шаги упрощателя в журнал текущего потока (режим trace; журнал должен быть включён)
let withSimplifyJournal (f: unit -> 'a) : 'a =
    let saved = StepLog.Journal.TraceSimplify
    StepLog.Journal.TraceSimplify <- true
    simpJournalUsers <- simpJournalUsers + 1
    refreshSimpTracing ()
    try f ()
    finally
        simpJournalUsers <- simpJournalUsers - 1
        refreshSimpTracing ()
        StepLog.Journal.TraceSimplify <- saved

// --- trace ---

let private traced = HashSet<string>()
let private tracedPrefixes = HashSet<string>()   // trace-methods: все методы операции "op(..."
let mutable tracing : bool = false               // быстрая проверка в горячем пути
let mutable private traceLevel = 0

// Шаг 17b: профилирование включается (profile выражение); выключено по умолчанию
let mutable profiling : bool = false
// Единственный флаг для горячего пути: включён trace ИЛИ профилирование (одна проверка в evalCore)
let mutable hooked : bool = false

let private refresh () =
    tracing <- traced.Count > 0 || tracedPrefixes.Count > 0
    hooked <- tracing || profiling

let traceAdd (name: string) = traced.Add name |> ignore; refresh ()
let traceMethods (op: string) = tracedPrefixes.Add (op + "(") |> ignore; refresh ()
let untrace (name: string) =
    traced.Remove name |> ignore
    tracedPrefixes.Remove (name + "(") |> ignore
    refresh ()
let untraceAll () =
    traced.Clear(); tracedPrefixes.Clear(); traceLevel <- 0; refresh ()
let tracedList () : string list =
    [ yield! Seq.sort traced; yield! tracedPrefixes |> Seq.sort |> Seq.map (fun p -> p + "...)") ]

// Печать аргументов может вызывать трассируемые методы print: пока печатаем трассу, trace отключён
let mutable private suppress = false

let isTraced (name: string) : bool =
    tracing && not suppress && (traced.Contains name || (tracedPrefixes |> Seq.exists (fun p -> name.StartsWith p)))

// Вызов с трассировкой: вход → результат (отступ по глубине трассируемых вызовов)
let traceCall (name: string) (args: LispValue list) (call: unit -> LispValue) : LispValue =
    let indent = String(' ', 2 * traceLevel)
    let w = out ()
    let quiet (f: unit -> string) =
        suppress <- true
        try f () finally suppress <- false
    w.WriteLine(indent + quiet (fun () -> "→ (" + String.concat " " (name :: List.map showValue args) + ")"))
    traceLevel <- traceLevel + 1
    let r =
        try call ()
        finally traceLevel <- traceLevel - 1
    w.WriteLine(indent + quiet (fun () -> "← " + name + " = " + showValue r))
    r

// --- Шаг 17b: профилировщик ---
// Вызовы (user-функции, builtin, методы) оборачиваются в `measure`: считаем число вызовов,
// включительное время (с вложенными вызовами) и собственное (без вложенных измеряемых вызовов).
// Включительное время рекурсивной функции считается только на внешнем вхождении (без двойного счёта).
// Профилируемые вызовы идут без TCO (как и трассируемые).

type ProfEntry(name: string, isBuiltin: bool) =
    member val Name = name
    member val IsBuiltin = isBuiltin
    member val Calls = 0L with get, set
    member val Inclusive = 0L with get, set    // тики Stopwatch
    member val Exclusive = 0L with get, set
    member val Active = 0 with get, set        // число активных вхождений (рекурсия)

let private profTable = Dictionary<string, ProfEntry>()       // user-функции и методы
let private profBuiltins = Dictionary<string, ProfEntry>()    // builtin (отдельная таблица: имена могут совпасть)
let mutable private childTicks = 0L

let profReset () =
    profTable.Clear()
    profBuiltins.Clear()
    childTicks <- 0L

let setProfiling (on: bool) =
    profiling <- on
    refresh ()

// Выполнить вызов с измерением
let measure (name: string) (isBuiltin: bool) (call: unit -> LispValue) : LispValue =
    let table = if isBuiltin then profBuiltins else profTable
    let e =
        match table.TryGetValue name with
        | true, e -> e
        | _ ->
            let e = ProfEntry(name, isBuiltin)
            table.[name] <- e
            e
    let saved = childTicks
    childTicks <- 0L
    e.Active <- e.Active + 1
    let t0 = Diagnostics.Stopwatch.GetTimestamp()
    try
        call ()
    finally
        let dt = Diagnostics.Stopwatch.GetTimestamp() - t0
        e.Calls <- e.Calls + 1L
        e.Active <- e.Active - 1
        if e.Active = 0 then e.Inclusive <- e.Inclusive + dt
        e.Exclusive <- e.Exclusive + (dt - childTicks)
        childTicks <- saved + dt

let private toMs (ticks: int64) : float =
    float ticks * 1000.0 / float Diagnostics.Stopwatch.Frequency

// Отчёт: таблица по собственному времени (топ 30), итог, доля builtins и «чистой интерпретации»
let profileReport (totalTicks: int64) : unit =
    let w = out ()
    let rows = Seq.append profTable.Values profBuiltins.Values |> Seq.sortByDescending (fun e -> e.Exclusive) |> Seq.toList
    w.WriteLine "профиль:"
    w.WriteLine(sprintf "  %-34s %9s %12s %12s" "функция" "вызовов" "включ., мс" "собств., мс")
    for e in rows |> List.truncate 30 do
        let label = (if e.IsBuiltin then "[builtin] " else "") + e.Name
        let label = if label.Length > 34 then label.Substring(0, 31) + "..." else label
        w.WriteLine(sprintf "  %-34s %9d %12.2f %12.2f" label e.Calls (toMs e.Inclusive) (toMs e.Exclusive))
    if rows.Length > 30 then w.WriteLine(sprintf "  ... ещё %d" (rows.Length - 30))
    let builtinTicks = rows |> List.filter (fun e -> e.IsBuiltin) |> List.sumBy (fun e -> e.Exclusive)
    let pure' = max 0L (totalTicks - builtinTicks)
    let pct (t: int64) = if totalTicks <= 0L then 0.0 else 100.0 * float t / float totalTicks
    w.WriteLine(sprintf "  всего: %.2f мс" (toMs totalTicks))
    w.WriteLine(sprintf "  в builtins (F#: simplify, MPoly, factor, арифметика...): %.2f мс (%.1f%%)" (toMs builtinTicks) (pct builtinTicks))
    w.WriteLine(sprintf "  чистая интерпретация Lisp (всего - builtins): %.2f мс (%.1f%%)" (toMs pure') (pct pure'))
