// Журнал шагов решения (шаг 21h' — основа, шаг S.1 — дерево шагов, уровни, лимиты).
// Шаг: стабильный английский идентификатор приёма (rule, kebab-case: "integration-by-parts"), заголовок и пояснение
// по-русски (title, comment), выражение до и после (before/after — произвольные значения: выражение Lisp LispValue
// или многочлен MPoly; печатает вызывающий код), уровень (main — виден в кратком решении, detail — только в полном)
// и вложенные шаги (children).
//
// Вложенность — рамки: Open(...) открывает рамку, все шаги до Close(...) становятся её детьми; Discard() отбрасывает
// рамку вместе с детьми (неудачная попытка эвристики не попадает в журнал — правило «без шума»). Стек рамок и список
// шагов — по потокам (ThreadStatic): алгебра тестируется параллельно; интерпретатор Lisp однопоточный.
//
// Стоимость при выключенном журнале — одно чтение признака потока: в горячих местах пишите
//     if StepLog.Journal.Enabled then StepLog.Journal.Record("rule-id", "Заголовок", "пояснение", до, после, StepLog.Main)
// (аргументы вычисляются только при включённом журнале).
//
// Уровни выдачи (select): brief — main-шаги верхнего уровня и их ключевые потомки (isKeyRule); full — дерево до глубины MaxDepth и не больше
// MaxNodes узлов; trace — как full (шаги упрощателя записывает Lisp.Core, если захват идёт в режиме trace).
// Отбор — при выдаче, не при записи; обрезка помечается (Omitted у узла, Selection.Total/Shown).
module StepLog

open System
open System.Collections.Generic

// Уровень шага: main — основной (краткое решение), detail — подробность (только в полном решении)
type Level =
    | Main
    | Detail

let levelName (l: Level) : string = match l with Main -> "main" | Detail -> "detail"

// Один шаг: приём (стабильный идентификатор), заголовок и пояснение по-русски, до/после, уровень, вложенные шаги;
// Omitted — сколько вложенных шагов скрыто обрезкой при выдаче (0 — ничего не скрыто)
type Step =
    { Rule: string
      Title: string
      Comment: string
      Before: obj
      After: obj
      Level: Level
      Children: Step list
      Omitted: int }

// Идентификатор приёма: латиница в нижнем регистре, цифры, «-», «:», «_», «.» (например integration-by-parts,
// simplify:collect-terms)
let isRuleId (s: string) : bool =
    not (String.IsNullOrEmpty s) && Char.IsAsciiLetterLower s.[0]
    && s |> Seq.forall (fun c -> Char.IsAsciiLetterLower c || Char.IsAsciiDigit c || c = '-' || c = ':' || c = '_' || c = '.')

// Правило совместимости для старой записи из четырёх полей (приём, комментарий, до, после), шаг 21h':
// приём-идентификатор (step, groebner-basis) становится rule с пустым заголовком; приём-текст по-русски
// («базис Грёбнера») — заголовком, rule = "step"
let legacyRuleTitle (name: string) : string * string =
    if isRuleId name then name, "" else "step", name

// Открытая рамка (with-step): дети копятся до закрытия
type private Frame(rule: string, title: string, before: obj, level: Level) =
    member val Children = ResizeArray<Step>()
    member _.Rule = rule
    member _.Title = title
    member _.Before = before
    member _.Level = level

// --- Шаг D2a: журнал попыток (attempts) ---
// Каждая рамка with-step (успешная И неудачная) оставляет узел Attempt: стратегия,
// успех/отказ, причина отказа (D2b добавит явные причины через attempt-fail), время, мс,
// повторы (соседние одинаковые схлопываются при выдаче). Пишется только при включённом
// журнале — параллельно шагам; уровни brief/full/trace не меняются.
type Attempt =
    { Rule: string
      Title: string
      Before: obj
      Ok: bool                     // true — рамка закрылась (успех), false — отброшена
      Reason: string               // успех: пояснение; отказ: причина (#f/ошибка/attempt-fail)
      Ms: float
      Repeats: int                 // сколько одинаковых соседних отказов схлопнуто (1 — один)
      Children: Attempt list }

// Открытая рамка попытки: mutable, замораживается в Attempt при Close/Discard
type private AFrame(rule: string, title: string, before: obj) =
    member val Children = ResizeArray<Attempt>()
    member _.Rule = rule
    member _.Title = title
    member _.Before = before
    member val T0 = Diagnostics.Stopwatch.GetTimestamp()
    member val Reason = "" with get, set   // явная причина (attempt-fail, шаг D2b) — приоритетнее автоматической

let private msOf (t0: int64) : float =
    let dt = Diagnostics.Stopwatch.GetTimestamp() - t0
    float dt * 1000.0 / float Diagnostics.Stopwatch.Frequency

[<Sealed; AbstractClass>]
type Journal private () =
    [<ThreadStatic; DefaultValue>]
    static val mutable private enabled : bool
    [<ThreadStatic; DefaultValue>]
    static val mutable private steps : ResizeArray<Step>
    [<ThreadStatic; DefaultValue>]
    static val mutable private frames : Stack<Frame>
    [<ThreadStatic; DefaultValue>]
    static val mutable private traceSimplify : bool
    [<ThreadStatic; DefaultValue>]
    static val mutable private aFrames : Stack<AFrame>
    [<ThreadStatic; DefaultValue>]
    static val mutable private attempts : ResizeArray<Attempt>

    // Журнал включён в текущем потоке?
    static member Enabled
        with get () : bool = Journal.enabled
        and set (v: bool) = Journal.enabled <- v

    // Режим trace: Lisp.Core пишет в журнал и шаги упрощателя (level detail, rule "simplify:имя")
    static member TraceSimplify
        with get () : bool = Journal.traceSimplify
        and set (v: bool) = Journal.traceSimplify <- v

    // Добавить готовый шаг: в верхнюю открытую рамку или в верхний уровень
    static member private Add(s: Step) : unit =
        if not (isNull Journal.frames) && Journal.frames.Count > 0 then Journal.frames.Peek().Children.Add s
        else
            if isNull Journal.steps then Journal.steps <- ResizeArray<Step>()
            Journal.steps.Add s

    // Записать шаг (при выключенном журнале — ничего не делает)
    static member Record(rule: string, title: string, comment: string, before: obj, after: obj, level: Level) : unit =
        if Journal.enabled then
            Journal.Add { Rule = rule; Title = title; Comment = comment; Before = before; After = after
                          Level = level; Children = []; Omitted = 0 }

    // Старая запись (шаг 21h'): приём, комментарий, до, после — см. legacyRuleTitle; уровень main
    static member Record(rule: string, comment: string, before: obj, after: obj) : unit =
        if Journal.enabled then
            let r, t = legacyRuleTitle rule
            Journal.Record(r, t, comment, before, after, Main)

    // Число открытых рамок
    static member Depth : int = if isNull Journal.frames then 0 else Journal.frames.Count

    // Открыть рамку; шаги до Close/Discard станут её детьми. Возвращает метку рамки (глубину после открытия) для
    // Close/Discard; при выключенном журнале — ничего не делает и возвращает 0 (тогда Close/Discard — тоже ничего).
    // D2a: параллельно открывается рамка попытки (attempts)
    static member Open(rule: string, title: string, before: obj, level: Level) : int =
        if Journal.enabled then
            if isNull Journal.frames then Journal.frames <- Stack<Frame>()
            Journal.frames.Push(Frame(rule, title, before, level))
            if isNull Journal.aFrames then Journal.aFrames <- Stack<AFrame>()
            Journal.aFrames.Push(AFrame(rule, title, before))
            Journal.frames.Count
        else 0

    // добавить замороженную попытку в родительскую рамку или верхний уровень
    static member private AddAttempt(a: Attempt) : unit =
        if not (isNull Journal.aFrames) && Journal.aFrames.Count > 0 then Journal.aFrames.Peek().Children.Add a
        else
            if isNull Journal.attempts then Journal.attempts <- ResizeArray<Attempt>()
            Journal.attempts.Add a

    // заморозить верхнюю рамку попытки (успех/отказ) — токен совпадает с frames (стеки синхронны)
    static member private FinishAttempt(token: int, ok: bool, reason: string) : unit =
        if token > 0 && Journal.aFrames.Count = token then
            let f = Journal.aFrames.Pop()
            let why = if f.Reason <> "" then f.Reason else reason
            Journal.AddAttempt { Rule = f.Rule; Title = f.Title; Before = f.Before; Ok = ok
                                 Reason = why; Ms = msOf f.T0; Repeats = 1; Children = List.ofSeq f.Children }

    // Закрыть рамку с меткой token (если она верхняя): шаг с детьми добавляется в объемлющую рамку (или верхний уровень)
    static member Close(token: int, comment: string, after: obj) : unit =
        if token > 0 && Journal.Depth = token then
            let f = Journal.frames.Pop()
            Journal.Add { Rule = f.Rule; Title = f.Title; Comment = comment; Before = f.Before; After = after
                          Level = f.Level; Children = List.ofSeq f.Children; Omitted = 0 }
            Journal.FinishAttempt(token, true, comment)

    // Отбросить рамку с меткой token вместе с детьми (неудачная попытка шагов);
    // в журнале попыток (D2a) рамка остаётся с пометкой отказа и причиной
    static member Discard(token: int) : unit =
        if token > 0 && Journal.Depth = token then
            Journal.frames.Pop() |> ignore
            Journal.FinishAttempt(token, false, "нет результата")

    // D2a/D2b: отбросить с явной причиной (attempt-fail)
    static member DiscardReason(token: int, reason: string) : unit =
        if token > 0 && Journal.Depth = token then
            Journal.frames.Pop() |> ignore
            Journal.FinishAttempt(token, false, reason)

    // D2b: явная причина для текущей (верхней) открытой рамки попытки — приоритетнее автоматической
    static member NoteFail(reason: string) : unit =
        if not (isNull Journal.aFrames) && Journal.aFrames.Count > 0 then
            Journal.aFrames.Peek().Reason <- reason

    // Рамка для F#-кода: выполнить f; finish результат → Some (комментарий, после) — рамка закрывается, None — неудача,
    // рамка отбрасывается; исключение — рамка отбрасывается, исключение летит дальше. При выключенном журнале — просто f ()
    static member Within(rule: string, title: string, before: obj, level: Level, f: unit -> 'a,
                         finish: 'a -> (string * obj) option) : 'a =
        if not Journal.enabled then f ()
        else
            let token = Journal.Open(rule, title, before, level)
            let r, fin =
                try
                    let r = f ()
                    r, finish r
                with ex ->
                    Journal.DiscardReason(token, ex.Message)
                    reraise ()
            match fin with
            | Some (comment, after) -> Journal.Close(token, comment, after)
            | None -> Journal.Discard(token)
            r

    // Записанные шаги верхнего уровня текущего потока по порядку (открытые рамки не входят)
    static member Steps : Step list =
        if isNull Journal.steps then [] else List.ofSeq Journal.steps

    // D2a: записанные попытки верхнего уровня текущего потока (дерево Attempt)
    static member Attempts : Attempt list =
        if isNull Journal.attempts then [] else List.ofSeq Journal.attempts

    // Очистить журнал текущего потока (и открытые рамки)
    static member Clear() : unit =
        if not (isNull Journal.steps) then Journal.steps.Clear()
        if not (isNull Journal.frames) then Journal.frames.Clear()
        if not (isNull Journal.attempts) then Journal.attempts.Clear()
        if not (isNull Journal.aFrames) then Journal.aFrames.Clear()

    // Выполнить f с включённым чистым журналом; вернуть результат и шаги верхнего уровня; прежнее состояние журнала
    // (признак, шаги, открытые рамки, режим trace) восстанавливается. Рамки, оставшиеся открытыми внутри f, теряются
    static member Capture(f: unit -> 'a) : 'a * Step list =
        let wasEnabled = Journal.enabled
        let saved = Journal.steps
        let savedFrames = Journal.frames
        let savedTrace = Journal.traceSimplify
        // D2a: стек попыток синхронен со стеком рамок (токен = глубина) — сохраняется и сбрасывается вместе с ним
        let savedAFrames = Journal.aFrames
        let savedAttempts = Journal.attempts
        Journal.enabled <- true
        Journal.steps <- ResizeArray<Step>()
        Journal.frames <- null
        Journal.traceSimplify <- false
        Journal.aFrames <- null
        Journal.attempts <- null
        try
            let r = f ()
            r, List.ofSeq Journal.steps
        finally
            Journal.enabled <- wasEnabled
            Journal.steps <- saved
            Journal.frames <- savedFrames
            Journal.traceSimplify <- savedTrace
            Journal.aFrames <- savedAFrames
            Journal.attempts <- savedAttempts

    // D2a: как Capture, но возвращает дерево попыток (шаги пишутся как обычно)
    static member CaptureAttempts(f: unit -> 'a) : 'a * Attempt list =
        let wasEnabled = Journal.enabled
        let savedSteps = Journal.steps
        let savedFrames = Journal.frames
        let savedTrace = Journal.traceSimplify
        let savedAFrames = Journal.aFrames
        let savedAttempts = Journal.attempts
        Journal.enabled <- true
        Journal.steps <- ResizeArray<Step>()
        Journal.frames <- null
        Journal.traceSimplify <- false
        Journal.aFrames <- null
        Journal.attempts <- ResizeArray<Attempt>()
        try
            let r = f ()
            r, List.ofSeq Journal.attempts
        finally
            Journal.enabled <- wasEnabled
            Journal.steps <- savedSteps
            Journal.frames <- savedFrames
            Journal.traceSimplify <- savedTrace
            Journal.aFrames <- savedAFrames
            Journal.attempts <- savedAttempts

// --- Уровни выдачи и лимиты ---

type Detail =
    | Brief      // только main-шаги верхнего уровня, без детей
    | Full       // дерево до глубины MaxDepth, не больше MaxNodes узлов
    | Trace      // как Full; при захвате дополнительно пишутся шаги упрощателя
    | Attempts   // D2a: журнал попыток — дерево «стратегия — успех/отказ: причина — мс» (Attempt, не Step)

let detailName (d: Detail) : string =
    match d with Brief -> "brief" | Full -> "full" | Trace -> "trace" | Attempts -> "attempts"

let tryParseDetail (s: string) : Detail option =
    match s with
    | "brief" -> Some Brief
    | "full" -> Some Full
    | "trace" -> Some Trace
    | "attempts" -> Some Attempts
    | _ -> None

let MaxDepth = 8
let MaxNodes = 200

// Результат отбора: шаги (у узлов с обрезанными детьми — Omitted > 0), показано узлов, всего узлов в выбранном уровне,
// скрыто шагов верхнего уровня (превышение MaxNodes), была ли обрезка по глубине
type Selection =
    { Steps: Step list
      Shown: int
      Total: int
      TopOmitted: int
      DepthCut: bool }

let rec countNodes (ss: Step list) : int = ss |> List.sumBy (fun s -> 1 + countNodes s.Children)

// Обрезано ли что-нибудь
let isTruncated (sel: Selection) : bool = sel.Shown < sel.Total

// Пометка об обрезке по-русски (None — ничего не обрезано)
let truncationNote (sel: Selection) : string option =
    if not (isTruncated sel) then None
    else
        let why =
            [ if sel.Shown >= MaxNodes && sel.Total > MaxNodes then sprintf "не больше %d шагов" MaxNodes
              if sel.DepthCut then sprintf "глубина до %d" MaxDepth ]
        Some (sprintf "шаги обрезаны: показано %d из %d (%s)" sel.Shown sel.Total
                (if why.IsEmpty then "лимит" else String.concat ", " why))

// Ключевые шаги алгоритма: main-шаги с этими префиксами rule (alg- алгебраический Риш, mx- смешанный случай,
// gn- род 0, pc- параметры) показываются и в brief — вложенными в главный шаг верхнего уровня; прочие дети brief не входят
let keyRulePrefixes = [ "alg-"; "mx-"; "gn-"; "pc-"; "sum-"; "gosper-"; "abramov-"; "zeilb-"; "rsolve-"; "cf-";
                        "lt-"; "ld-"; "tz-"; "tf-"; "di-"; "gal-"; "dn-"; "dio-"; "pell-"; "sq-"; "sos-";
                        "ode-classify"; "ode-check"; "ode-refuse"; "ode-fo-"; "ode-ex-";
                        "ode-lo-"; "ode-eu-"; "ode-re-"; "ode-ca-"; "ode-sy-"; "ode-se-"; "kovacic"; "risch" ]
let isKeyRule (rule: string) : bool = keyRulePrefixes |> List.exists (fun p -> rule.StartsWith(p, StringComparison.Ordinal))

// ключевые потомки на любой глубине (неключевые промежуточные рамки пропускаются, их ключевые дети поднимаются)
let rec private keyTree (ss: Step list) : Step list =
    ss |> List.collect (fun s ->
        if s.Level = Main && isKeyRule s.Rule then [ { s with Children = keyTree s.Children; Omitted = 0 } ]
        else keyTree s.Children)

let rec select (detail: Detail) (steps: Step list) : Selection =
    match detail with
    | Attempts -> select Brief steps   // D2a: Attempts — не отбор шагов (дерево Attempt отбирает selectAttempts)
    | Brief ->
        let top = steps |> List.filter (fun s -> s.Level = Main) |> List.map (fun s -> { s with Children = keyTree s.Children; Omitted = 0 })
        let kept = top |> List.truncate MaxNodes
        { Steps = kept; Shown = countNodes kept; Total = countNodes top; TopOmitted = top.Length - kept.Length; DepthCut = false }
    | Full | Trace ->
        let budget = ref MaxNodes
        let depthCut = ref false
        // depth — глубина узлов списка ss (верхний уровень — 1); → (оставленные, скрыто узлов)
        let rec prune (depth: int) (ss: Step list) : Step list * int =
            let kept = ResizeArray<Step>()
            let mutable omitted = 0
            for s in ss do
                if budget.Value <= 0 then omitted <- omitted + 1 + countNodes s.Children
                else
                    budget.Value <- budget.Value - 1
                    if depth >= MaxDepth then
                        let cut = countNodes s.Children
                        if cut > 0 then depthCut.Value <- true
                        kept.Add { s with Children = []; Omitted = cut }
                    else
                        let ch, om = prune (depth + 1) s.Children
                        kept.Add { s with Children = ch; Omitted = om }
            List.ofSeq kept, omitted
        let kept, top = prune 1 steps
        { Steps = kept; Shown = MaxNodes - budget.Value; Total = countNodes steps; TopOmitted = top; DepthCut = depthCut.Value }

// --- D2a: отбор дерева попыток ---

// похожие ли попытки (для схлопывания повторов): то же правило и результат; причина учитывается только у отказов
// (у успеха пояснение обычно различается); дети должны совпадать по структуре правил
let rec private similarAttempts (a: Attempt) (b: Attempt) : bool =
    a.Rule = b.Rule && a.Ok = b.Ok
    && (a.Ok || a.Reason = b.Reason)
    && List.length a.Children = List.length b.Children
    && List.forall2 similarAttempts a.Children b.Children

// схлопнуть соседние похожие попытки (сумма Repeats, среднее время, дети — от первой)
let rec private collapseAttempts (ss: Attempt list) : Attempt list =
    match ss with
    | [] -> []
    | a :: rest ->
        // все соседние похожие на a
        let rec splitSame (acc: Attempt list) (xs: Attempt list) : Attempt list * Attempt list =
            match xs with
            | b :: more when similarAttempts a b -> splitSame (b :: acc) more
            | _ -> (List.rev acc, xs)
        let same, others = splitSame [] rest
        let n = 1 + same.Length
        let totalMs = (a :: same) |> List.sumBy (fun x -> x.Ms)
        let merged = { a with Repeats = n; Ms = totalMs / float n }
        let collapsed = { merged with Children = collapseAttempts a.Children }
        collapsed :: collapseAttempts others

let rec countAttemptNodes (ss: Attempt list) : int = ss |> List.sumBy (fun s -> 1 + countAttemptNodes s.Children)

// отбор попыток: схлопывание повторов, затем лимиты как у full (глубина MaxDepth, узлов MaxNodes).
// → дерево, показано узлов, всего узлов (после схлопывания)
type AttemptSelection =
    { Tree: Attempt list
      Shown: int
      Total: int }

let selectAttempts (attempts: Attempt list) : AttemptSelection =
    let collapsed = collapseAttempts attempts
    let budget = ref MaxNodes
    let depthCut = ref false
    // depth — глубина (верхний уровень — 1); → оставленные (обрезанные дети пропускаются счётчиком лимита)
    let rec prune (depth: int) (ss: Attempt list) : Attempt list =
        let kept = ResizeArray<Attempt>()
        for s in ss do
            if budget.Value > 0 then
                budget.Value <- budget.Value - 1
                if depth >= MaxDepth && not (List.isEmpty s.Children) then depthCut.Value <- true
                let ch = if depth >= MaxDepth then [] else prune (depth + 1) s.Children
                kept.Add { s with Children = ch }
        List.ofSeq kept
    let tree = prune 1 collapsed
    let shown = MaxNodes - budget.Value
    let total = countAttemptNodes collapsed
    { Tree = tree; Shown = (if depthCut.Value then shown + 1 else shown); Total = (if depthCut.Value then total + 1 else total) }
