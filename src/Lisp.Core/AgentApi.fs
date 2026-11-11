// API для LLM-агентов и CLI: eval, simplify + JSON-интерфейс
// Используется MCP-сервером и CLI-режимом (stdin/stdout JSON). Шаг 22.1: ответ — единый формат ToolResponse
// (ToolResponse.fs), статус — функция classify ниже.
module AgentApi

open System
open System.Diagnostics
open System.Text.Json
open Types
open Reader
open Evaluator
open Simplify
open Builtins
open Printer
open MathPrinter
open ToolResponse

// Создаём свежую сессию (окружение) — для изоляции запросов
// Включает все builtins + CAS-функции + load (файлы грузятся в сессию)
// LEAN.L3: результаты прогона Lean, принятые хостом (--lean-results). Хранятся здесь,
// чтобы каждая новая сессия (MCP/--json создают свой Env) получила их при создании.
let mutable leanResults : (string * string * string * string * string * string) list = []

let private seedLeanResults (env: Env) =
    for (hash, status, file, lemma, toolchain, log) in leanResults do
        eval (LispList [ LispSym "lean-results-add"; LispStr hash; LispStr status; LispStr file
                         LispStr lemma; LispStr toolchain; LispStr log ]) env |> ignore

let makeSession () : Env =
    let env = newEnv ()
    seedLeanResults env
    env

let private quoted (v: LispValue) : LispValue = LispList [LispSym "quote"; v]

let private parseOne (what: string) (s: string) : LispValue =
    match readAll s with
    | [v] -> v
    | _ -> failwithf "%s: ожидается одно выражение" what

// --- Вычисления операций: значение (LispValue) ---
// Шаг 22.1: значения, а не строки — по значению определяется статус ответа (classify)

let private callIn (session: Env) (op: string) (args: LispValue list) : LispValue * LispValue =
    let form = LispList (LispSym op :: List.map quoted args)
    eval form session, form

// Шаг 19/20: интегратор, series, limit — на Lisp; вызов (op 'e 'x ...) в сессии. Вторая компонента — вызываемая форма
let valIntegrate (session: Env) (var: string) (expr: string) =
    callIn session "integrate" [parseOne "integrate" expr; LispSym var]

let valSeries (session: Env) (var: string) (expr: string) (point: string) (order: int) =
    callIn session "series" [parseOne "series" expr; LispSym var; parseOne "series (point)" point; LispInteger (bigint order)]

let valLimit (session: Env) (var: string) (expr: string) (point: string) (side: string option) =
    let sideArgs = match side with Some s -> [LispSym s] | None -> []
    callIn session "limit" ([parseOne "limit" expr; LispSym var; parseOne "limit (point)" point] @ sideArgs)

// --- Основные операции API (прежний интерфейс) ---
// Каждая операция возвращает пару: (s-выражение, инфиксная математическая запись)

let private pair (v: LispValue) : string * string = (prettyPrint v, mathPrint v)

// Вычислить Lisp-выражение (строка → результаты обеих записей)
let apiEval (session: Env) (code: string) : string * string =
    // Шаг 21d: формы помнят позицию (псевдофайл «<json>») — кадры стека ошибки показывают «<json>:строка»
    let results = readAllFrom "<json>" code |> List.map (fun e -> eval e session)
    match results with
    | [] -> ("nil", "nil")
    | _ ->
        (String.concat "\n" (List.map prettyPrint results),
         String.concat "\n" (List.map mathPrint results))

// Упростить символьное выражение (не вычисляя переменные)
let apiSimplify (expr: string) : string * string = pair (simplify (parseOne "simplify" expr))

// Продифференцировать выражение по переменной
let apiDiff (var: string) (expr: string) : string * string =
    pair (Differentiate.diff var (parseOne "diff" expr) |> Simplify.simplify)

let apiIntegrate (session: Env) (var: string) (expr: string) : string * string = pair (fst (valIntegrate session var expr))

// объект ряда печатается через хук print/math-print
let apiSeries (session: Env) (var: string) (expr: string) (point: string) (order: int) : string * string =
    pair (fst (valSeries session var expr point order))

let apiLimit (session: Env) (var: string) (expr: string) (point: string) (side: string option) : string * string =
    pair (fst (valLimit session var expr point side))

// Раскрыть скобки
let apiExpand (expr: string) : string * string = pair (Expand.expand (parseOne "expand" expr))

// Факторизация — вынесение общего множителя
let apiFactor (expr: string) : string * string = pair (Factor.factor (parseOne "factor" expr))

// Шаг 8b: разбор инфиксной математической записи (без вычисления)
// «2x^2 + 3x - 5» → s-выражение + pretty
let apiParse (code: string) : string * string = pair (MathReader.mathParse code)

// Шаг 21: программа входного математического языка в сессии (переменные и функции языка живут в сессии —
// lib\mathlang.lisp). Результат: s-выражения значений всех операторов и запись в синтаксисе языка, по строке на оператор
// Вычислить один оператор языка (AST) в сессии: (math-eval-tree 'ast)
let evalMathTree (session: Env) (ast: LispValue) : LispValue =
    eval (LispList [LispSym "math-eval-tree"; quoted ast]) session

let private runMathAsts (session: Env) (asts: LispValue list) : string * string =
    let results = asts |> List.map (evalMathTree session)
    (String.concat "\n" (List.map prettyPrint results),
     String.concat "\n" (List.map mathPrintLang results))

let apiMath (session: Env) (code: string) : string * string =
    runMathAsts session (MathReader.mathParseProgram code)

// Шаг 21b: print(...) в режиме JSON не пишет в stdout (иначе ломается поток JSON-ответов), а накапливается:
// output — накопленные строки через \n (пустая строка, если print не вызывался); при ошибке output — то, что успело напечататься
let private withCapturedOutput (session: Env) (output: string ref) (f: unit -> 'a) : 'a =
    eval (LispList [LispSym "m-capture-start"]) session |> ignore
    try
        f ()
    finally
        // подшаг 22.4: после прерывания (флаг отмены поднят) перехват всё равно закрывается
        output.Value <-
            Cancel.suspended (fun () ->
                match eval (LispList [LispSym "m-capture-end"]) session with
                | LispStr s -> s
                | _ -> "")

let apiMathCaptured (session: Env) (code: string) (output: string ref) : string * string =
    let asts = MathReader.mathParseProgramFrom "<json>" code      // ошибка разбора — до выполнения, печатать нечего
    withCapturedOutput session output (fun () -> runMathAsts session asts)

// Сообщение об ошибке без Lisp-стека (для математического режима; стек — в *last-error* и (backtrace))
let plainErrorMessage (ex: exn) : string =
    match Debug.wrap ex with
    | LispError (msg, _, _) -> msg
    | other -> other.Message

// --- Шаг 22.1: статус ответа ---

// Операции, невычисленная форма которых наружу означает «не знаю» (контракт алгоритмов, docs\lisp-library-guide.md §4)
let unevaluatedOps : Set<string> = set [ "integrate"; "limit"; "sum"; "product" ]

let rec private findUnevaluated (v: LispValue) : string option =
    match v with
    | LispList (LispSym op :: _) when unevaluatedOps.Contains op -> Some op
    | LispList xs -> List.tryPick findUnevaluated xs
    | _ -> None

let private isEmptySet (session: Env) (v: LispValue) : bool =
    match v with
    | LispObject _ ->
        let isTrue form = match eval form session with LispBool true -> true | _ -> false
        isTrue (LispList [LispSym "set?"; quoted v])
        && isTrue (LispList [LispSym "null?"; LispList [LispSym "set->list"; quoted v]])
    | _ -> false

// Вызов solve в последней входной форме: (solve ...) или присваивание языка (:= имя (solve ...))
let private isSolveCall (form: LispValue option) : bool =
    match form with
    | Some (LispList (LispSym "solve" :: _))
    | Some (LispList [LispSym ":="; _; LispList (LispSym "solve" :: _)]) -> true
    | _ -> false

// Шаг 21l.7: ответ-рекуррентность (recurrence S n …) — результат Цайльбергера без
// гипергеометрической замкнутой формы (Апери): статус answer, note поясняет
let private isRecurrence (v: LispValue) : bool =
    match v with
    | LispList (LispSym "recurrence" :: _) -> true
    | _ -> false

// первый свободный символ формы (для рекуррентности: переменная n из верхней границы суммы)
let rec private firstSym (e: LispValue) : string option =
    match e with
    | LispSym s when not (List.contains s ["+"; "-"; "*"; "/"; "^"; "="; "quote"]) -> Some s
    | LispList (LispSym _ :: args) -> args |> List.tryPick firstSym
    | LispList items -> items |> List.tryPick firstSym
    | _ -> None

// Статус по значению последней формы/оператора запроса (по одной функции для всех операций и каналов):
//   * невычисленная форма известной операции на верхнем уровне (integrate, limit, sum, product) → unknown;
//     внутри ответа (x + integrate(...)) → answer с предупреждением в warnings;
//   * пустое множество — значение вызова solve → no-solution (доказано: решений нет);
//   * иначе → answer.
// nonelementary (шаг 21k.4): значение — невычисленный (integrate f x), и в канале условий есть (risch-nonelementary (integrate f x))
// от алгоритма Риша (nonelementaryReason); либо исключение с данными (nonelementary "причина"), см. classifyError.
// Шаг 21k.4: алгоритм Риша доказал неэлементарность — условие (risch-nonelementary форма) с той же невычисленной формой, что и
// значение; причина записи — в note. Значение — только неопределённый интеграл (integrate f x)
let private nonelementaryReason (v: LispValue) : string option =
    match v with
    | LispList [ LispSym "integrate"; _; _ ] ->
        ConditionLog.Conditions.All |> List.tryPick (fun c ->
            match c.Condition with
            | :? LispValue as cv ->
                match cv with
                | LispList [ LispSym "risch-nonelementary"; w ] when prettyPrint w = prettyPrint v -> Some c.Reason
                | _ -> None
            | _ -> None)
    | _ -> None

// Шаг DI.3: определённый интеграл расходится — условие (divergent форма "причина") с той же невычисленной формой
let private divergentReason (v: LispValue) : string option =
    match v with
    | LispList (LispSym "integrate" :: _) ->
        ConditionLog.Conditions.All |> List.tryPick (fun c ->
            match c.Condition with
            | :? LispValue as cv ->
                match cv with
                | LispList [ LispSym "divergent"; w; LispStr r ] when prettyPrint w = prettyPrint v -> Some r
                | _ -> None
            | _ -> None)
    | _ -> None

let classify (session: Env) (lastForm: LispValue option) (v: LispValue) : Status * string option * string list =
    match v with
    | LispList (LispSym "integrate" :: _) when (divergentReason v).IsSome ->
        Unknown, Some ("integrate: интеграл расходится (divergent): " + (divergentReason v).Value), []
    // Шаг LP.3: ответы линейного программирования — (optimal x value y)/(infeasible y)/(unbounded x d)/(unknown ...)
    | LispList (LispSym "infeasible" :: _) -> NoSolution, Some "linear-programming: ограничения несовместны (сертификат Фаркаша в ответе)", []
    | LispList (LispSym "unbounded" :: _) -> Answer, Some "linear-programming: целевая функция не ограничена (луч в ответе)", []
    | LispList [ LispSym "unknown"; _; _; LispBool false ] -> Unknown, Some "linear-programming: лимит узлов ветвления — лучшая точка не обязательно оптимальна", []
    | LispList (LispSym "integrate" :: _) when (nonelementaryReason v).IsSome ->
        Nonelementary, nonelementaryReason v, []
    | LispList (LispSym op :: _) when unevaluatedOps.Contains op ->
        Unknown, Some (op + ": ответ не найден — возвращена невычисленная форма"), []
    | _ when isSolveCall lastForm && isEmptySet session v ->
        NoSolution, Some "solve: решений нет (пустое множество)", []
    | _ when isRecurrence v ->
        Answer, Some "замкнутой формы нет (нет гипергеометрических решений); ответ — рекуррентность с начальными значениями", []
    | _ ->
        let warnings =
            match findUnevaluated v with
            | Some op -> [ "результат содержит невычисленную форму " + op + "(...)" ]
            | None -> []
        Answer, None, warnings

// Статус исключения: данные raise (no-solution|nonelementary|unknown "причина") → этот статус с причиной;
// сообщение «...: не умею ...» (solve, series) → unknown; прочее → error
let classifyError (ex: exn) : Status * string option =
    match Debug.wrap ex with
    // подшаг 22.4: прерывание по флагу отмены (Cancel: таймаут, отмена клиентом, предел памяти)
    | LispError (_, _, LispList [LispSym "timeout"; LispStr r]) ->
        Timeout, Some ("вычисление прервано: " + r + "; сессия сохранена и готова к следующему вызову")
    | LispError (_, _, LispList [LispSym "no-solution"; LispStr r]) -> NoSolution, Some r
    | LispError (_, _, LispList [LispSym "nonelementary"; LispStr r]) -> Nonelementary, Some r
    | LispError (_, _, LispList [LispSym "unknown"; LispStr r]) -> Unknown, Some r
    | e when e.Message.Contains ": не умею" -> Unknown, Some e.Message
    | _ -> Error, None

// Действующие декларации доменов сессии: «x ∈ ℝ» — по строке на ограничение
let assumptionsOf (session: Env) : string list =
    try
        match eval (LispList [LispSym "declarations"]) session with
        | LispList entries ->
            entries |> List.collect (fun e ->
                match e with
                | LispList (x :: ds) -> ds |> List.map (fun d -> mathPrintLang (LispList [LispSym ":in"; x; d]))
                | _ -> [])
        | _ -> []
    with _ -> []

// Шаг S.1: шаг журнала → запись ответа (дерево); pretty — запись языка ((list a b) → [a, b], как в печати steps)
// Шаг S.5: lang ("ru" | "en") — только запись значений («или»/«or»); перевод заголовков — StepDict.localize до вызова
let rec stepEntryLang (lang: string) (s: StepLog.Step) : StepEntry =
    let show (o: obj) =
        match o with
        | :? LispValue as v -> prettyPrint v, AlgoBuiltins.showPayloadLang lang o
        | null -> "nil", ""
        | other -> let t = sprintf "%A" other in t, t
    let b, bp = show s.Before
    let a, ap = show s.After
    let tex (o: obj) =
        match o with
        | :? LispValue as v -> LatexPrinter.latexPrint v
        | _ -> ""
    { Rule = s.Rule; Title = s.Title; Comment = s.Comment; Before = b; BeforePretty = bp; BeforeLatex = tex s.Before
      After = a; AfterPretty = ap; AfterLatex = tex s.After
      Level = StepLog.levelName s.Level; Children = List.map (stepEntryLang lang) s.Children; Omitted = s.Omitted }

let stepEntry (s: StepLog.Step) : StepEntry = stepEntryLang "ru" s

// Шаг D2a: попытка (журнал attempts) → запись ответа: comment = «успех: пояснение» | «отказ: причина» + время/повторы,
// after — пусто (результат неудачной попытки неизвестен), level = "attempt", omitted — сколько детей скрыто обрезкой
let rec attemptEntryLang (lang: string) (a: StepLog.Attempt) : StepEntry =
    let status = if a.Ok then "успех: " + a.Reason else "отказ: " + a.Reason
    let repeats = if a.Repeats > 1 then sprintf " ×%d" a.Repeats else ""
    let comment = sprintf "%s%s — %.1f мс" status repeats a.Ms
    let b, bp =
        match a.Before with
        | :? LispValue as v -> prettyPrint v, AlgoBuiltins.showPayloadLang lang a.Before
        | null -> "nil", ""
        | other -> let t = sprintf "%A" other in t, t
    { Rule = a.Rule; Title = a.Title; Comment = comment; Before = b; BeforePretty = bp; BeforeLatex = ""
      After = ""; AfterPretty = ""; AfterLatex = ""
      Level = "attempt"; Children = List.map (attemptEntryLang lang) a.Children; Omitted = 0 }

// Условия применимости ответа: канал record-condition (ConditionLog), всегда включён; очищается в начале запроса
let private conditionEntries () : ConditionEntry list =
    ConditionLog.Conditions.All |> List.map (fun c ->
        match c.Condition with
        | :? LispValue as v -> { Pretty = mathPrintLang v; Sexpr = prettyPrint v; Reason = c.Reason }
        | other -> let t = sprintf "%A" other in { Pretty = t; Sexpr = t; Reason = c.Reason })

// --- JSON-протокол для CLI-режима ---
// Вход (одна строка): {"op": "math", "code": "integrate(x^2, x)", "steps": "none|brief|full"}
//                    {"op": "eval", "code": "(+ 1 2)"}  {"op": "diff", "code": "(* x x)", "var": "x"} ...
// Выход — ToolResponse (ToolResponse.fs): {"status":"answer","result":"3","pretty":"3",...,"ok":true,"error":null,"stack":null}

// Результат вычисления запроса: значения (по одному на форму/оператор), последняя входная форма (для правила
// no-solution), печать pretty, захваченный вывод print (только op "math")
type private Computed =
    { Values: LispValue list
      LastForm: LispValue option
      Show: LispValue -> string
      Output: string option
      Note: string option }       // пометка операции (equivalent, declarations); иначе note даёт classify

let private computed (v: LispValue) (form: LispValue option) : Computed =
    { Values = [v]; LastForm = form; Show = mathPrint; Output = None; Note = None }

// --- Подшаг 22.5: equivalent — равенство двух выражений ---

// Целые, рациональные и «x ∈ интервал» из деклараций: ограничения символа на значения проб
type private SampleRange = { Rank: int; Lo: float; Hi: float; Empty: bool }

let private sampleRange (session: Env) (name: string) : SampleRange =
    let call op (args: LispValue list) = eval (LispList (LispSym op :: List.map quoted args)) session
    let isTrue v = match v with LispBool true -> true | _ -> false
    let bound (v: LispValue) : float =
        match v with
        | LispSym "inf" -> Double.PositiveInfinity
        | LispSym "-inf" -> Double.NegativeInfinity
        | other -> match SolveNum.numEval other with Some z -> z.Real | None -> 0.0
    let ds = match call "declarations" [LispSym name] with LispList xs -> xs | _ -> []
    ds |> List.fold (fun r d ->
        if isTrue (call "domain?" [d]) then
            match call "domain-rank" [d] with
            | LispInteger n -> { r with Rank = min r.Rank (int n) }
            | _ -> r
        elif isTrue (call "interval-empty?" [d]) then { r with Empty = true }
        else
            { r with Lo = max r.Lo (bound (call "interval-lo" [d])); Hi = min r.Hi (bound (call "interval-hi" [d])) })
        { Rank = 4; Lo = Double.NegativeInfinity; Hi = Double.PositiveInfinity; Empty = false }

// Проба значения символа внутри его ограничений: рациональное p/q (ℕ ℤ — целое); None — подходящего нет.
// Границы (в том числе замкнутые) не берутся: это чаще всего особые точки; 0 тоже избегается
let private sampleValue (rnd: Random) (r: SampleRange) : (bigint * bigint) option =
    if r.Empty then None
    else
        let lo0 = if r.Rank = 0 then max r.Lo 0.0 else r.Lo
        let lo, hi =
            match Double.IsInfinity lo0, Double.IsInfinity r.Hi with
            | true, true -> -12.0, 12.0
            | true, false -> r.Hi - 12.0, r.Hi
            | false, true -> lo0, lo0 + 12.0
            | false, false -> lo0, r.Hi
        let tryDen (den: int) =
            let nmin = int (Math.Floor(lo * float den)) + 1
            let nmax = int (Math.Ceiling(hi * float den)) - 1
            if nmin > nmax then None
            else
                let p = nmin + rnd.Next(nmax - nmin + 1)
                let p = if p = 0 then (if nmax > 0 then 1 elif nmin < 0 then -1 else 0) else p
                Some (bigint p, bigint den)
        let dens = if r.Rank <= 1 then [1] else [ for _ in 1 .. 6 -> [| 1; 2; 3; 4; 5; 7; 8; 10 |].[rnd.Next 8] ] @ [ 16; 100 ]
        dens |> List.tryPick tryDen

let private showRat (p: bigint, q: bigint) : string = if q.IsOne then string p else sprintf "%O/%O" p q

let private showComplex (z: System.Numerics.Complex) : string =
    let fmt (x: float) = x.ToString("R", Globalization.CultureInfo.InvariantCulture)
    if abs z.Imaginary <= 1e-12 * max 1.0 (abs z.Real) then fmt z.Real
    else sprintf "%s%s%si" (fmt z.Real) (if z.Imaginary < 0.0 then "-" else "+") (fmt (abs z.Imaginary))

// (equivalent a b vars) → ("true" | "false" | "unknown", пояснение).
//   1. символьно: упрощение разности a - b (simplify, expand, together, cancel) даёт 0 → true;
//   2. иначе численно в случайных рациональных точках с учётом деклараций (ℕ ℤ ℚ ℝ, интервалы; необъявленный символ —
//      вещественная проба): значения различаются → false с контрпримером; во всех точках совпали → unknown
//      (по одной численной проверке true не выдаётся).
// Подробный исход проверки (подшаг 22.6: сертификаты equivalence и counterexample): Method — чем доказано
// (simplify, expand, together, cancel, together+expand) или "numeric"; Valid — число вычислимых пробных точек;
// Point — точка контрпримера («x», «1/2»), ValA/ValB — значения выражений в ней
type EquivResult =
    { Verdict: string
      Why: string
      Method: string
      Valid: int
      Point: (string * string) list
      ValA: string
      ValB: string }

let checkEquivalentFull (session: Env) (a: LispValue) (b: LispValue) (vars: string list) : EquivResult =
    let diff = LispList [LispSym "+"; a; LispList [LispSym "*"; LispInteger -1I; b]]
    let call op (v: LispValue) = eval (LispList [LispSym op; quoted v]) session
    let attempt (name: string) (f: unit -> LispValue) : string option =
        try (match f () with LispInteger z when z.IsZero -> Some name | _ -> None)
        with _ when not Cancel.requested -> None
    let proof =
        attempt "simplify" (fun () -> simplify diff)
        |> Option.orElseWith (fun () -> attempt "expand" (fun () -> simplify (call "expand" (simplify diff))))
        |> Option.orElseWith (fun () -> attempt "together" (fun () -> simplify (call "together" diff)))
        |> Option.orElseWith (fun () -> attempt "cancel" (fun () -> simplify (call "cancel" diff)))
        |> Option.orElseWith (fun () -> attempt "together+expand" (fun () -> simplify (call "expand" (call "together" (simplify diff)))))
    match proof with
    | Some how ->
        { Verdict = "true"; Why = $"доказано символьно: разность упрощается до 0 ({how}); верно там, где оба выражения определены"
          Method = how; Valid = 0; Point = []; ValA = ""; ValB = "" }
    | None ->
        let syms =
            let fs = RootSum.freeSyms (LispList [LispSym "list"; a; b]) |> Seq.filter (fun s -> s <> "pi" && s <> "%i") |> List.ofSeq
            (vars @ fs) |> List.distinct |> List.sort
        let ranges = syms |> List.map (fun s -> s, sampleRange session s)
        let rnd = Random(20260101)           // фиксированное зерно — ответ воспроизводим
        let wanted = 8
        let mutable valid = 0
        let mutable counter : string option = None
        let mutable cPoint : (string * string) list = []
        let mutable cA = ""
        let mutable cB = ""
        let mutable tries = 0
        while counter.IsNone && valid < wanted && tries < 60 do
            tries <- tries + 1
            Cancel.check ()
            let picks = ranges |> List.map (fun (s, r) -> s, sampleValue rnd r)
            if picks |> List.forall (fun (_, p) -> p.IsSome) then
                let pts = picks |> List.map (fun (s, p) -> s, p.Value)
                let env = pts |> List.map (fun (s, (p, q)) -> s, System.Numerics.Complex(float p / float q, 0.0)) |> Map.ofList
                let ok (z: System.Numerics.Complex) = not (Double.IsNaN z.Real || Double.IsNaN z.Imaginary || Double.IsInfinity z.Real || Double.IsInfinity z.Imaginary)
                match SolveNum.numEvalEnv env a, SolveNum.numEvalEnv env b with
                | Some za, Some zb when ok za && ok zb ->
                    valid <- valid + 1
                    let scale = max 1.0 (max (System.Numerics.Complex.Abs za) (System.Numerics.Complex.Abs zb))
                    if System.Numerics.Complex.Abs (za - zb) > 1e-8 * scale then
                        let at = if pts.IsEmpty then "" else (pts |> List.map (fun (s, v) -> $"{s} = {showRat v}") |> String.concat ", ") + ": "
                        counter <- Some $"контрпример: {at}первое выражение = {showComplex za}, второе = {showComplex zb}"
                        cPoint <- pts |> List.map (fun (s, v) -> s, showRat v)
                        cA <- showComplex za
                        cB <- showComplex zb
                | _ -> ()
        let r = { Verdict = "unknown"; Why = ""; Method = "numeric"; Valid = valid; Point = []; ValA = ""; ValB = "" }
        match counter with
        | Some c ->
            { r with Verdict = "false"; Why = c + " (значения при проверке вещественных пробных точек; декларации учтены)"
                     Point = cPoint; ValA = cA; ValB = cB }
        | None when valid = 0 ->
            { r with Why = "символьно не доказано; численная проверка невозможна (выражения не вычисляются числом или пробные точки вне области определения)" }
        | None ->
            { r with Why = $"символьно не доказано; численно совпадают в {valid} случайных точках (это не доказательство равенства)" }

let checkEquivalent (session: Env) (a: LispValue) (b: LispValue) (vars: string list) : string * string =
    let r = checkEquivalentFull session a b vars
    r.Verdict, r.Why

// --- Шаг S.1: помощник тестов — инвариант «каждый шаг — эквивалентное преобразование» ---
// Для каждого шага дерева (обход в глубину; путь "1", "1.2", ...): before ≡ after через checkEquivalentFull
// (механизм инструмента equivalent). Проверяется, только если обе стороны — алгебраические выражения: не nil, не строки,
// не (list ...) / множества / векторы / уравнения и отношения (решение уравнения, базис идеала — не равенство
// выражений), иначе verdict "skipped". Шаги с rule из skipRules тоже пропускаются (переход не эквивалентный по смыслу).
// Verdict: "true" | "false" (контрпример в Why) | "unknown" | "skipped"
type StepCheck =
    { StepPath: string
      StepRule: string
      Verdict: string
      Why: string }

let private nonExpressionHeads =
    set [ "list"; "set"; "="; "/="; "<"; ">"; "<="; ">="; "and"; "or"; "not"; "vector"; ":in"; "root-of"
          "limit"; "series"; "O" ]   // шаг S.4: пределы и ряды (с остатком O(...)) — не равенства выражений

let rec private isAlgebraic (v: LispValue) : bool =
    match v with
    | LispInteger _ | LispRational _ | LispFloat _ | LispComplex _ | LispAlgebraic _ | LispSym _ -> true
    | LispList (LispSym h :: args) -> not (nonExpressionHeads.Contains h) && List.forall isAlgebraic args
    | _ -> false

// Шаг S.2: невычисленная производная шага diff — (d/dx u) — вычисляется перед проверкой
let rec private expandDerivs (v: LispValue) : LispValue =
    match v with
    | LispList [ LispSym h; e ] when h.Length > 3 && h.StartsWith "d/d" -> Differentiate.diff (h.Substring 3) (expandDerivs e)
    | LispList items -> LispList (List.map expandDerivs items)
    | _ -> v

// Шаг S.3: невычисленный интеграл шага — (int/dx f) [(int/dx f a b)]; голова кодирует переменную
let private intHeadVar (h: string) : string option =
    if h.Length > 5 && h.StartsWith "int/d" then Some (h.Substring 5) else None

let rec private intHeads (v: LispValue) : (string * int) list =
    match v with
    | LispList (LispSym h :: args) ->
        (match intHeadVar h with Some x -> [ x, args.Length ] | None -> []) @ List.collect intHeads args
    | _ -> []

// «после» шага интегрирования: вложенные (int/dv g) — неопределённые интегралы той же переменной — как (integrate g v),
// чтобы дифференцирование вернуло подынтегральную функцию
let rec private intAsIntegrate (v: LispValue) : LispValue =
    match v with
    | LispList [ LispSym h; g ] when (intHeadVar h).IsSome ->
        LispList [ LispSym "integrate"; intAsIntegrate g; LispSym (intHeadVar h).Value ]
    | LispList items -> LispList (List.map intAsIntegrate items)
    | _ -> v

// Шаги замены переменной: «до» и «после» записаны в разных переменных — алгебраически не сравниваются
let private variableChangeRules = [ "int-substitution-change"; "int-back-substitution" ]

let checkSteps (session: Env) (skipRules: string list) (steps: StepLog.Step list) : StepCheck list =
    let out = ResizeArray<StepCheck>()
    let rec walk (prefix: string) (ss: StepLog.Step list) =
        ss |> List.iteri (fun i (s: StepLog.Step) ->
            let path = if prefix = "" then string (i + 1) else prefix + "." + string (i + 1)
            let mk verdict why = { StepPath = path; StepRule = s.Rule; Verdict = verdict; Why = why }
            let check =
                if List.contains s.Rule skipRules then mk "skipped" "rule в списке исключений"
                elif List.contains s.Rule variableChangeRules then mk "skipped" "замена переменной: до и после — в разных переменных"
                elif s.Rule = "int-parts-choice" then mk "skipped" "выбор u и dv: «после» — пара равенств, не выражение"
                else
                    match s.Before, s.After with
                    | (:? LispValue as b), (:? LispValue as a) when not (intHeads b @ intHeads a).IsEmpty ->
                        // шаг интегрирования: d/dx(после) = подынтегральная функция (с точностью до постоянной);
                        // «после» может содержать неопределённые интегралы той же переменной (по частям, Эрмит)
                        match b with
                        | LispList [ LispSym h; f ] when (intHeadVar h).IsSome && (intHeads f).IsEmpty
                                                         && intHeads a |> List.forall (fun (v, n) -> v = (intHeadVar h).Value && n = 1) ->
                            let r = checkEquivalentFull session (Differentiate.diff (intHeadVar h).Value (intAsIntegrate a)) f []
                            mk r.Verdict r.Why
                        | _ -> mk "skipped" "определённый интеграл или интегралы по разным переменным"
                    | (:? LispValue as b), (:? LispValue as a) when isAlgebraic b && isAlgebraic a ->
                        let r = checkEquivalentFull session (expandDerivs b) (expandDerivs a) []
                        mk r.Verdict r.Why
                    | _ -> mk "skipped" "до/после — не алгебраические выражения"
            out.Add check
            walk path s.Children)
    walk "" steps
    List.ofSeq out

// Шаги, не прошедшие проверку (Verdict "false"): пустой список — инвариант выполнен
let failedSteps (checks: StepCheck list) : StepCheck list = checks |> List.filter (fun c -> c.Verdict = "false")

// Выполнить программу языка в сессии с журналом: значение и все шаги (без отбора и лимитов) — для тестов шагов
let mathSteps (session: Env) (code: string) : LispValue * StepLog.Step list =
    let r, steps, _ = AlgoBuiltins.captureSteps None (fun () -> eval (LispList [LispSym "math-eval"; LispStr code]) session)
    r, steps

// --- Подшаг 22.6: сертификаты (проверка ответа независимым путём; по запросу certificate: true) ---
// Сертификат статус не меняет. Построение — в handleRequest (certificateFor); здесь — проверки по видам.
// Виды: derivative (integrate), substitution (solve), equivalence (simplify/expand/factor/together/apart/equivalent),
// counterexample (equivalent → false), ideal_membership (groebner), none (diff, limit, series, math, eval, ...).

// LEAN.L1: вид запрошенного сертификата (certificate: true | false | "lean")
type private CertRequest =
    | CertNone
    | CertDefault
    | CertLean

let private certOf (kind: string) (verified: string) (methodName: string) (detail: (string * CertDetail) list) : CertificateEntry =
    { Kind = kind; Verified = verified; Method = methodName; Detail = DObj detail }

let private certSkipped (kind: string) (reason: string) : CertificateEntry =
    certOf kind "skipped" "нет" [ "reason", DStr reason ]

// Проверено (true) или хотя бы численно (numeric): годится как итог перебора вариантов исходного выражения
let private certHolds (c: CertificateEntry) : bool = c.Verified = "true" || c.Verified = "numeric"

// Первый вариант, давший проверенный сертификат; иначе — сертификат первого варианта
let private bestCert (cands: 'a list) (attempt: 'a -> CertificateEntry) : CertificateEntry =
    let results = cands |> List.map attempt
    match results |> List.tryFind certHolds with
    | Some c -> c
    | None -> List.head results

let private lispCall (session: Env) (op: string) (args: LispValue list) : LispValue =
    eval (LispList (LispSym op :: List.map quoted args)) session

// Шаг LA.4: (m-vector a b ..) математического языка → обычный вложенный список Lisp (для linalg)
let rec private mVecToNested (v: LispValue) : LispValue =
    match v with
    | LispList (LispSym "m-vector" :: xs) -> LispList (List.map mVecToNested xs)
    | LispList xs -> LispList (List.map mVecToNested xs)
    | other -> other

// Элементы вектора/списка языка («[a, b]»: вектор, (m-vector ...), (list ...)); не вектор — один элемент
// (вектор значения языка — тензор формы (n), LispObject; его элементы даёт m-items)
let private isVectorValue (session: Env) (v: LispValue) : bool =
    match v with
    | LispVector _ | LispList (LispSym ("m-vector" | "vector" | "list") :: _) -> true
    | LispObject _ ->
        (match lispCall session "tensor?" [ v ] with
         | LispBool true -> (match lispCall session "tensor-shape-list" [ v ] with LispList [ _ ] -> true | _ -> false)
         | _ -> false)
    | _ -> false

let private asItems (session: Env) (v: LispValue) : LispValue list =
    match v with
    | LispVector xs -> List.ofArray xs
    | LispList (LispSym ("m-vector" | "vector" | "list") :: xs) -> xs
    | LispObject _ when isVectorValue session v -> (match lispCall session "m-items" [ v ] with LispList xs -> xs | _ -> [ v ])
    // синтаксис lisp: простой список — «((+ x 1) (- y 2))» (голова — список) или «(x y)» (одни символы)
    | LispList (LispList _ :: _ as xs) -> xs
    | LispList xs when not xs.IsEmpty && xs |> List.forall (fun e -> match e with LispSym _ -> true | _ -> false) -> xs
    | other -> [ other ]

let rec private mentionsInfinity (v: LispValue) : bool =
    match v with
    | LispSym "inf" -> true
    | LispList xs -> List.exists mentionsInfinity xs
    | _ -> false

let private minus (a: LispValue) (b: LispValue) : LispValue =
    simplify (LispList [ LispSym "+"; a; LispList [ LispSym "*"; LispInteger -1I; b ] ])

// d/dx anti = f: (verified, method, подробности) — int-check-how (lib\integrate\check.lisp): точно (simplify, together),
// иначе численно в пробных точках
let private derivativeCheck (session: Env) (show: LispValue -> string) (var: string) (f: LispValue) (anti: LispValue)
        : string * string * (string * CertDetail) list =
    let dF = Differentiate.diff var anti |> Simplify.simplify
    let how = match lispCall session "int-check-how" [ anti; f; LispSym var ] with LispSym s -> s | _ -> "skip"
    let verified, m =
        match how with
        | "simplify" -> "true", "символьно: simplify(d/dx F − f) = 0"
        | "together" -> "true", "символьно: together(d/dx F − f) = 0"
        | "numeric" -> "numeric", "численно: d/dx F = f в 5 пробных точках (символьный нуль не получен)"
        | "bad" -> "false", "численно: d/dx F ≠ f в пробных точках"
        | _ -> "skipped", "d/dx F − f не упрощается до 0 и не вычисляется численно"
    verified, m, [ "derivative", DStr (show dF); "residual", DStr (show (minus dF f)) ]

// integrate: неопределённый — d/dx F − f = 0; определённый — первообразная (повторный вызов integrate), её проверка и
// F(b) − F(a) = ответ. fs — варианты подынтегрального выражения; limits — (a, b) определённого интеграла
let private certIntegrate (session: Env) (show: LispValue -> string) (var: string) (fs: LispValue list)
        (limits: (LispValue * LispValue) option) (result: LispValue) : CertificateEntry =
    // Шаг DI.3: сертификат определённого интеграла (lib\definite.lisp): интервальный certified-integral + строгий хвост
    let definiteCert (f: LispValue) (a0: LispValue) (b0: LispValue) : CertificateEntry =
        // «-inf» входного языка — (* -1 inf) / (- inf): модулю definite нужен символ -inf
        let norm (v: LispValue) =
            match v with
            | LispList [ LispSym "*"; LispInteger n; LispSym "inf" ] when n = -1I -> LispSym "-inf"
            | LispList [ LispSym "-"; LispSym "inf" ] -> LispSym "-inf"
            | LispList [ LispSym "-"; LispInteger z; LispSym "inf" ] when z.IsZero -> LispSym "-inf"
            | _ -> v
        let a, b = norm a0, norm b0
        let head = [ "integrand", DStr (show f); "limits", DList [ DStr (show a); DStr (show b) ]; "value", DStr (show result) ]
        match (try lispCall session "definite-check" [ f; LispSym var; a; b; result ] with _ -> LispSym "unknown") with
        | LispBool true -> certOf "definite" "true" "интервальная проверка: certified-integral на конечной части и строгая оценка хвоста" head
        | LispSym "numeric" -> certOf "definite" "numeric" "численная проверка значения (интегралы с root-sum или окружностью)" head
        | LispBool false -> certOf "definite" "false" "значение не попадает в интервал, охватывающий интеграл" head
        | other -> certOf "definite" "skipped" "нет" (head @ [ "reason", DStr ("definite-check не смог ни подтвердить, ни опровергнуть значение: " + show other) ])
    let attempt (f: LispValue) =
        let head = [ "integrand", DStr (show f) ]
        if (findUnevaluated result).IsSome then certSkipped "derivative" "в ответе есть невычисленная форма — проверять нечего"
        else
            match limits with
            | None ->
                let v, m, d = derivativeCheck session show var f result
                if v = "skipped" then certOf "derivative" v m (head @ [ "antiderivative", DStr (show result) ] @ d @ [ "reason", DStr m ])
                else certOf "derivative" v m (head @ [ "antiderivative", DStr (show result) ] @ d)
            | Some (a, b) when mentionsInfinity a || mentionsInfinity b -> definiteCert f a b
            | Some (a, b) ->
                let anti = lispCall session "integrate" [ f; LispSym var ]
                if (findUnevaluated anti).IsSome then
                    let dc = definiteCert f a b
                    if certHolds dc then dc
                    else certSkipped "derivative" "первообразная не найдена (определённый интеграл вычислен другим способом) — проверять подстановкой пределов нечем"
                else
                    let v, m, d = derivativeCheck session show var f anti
                    let at (p: LispValue) = lispCall session "subst" [ LispList [ LispSym "="; LispSym var; p ]; anti ]
                    let value = minus (at b) (at a)
                    let eq = checkEquivalentFull session value result []
                    let detail =
                        head @ [ "antiderivative", DStr (show anti) ] @ d
                        @ [ "limits", DList [ DStr (show a); DStr (show b) ]; "F(b) - F(a)", DStr (show value) ]
                    match eq.Verdict with
                    | "true" -> certOf "derivative" v (m + "; F(b) − F(a) = ответ (" + eq.Method + ")") detail
                    | "false" ->
                        // F(b) − F(a) ≠ ответ: ответ мог прийти из definite (особенность внутри промежутка) — его сертификат
                        let dc = definiteCert f a b
                        if certHolds dc then dc else certOf "derivative" "false" (m + "; F(b) − F(a) ≠ ответ") detail
                    | _ ->
                        certOf "derivative" "skipped" "нет"
                            (detail @ [ "reason", DStr "F(b) − F(a) не удалось сравнить с ответом (особенность или другой способ вычисления)" ])
    bestCert fs attempt

// solve: подстановка каждого решения в каждое уравнение (solve-check, lib\solve.lisp)
let private certSolve (session: Env) (show: LispValue -> string) (eqs: LispValue) (vars: LispValue) (result: LispValue) : CertificateEntry =
    // решение системы — вектор уравнений (x = a, y = b): для solve-check это список
    let shown = match lispCall session "set->list" [ result ] with LispList xs -> xs | _ -> []
    let sols = shown |> List.map (fun s -> if isVectorValue session s then LispList (asItems session s) else s)
    let eqsArg = if isVectorValue session eqs then LispList (asItems session eqs) else eqs
    let varsArg = if isVectorValue session vars then LispList (asItems session vars) else vars
    match lispCall session "solve-check" [ eqsArg; varsArg; LispList sols ] with
    | LispList [ LispSym overall; LispList rows ] ->
        let row (i: int) (r: LispValue) =
            match r with
            | LispList [ _; LispSym st; LispList resids ] ->
                let s = if i < shown.Length then shown.[i] else LispSym "?"
                let stName = match st with "exact" -> "symbolic" | "numeric" -> "numeric" | "skip" -> "skipped" | other -> other
                DObj [ "solution", DStr (show s); "check", DStr stName
                       "residuals", DList (resids |> List.map (fun x -> DStr (show x))) ]
            | other -> DObj [ "solution", DStr (show other) ]
        let detail = [ "equations", DStr (show eqs); "solutions", DList (List.mapi row rows) ]
        match overall with
        | "exact" -> certOf "substitution" "true" "символьно: невязка каждого уравнения упрощается до 0" detail
        | "numeric" -> certOf "substitution" "numeric" "численно: невязка < 1e-8 (параметры — пробные числа); символьный нуль не получен" detail
        | "partial" ->
            certOf "substitution" "partial" "часть решений проверена подстановкой, остальные (root-of) не проверены" detail
        | "bad" -> certOf "substitution" "false" "подстановка: найдено решение с ненулевой невязкой" detail
        | "empty" -> certSkipped "substitution" "решений нет — подставлять нечего"
        | _ ->
            certOf "substitution" "skipped" "нет"
                (detail @ [ "reason", DStr "решения заданы неявно (root-of): подстановка не определена" ])
    | _ -> certSkipped "substitution" "проверка не выполнена (неожиданный вид решения)"

// groebner: остаток каждого исходного многочлена по базису (groebner-check, lib\groebner.lisp) равен 0
let private certGroebner (session: Env) (show: LispValue -> string) (polys: LispValue) (vars: LispValue)
        (order: string option) (basis: LispValue) : CertificateEntry =
    // базис — вектор языка (или список Lisp)
    let basisItems = match basis with LispList xs -> xs | other -> asItems session other
    let args = [ LispList (asItems session polys); LispList basisItems; LispList (asItems session vars) ] @ (order |> Option.map LispSym |> Option.toList)
    match lispCall session "groebner-check" args with
    | LispList rows ->
        let pairs = rows |> List.choose (fun r -> match r with LispList [ f; rem ] -> Some (f, rem) | _ -> None)
        let isZero (v: LispValue) = match v with LispInteger z -> z.IsZero | _ -> false
        let detail =
            [ "basis", DStr (show basis)
              "remainders", DList (pairs |> List.map (fun (f, rem) -> DObj [ "polynomial", DStr (show f); "remainder", DStr (show rem) ])) ]
        if pairs |> List.forall (fun (_, r) -> isZero r) then
            certOf "ideal_membership" "true"
                "нормальная форма: остаток каждого исходного многочлена по базису = 0 (идеал исходных ⊆ идеал базиса; обратное вложение не проверяется)" detail
        else certOf "ideal_membership" "false" "нормальная форма: остаток исходного многочлена по базису ≠ 0" detail
    | _ -> certSkipped "ideal_membership" "проверка не выполнена (неожиданный вид результата)"

// simplify/expand/factor/together/apart: исходное выражение и ответ эквивалентны (механизм equivalent)
let private certEquivalence (session: Env) (show: LispValue -> string) (originals: LispValue list) (result: LispValue) : CertificateEntry =
    if (findUnevaluated result).IsSome then certSkipped "equivalence" "в ответе есть невычисленная форма — проверять нечего"
    else
        let attempt (orig: LispValue) =
            let r = checkEquivalentFull session orig result []
            let head = [ "original", DStr (show orig); "result", DStr (show result) ]
            match r.Verdict with
            | "true" -> certOf "equivalence" "true" ("символьно: " + r.Method) head
            | "false" ->
                certOf "equivalence" "false" "численно: значения различаются в пробной точке"
                    (head @ [ "counterexample", DObj [ "point", DObj (r.Point |> List.map (fun (s, v) -> s, DStr v))
                                                       "original", DStr r.ValA; "result", DStr r.ValB ] ])
            | _ when r.Valid > 0 ->
                certOf "equivalence" "numeric" $"численно: совпадают в {r.Valid} пробных точках (символьно не доказано)" head
            | _ -> certOf "equivalence" "skipped" "нет" (head @ [ "reason", DStr r.Why ])
        bestCert originals attempt

// Контрпример equivalent: точное подтверждение — подстановка рациональной точки в оба выражения даёт различные числа
let private certCounterexample (session: Env) (show: LispValue -> string) (a: LispValue) (b: LispValue) (r: EquivResult) : CertificateEntry =
    let detail =
        [ "point", DObj (r.Point |> List.map (fun (s, v) -> s, DStr v)); "first", DStr r.ValA; "second", DStr r.ValB ]
    let exact =
        try
            let pt = r.Point |> List.map (fun (s, v) -> LispList [ LispSym "="; LispSym s; (match readAll v with [ x ] -> x | _ -> LispSym v) ])
            let sub (e: LispValue) = simplify (lispCall session "subst" [ LispList pt; e ])
            match sub a, sub b with
            | (LispInteger _ | LispRational _ as x), (LispInteger _ | LispRational _ as y) when prettyPrint x <> prettyPrint y ->
                Some (show x, show y)
            | _ -> None
        with _ when not Cancel.requested -> None
    match exact with
    | Some (x, y) ->
        certOf "counterexample" "true" "точная подстановка рациональной точки: значения различаются"
            ([ "point", DObj (r.Point |> List.map (fun (s, v) -> s, DStr v)); "first", DStr x; "second", DStr y ])
    | None -> certOf "counterexample" "numeric" "вычисление в пробной точке (числа с плавающей точкой)" detail

// LEAN.L1: сертификат Lean — текст .lean и статус приёма результатов (lean-certificate в lib\lean\emit.lisp).
// Генератор целиком на Lisp; здесь только вызов и раскладка alist'а в detail.
let private certLean (session: Env) (f: LispValue) (var: string) (result: LispValue) : CertificateEntry =
    let q (x: LispValue) = LispList [ LispSym "quote"; x ]
    let conds = try lispCall session "conditions" [] with _ -> LispNil
    let res =
        try eval (LispList [ LispSym "lean-certificate"; q f; q result; q (LispSym var); q conds ]) session
        with ex -> LispList [ LispSym "unsupported"; LispStr ("ошибка генератора: " + plainErrorMessage ex) ]
    let unsupported (why: string) =
        certOf "lean" "skipped" ("Lean: не переводится — " + why)
            [ "lean", DObj [ "status", DStr "unsupported"; "reason", DStr why ] ]
    match res with
    | LispList (LispSym "unsupported" :: LispStr why :: _) -> unsupported why
    | LispList pairs when not pairs.IsEmpty ->
        let field (name: string) =
            match lispCall session "assoc" [ LispSym name; res ] with
            | LispPair (_, v) -> v
            | LispList [ _; v ] -> v
            | _ -> LispSym ""
        let textOf (name: string) =
            match field name with
            | LispStr s -> s
            | other -> prettyPrint other
        let status = textOf "status"
        let source = textOf "source"
        if source = "" then unsupported (textOf "reason")
        else
            let verified = if status = "passed" then "true" else "skipped"
            let methodName =
                match status with
                | "passed" -> "Lean: файл скомпилирован, sorry и лишних аксиом нет"
                | "failed" -> "Lean: не доказано автоматически (ответ не опровергнут)"
                | "timeout" -> "Lean: проверка не уложилась в лимит"
                | "generated" -> "Lean: .lean сгенерирован, проверка не запускалась"
                | _ -> "Lean: результата проверки нет (not-run)"
            certOf "lean" verified methodName
                [ "lean_source", DStr source
                  "lean",
                  DObj [ "status", DStr status; "file", DStr (textOf "file"); "lemma", DStr (textOf "lemma")
                         "toolchain", DStr (textOf "toolchain"); "log", DStr (textOf "log") ] ]
    | _ -> unsupported "генератор вернул неожиданное значение"

// Ошибка протокола (неверный запрос): status error, без стека
exception ProtocolError of string

let private protocolError (msg: string) : 'a = raise (ProtocolError msg)

// Обрабатываем один JSON-запрос → ToolResponse
let handleRequest (session: Env) (json: string) : ToolResponse =
    let sw = Stopwatch.StartNew()
    let output = ref ""
    let mutable isMath = false
    let finish (r: ToolResponse) =
        { r with TimingMs = sw.ElapsedMilliseconds
                 Assumptions = assumptionsOf session
                 Output = if isMath then Some output.Value else r.Output }
    // Подшаг 22.4: декларации доменов и прочее состояние — текущей сессии (простые операции идут в F# без eval)
    ActiveSession.Env <- session
    // Прерывание (флаг Cancel поднят сторожем McpHost): ответ timeout; флаг опускается здесь — дальше в запросе
    // вычисляются assumptions (eval в сессии)
    let interrupted (r: string) =
        Cancel.clear ()
        finish { empty Timeout with
                   Note = Some ("вычисление прервано: " + r + "; сессия сохранена и готова к следующему вызову")
                   Error = Some ("Прервано: " + r); Stack = Some []; TimedOut = true }
    try
        let root = JsonDocument.Parse(json).RootElement
        let strProp (name: string) : string option =
            let mutable p = Unchecked.defaultof<JsonElement>
            if root.TryGetProperty(name, &p) && p.ValueKind = JsonValueKind.String then Some (p.GetString()) else None
        // Шаг 20: поля для series/limit: "point" (строка, по умолчанию 0), "order" (число, по умолчанию 6), "side" (plus|minus)
        let order =
            let mutable p = Unchecked.defaultof<JsonElement>
            if root.TryGetProperty("order", &p) && p.ValueKind = JsonValueKind.Number then p.GetInt32() else 6
        // Шаг 22.1: "steps": none (по умолчанию) | brief | full — журнал шагов StepLog за время запроса.
        // Шаг S.1: brief — главные шаги верхнего уровня; full — дерево (глубина 8, ≤ 200 узлов); trace — full и шаги
        // упрощателя (level detail)
        let stepsDetail =
            match strProp "steps" with
            | None | Some "none" -> None
            | Some s ->
                match StepLog.tryParseDetail s with
                | Some d -> Some d
                | None -> protocolError $"Неизвестное значение steps: {s} (ожидается none | brief | full | trace | attempts)"
        let wantSteps = stepsDetail.IsSome
        // Шаг S.5: "lang": ru (по умолчанию) | en — язык заголовков и пояснений шагов (rule не переводится)
        let stepsLang =
            match strProp "lang" with
            | None -> "ru"
            | Some s when StepDict.isLang s -> s
            | Some s -> protocolError $"Неизвестное значение lang: {s} (ожидается ru | en)"
        let var () = match strProp "var" with Some v -> v | None -> protocolError "Не указана переменная (var)"
        let intProp (name: string) : int option =
            let mutable p = Unchecked.defaultof<JsonElement>
            if root.TryGetProperty(name, &p) && p.ValueKind = JsonValueKind.Number then Some (p.GetInt32()) else None
        // Шаг 22.3: "syntax": "lisp" (по умолчанию — прежнее поведение --json) | "math" — code/var/point/from/to
        // операций simplify/expand/factor/diff/integrate/solve/limit/series записаны на математическом языке.
        // В режиме math операция выполняется как вызов языка op(code, var, ...) (math-eval-tree): переменные и функции
        // языка из сессии подставляются, pretty — в синтаксисе языка, output — вывод print, ошибка — без стека Lisp
        let mathSyntax =
            match strProp "syntax" with
            | None | Some "lisp" -> false
            | Some "math" -> true
            | Some other -> protocolError $"Неизвестное значение syntax: {other} (ожидается math | lisp)"
        let mathOp (op: string) (code: string) : Computed =
            isMath <- true
            let parse (what: string) (s: string) =
                try MathReader.mathParse s
                with ex -> protocolError $"{op}: не удалось разобрать {what} «{s}»: {ex.Message}"
            let need (name: string) = match strProp name with Some v -> parse name v | None -> protocolError $"Не указано поле {name}"
            let opt (name: string) = strProp name |> Option.map (parse name) |> Option.toList
            let args =
                match op with
                | "simplify" | "expand" | "factor" | "together" -> []
                | "apart" -> [ need "var" ]
                | "groebner" -> need "var" :: (strProp "order" |> Option.map LispSym |> Option.toList)
                | "diff" -> need "var" :: (intProp "order" |> Option.map (fun n -> LispInteger (bigint n)) |> Option.toList)
                | "integrate" ->
                    match strProp "from", strProp "to" with
                    | Some _, None | None, Some _ -> protocolError "integrate: границы from и to указываются вместе"
                    | _ -> need "var" :: (opt "from" @ opt "to")
                | "solve" -> [ need "var" ]
                | "sum" ->
                    // шаг 21l.7: sum(e, k, from, to); from по умолчанию 0, to обязательна
                    match strProp "to" with
                    | None -> protocolError "sum: не указана верхняя граница (to)"
                    | Some _ -> [ need "var"; defaultArg (strProp "from" |> Option.map (parse "from")) (LispInteger 0I); need "to" ]
                | "limit" -> [ need "var"; need "point" ] @ (strProp "side" |> Option.map LispSym |> Option.toList)
                | "series" -> [ need "var"; defaultArg (strProp "point" |> Option.map (parse "point")) (LispInteger 0I)
                                LispInteger (bigint order) ]
                | _ -> protocolError $"Операция {op} не поддерживает syntax: math"
            let ast = LispList (LispSym op :: parse "code" code :: args)
            let v = withCapturedOutput session output (fun () -> evalMathTree session ast)
            { Values = [v]; LastForm = Some ast; Show = mathPrintLang; Output = None; Note = None }
        // программа математического языка (op math; декларации declare/undeclare сводятся к ней)
        let runMathProgram (c: string) : Computed =
            isMath <- true
            let asts = MathReader.mathParseProgramFrom "<json>" c   // ошибка разбора — до выполнения, печатать нечего
            let values = withCapturedOutput session output (fun () -> asts |> List.map (evalMathTree session))
            { Values = values; LastForm = List.tryLast asts; Show = mathPrintLang; Output = None; Note = None }
        let identifier (what: string) (s: string) =
            if not (Text.RegularExpressions.Regex.IsMatch(s, @"^[\p{L}_][\p{L}\p{N}_']*$")) then
                protocolError $"{what}: ожидается имя символа (буквы, цифры, _), получено «{s}»"
        // Подшаг 22.5: сторона equivalent — значение выражения (math: с подстановкой переменных и функций сессии)
        let equivSide (what: string) (s: string) : LispValue =
            if mathSyntax then
                isMath <- true
                let ast = try MathReader.mathParse s with ex -> protocolError $"equivalent: не удалось разобрать {what} «{s}»: {ex.Message}"
                withCapturedOutput session output (fun () -> evalMathTree session ast)
            else parseOne "equivalent" s
        let equivVars () : string list =
            match strProp "var" with
            | None -> []
            | Some s ->
                let v = if mathSyntax then MathReader.mathParse s else parseOne "equivalent (vars)" s
                let acc = Collections.Generic.HashSet<string>()
                let rec go (x: LispValue) =
                    match x with
                    | LispSym n when n <> "vector" && n <> "list" -> acc.Add n |> ignore
                    | LispList xs -> List.iter go xs
                    | LispVector xs -> Array.iter go xs
                    | _ -> ()
                go v
                List.ofSeq acc
        // Подшаг 22.6: certificate: true — в ответе сертификат (проверка независимым путём); по умолчанию false.
        // LEAN.L1: certificate: "lean" — вместо проверки сгенерировать .lean (сертификат kind = lean, status = generated)
        let certMode =
            let mutable p = Unchecked.defaultof<JsonElement>
            if root.TryGetProperty("certificate", &p) then
                match p.ValueKind with
                | JsonValueKind.True -> CertDefault
                | JsonValueKind.False | JsonValueKind.Null -> CertNone
                | JsonValueKind.String when p.GetString() = "true" -> CertDefault
                | JsonValueKind.String when p.GetString() = "false" -> CertNone
                | JsonValueKind.String when p.GetString() = "lean" -> CertLean
                | _ -> protocolError "Неизвестное значение certificate (ожидается true | false | \"lean\")"
            else CertNone
        let equivOutcome : (EquivResult * LispValue * LispValue) option ref = ref None
        let compute () : Computed =
            match strProp "op", strProp "code" with
            | None, _ -> protocolError "Не указана операция (op)"
            | Some "declarations", _ ->
                // действующие декларации сессии: по строке «x ∈ D» на ограничение (то же — в поле assumptions)
                let entries =
                    match eval (LispList [LispSym "declarations"]) session with
                    | LispList es ->
                        es |> List.collect (fun e ->
                            match e with
                            | LispList (x :: ds) -> ds |> List.map (fun d -> LispList [LispSym ":in"; x; d])
                            | _ -> [])
                    | _ -> []
                { Values = entries; LastForm = None; Show = mathPrintLang; Output = None
                  Note = (if entries.IsEmpty then Some "декларации не заданы (необъявленный символ — элемент ℂ)" else None) }
            | Some _, None -> protocolError "Не указан код (code)"
            | Some ("simplify" | "expand" | "factor" | "diff" | "integrate" | "solve" | "limit" | "series" | "together" | "apart" | "groebner" | "sum" as op), Some c
                when mathSyntax -> mathOp op c
            | Some "together", Some c -> let v, f = callIn session "together" [parseOne "together" c] in computed v (Some f)
            | Some "apart", Some c -> let v, f = callIn session "apart" [parseOne "apart" c; parseOne "apart (var)" (var ())] in computed v (Some f)
            | Some "groebner", Some c ->
                let ord = strProp "order" |> Option.map LispSym |> Option.toList
                let v, f = callIn session "groebner" ([ parseOne "groebner" c; parseOne "groebner (vars)" (var ()) ] @ ord)
                computed v (Some f)
            | Some "declare", Some c ->
                identifier "declare" c
                match strProp "domain" with
                | None -> protocolError "declare: не указан домен (domain)"
                | Some d when d.Contains ";" || d.Contains "\n" -> protocolError "declare: домен — одно выражение (ℝ, ℤ, positive, (0, ∞), [0, 1])"
                | Some d -> runMathProgram $"{c} :∈ {d}"
            | Some "undeclare", Some c -> identifier "undeclare" c; runMathProgram $"{c} :∈"
            | Some "equivalent", Some c ->
                let other = match strProp "other" with Some o -> o | None -> protocolError "equivalent: не указано второе выражение (other)"
                let a = equivSide "первое выражение" c
                let b = equivSide "второе выражение" other
                let r = checkEquivalentFull session a b (equivVars ())
                equivOutcome.Value <- Some (r, a, b)
                { Values = [LispSym r.Verdict]; LastForm = None; Show = mathPrintLang; Output = None; Note = Some r.Why }
            | Some "solve", Some c -> let v, f = callIn session "solve" [parseOne "solve" c; parseOne "solve (var)" (var ())] in computed v (Some f)
            | Some "sum", Some c ->
                // шаг 21l.7: символьная сумма (суммирование каскадом: Фаульхабер → Госпер → Абрамов → Цайльбергер+rsolve)
                let lo = match strProp "from" with Some a -> parseOne "sum (from)" a | None -> LispInteger 0I
                match strProp "to" with
                | None -> protocolError "sum: не указана верхняя граница (to)"
                | Some b -> let v, f = callIn session "sum-symbolic" [parseOne "sum" c; parseOne "sum (var)" (var ()); lo; parseOne "sum (to)" b] in computed v (Some f)
            | Some "series", Some c ->
                let v, f = valSeries session (var ()) c (defaultArg (strProp "point") "0") order
                computed v (Some f)
            | Some "limit", Some c ->
                let x = var ()
                match strProp "point" with
                | Some pt -> let v, f = valLimit session x c pt (strProp "side") in computed v (Some f)
                | None -> protocolError "Не указана точка (point)"
            | Some "eval", Some c ->
                // Шаг 21d: формы помнят позицию (псевдофайл «<json>») — кадры стека ошибки показывают «<json>:строка»
                let forms = readAllFrom "<json>" c
                { Values = forms |> List.map (fun e -> eval e session); LastForm = List.tryLast forms; Show = mathPrint; Output = None; Note = None }
            | Some "simplify", Some c -> computed (CasBuiltins.simplifyRecorded (parseOne "simplify" c)) None
            | Some "diff", Some c ->
                let x = var ()
                let n = defaultArg (intProp "order") 1
                if n < 0 then protocolError "diff: порядок (order) — неотрицательное целое"
                let d = List.fold (fun e _ -> Differentiate.diff x e |> Simplify.simplify) (parseOne "diff" c) [1 .. n]
                computed d None
            | Some "integrate", Some c ->
                match strProp "from", strProp "to" with
                | Some a, Some b ->
                    let v, f = callIn session "integrate" [parseOne "integrate" c; LispSym (var ()); parseOne "from" a; parseOne "to" b]
                    computed v (Some f)
                | None, None -> let v, f = valIntegrate session (var ()) c in computed v (Some f)
                | _ -> protocolError "integrate: границы from и to указываются вместе"
            | Some "expand", Some c -> computed (Expand.expand (parseOne "expand" c)) None
            | Some "factor", Some c -> computed (Factor.factor (parseOne "factor" c)) None
            | Some "parse", Some c -> computed (MathReader.mathParse c) None
            | Some "math", Some c -> runMathProgram c
            // Шаг LA.4: линейная алгебра — жорданова форма, exp(A·t), символьная степень, f(A)
            // code — матрица [[..,..],..] (или выражение); fn: jordan_form | jordan_blocks | mat_exp | mat_power | mat_fn |
            // diagonalize | is_diagonalizable | eigenvalues | eigenvectors; var — переменная t/n; func — функция для mat_fn
            | Some "linear-algebra", Some c ->
                let mat = let m = try MathReader.mathParse c with ex -> protocolError $"linear-algebra: не удалось разобрать матрицу «{c}»: {ex.Message}" in mVecToNested m
                let fn = match strProp "fn" with Some f -> f | None -> protocolError "linear-algebra: не указана операция (fn)"
                let larg = match strProp "var" with Some v -> [ LispSym v ] | None -> []
                let farg = match strProp "func" with Some f -> [ try MathReader.mathParse f with ex -> protocolError $"linear-algebra: не удалось разобрать func «{f}»: {ex.Message}" ] | None -> []
                let target =
                    match fn with
                    | "jordan_form" -> "math-jordan-form"
                    | "jordan_blocks" -> "math-jordan-blocks"
                    | "mat_exp" -> "math-mat-exp"
                    | "mat_power" -> "math-mat-power"
                    | "mat_fn" -> "math-mat-fn"
                    | "diagonalize" -> "math-diagonalize"
                    | "is_diagonalizable" -> "math-diagonalizable?"
                    | "eigenvalues" -> "eigenvalues"
                    | "eigenvectors" -> "eigenvectors"
                    | other -> protocolError $"linear-algebra: неизвестная операция fn: {other}"
                let args =
                    match fn with
                    | "mat_fn" -> farg @ [ mat ]                                        // f(A)
                    | "mat_exp" -> [ mat ] @ larg                                       // exp(A·t)
                    | "mat_power" -> [ mat; (match larg with [v] -> v | _ -> LispSym "n") ] // A^n: var (по умолчанию n)
                    | _ -> [ mat ]
                let v, f = callIn session target args
                computed v (Some f)
            // Шаг LP.3: линейное и целочисленное программирование — симплекс с сертификатами,
            // целочисленное — ветви и границы. code — целевая функция c (вектор), A/b/relations —
            // ограничения; integer — вектор "int"/"bin"/"free" по переменным (при отсутствии — обычное ЛП)
            | Some "linear-programming", Some c ->
                let mp (what: string) (s: string) : LispValue =
                    try withCapturedOutput session output (fun () -> evalMathTree session (MathReader.mathParse s))
                    with ex -> protocolError $"linear-programming: не удалось разобрать {what} «{s}»: {ex.Message}"
                let dir = match strProp "dir" with Some d when d = "max" || d = "min" -> d | Some d -> protocolError $"linear-programming: dir — max | min, получено «{d}»" | None -> protocolError "linear-programming: не указано направление (dir: max | min)"
                let cv = mp "code (целевая функция)" c
                let field (what: string) (name: string) = match strProp name with Some s -> s | None -> protocolError $"Не указано поле {name} ({what})"
                let Av = mp "A (матрица ограничений)" (field "матрица ограничений" "A")
                let bv = mp "b (правые части)" (field "правые части" "b")
                let relv = mp "relations" (defaultArg (strProp "relations") "[\"<=\"]")
                let isIlp = strProp "integer" |> Option.isSome
                let intv = match strProp "integer" with Some s -> mp "integer" s | None -> LispList []
                let form =
                    let q (x: LispValue) = LispList [LispSym "quote"; x]
                    if isIlp then LispList [ LispSym "math-ilp-solve"; q (LispSym dir); q cv; q Av; q bv; q relv; q intv ]
                    else LispList [ LispSym "math-lp-solve"; q (LispSym dir); q cv; q Av; q bv; q relv ]
                let v = withCapturedOutput session output (fun () -> eval form session)
                { Values = [v]; LastForm = Some form; Show = prettyPrint; Output = None; Note = None }
            | Some other, _ -> protocolError $"Неизвестная операция: {other}"
        // исходное выражение для сертификата: как записано (математический язык — разбор без вычисления) и, если язык
        // подставляет переменные/функции сессии, ещё и вычисленное; ответ сверяется с первым подошедшим вариантом
        let rawParse (s: string) : LispValue = if mathSyntax then MathReader.mathParse s else parseOne "certificate" s
        let certCandidates (s: string) : LispValue list =
            let raw = rawParse s
            if mathSyntax then
                let saved = output.Value
                let ev =
                    try Some (withCapturedOutput session output (fun () -> evalMathTree session raw))
                    with _ when not Cancel.requested -> None
                output.Value <- saved
                match ev with
                | Some e when prettyPrint e <> prettyPrint raw -> [ raw; e ]
                | _ -> [ raw ]
            else [ raw ]
        let certKind (op: string) : string =
            match op with
            | "integrate" -> "derivative"
            | "solve" -> "substitution"
            | "groebner" -> "ideal_membership"
            | "simplify" | "expand" | "factor" | "together" | "apart" | "equivalent" -> "equivalence"
            | "sum" -> "sum"
            | "linear-algebra" -> "linear_algebra"
            | "linear-programming" -> "linear_programming"
            | _ -> "none"
        // LEAN.L1: certificate: "lean" — отдельный путь (генерация .lean и приём статуса); обычные проверки не считаются
        let certificateLean (c: Computed) (status: Status) : CertificateEntry =
            let op = defaultArg (strProp "op") ""
            let need (name: string) = match strProp name with Some s -> s | None -> protocolError $"Не указано поле {name}"
            if op <> "integrate" then certSkipped "lean" "Lean-сертификат поддерживается только для integrate"
            elif status <> Answer then certSkipped "lean" "ответ не получен — генерировать .lean нечего"
            else
                match List.tryLast c.Values with
                | Some v -> certLean session (List.head (certCandidates (need "code"))) (need "var") v
                | None -> certSkipped "lean" "ответ не получен — генерировать .lean нечего"
        let certificateFor (c: Computed) (status: Status) (note: string option) : CertificateEntry =
            let op = defaultArg (strProp "op") ""
            let show = c.Show
            let kind = certKind op
            let need (name: string) = match strProp name with Some s -> s | None -> protocolError $"Не указано поле {name}"
            match List.tryLast c.Values with
            // Шаг LP.3: несовместность (NoSolution) — сертификат Фаркаша в ответе (infeasible y)
            | Some v when status = Answer || (status = NoSolution && op = "linear-programming") ->
                match op with
                | "integrate" ->
                    let limits = match strProp "from", strProp "to" with Some a, Some b -> Some (rawParse a, rawParse b) | _ -> None
                    certIntegrate session show (need "var") (certCandidates (need "code")) limits v
                | "solve" ->
                    let vars = rawParse (need "var")
                    bestCert (certCandidates (need "code")) (fun e -> certSolve session show e vars v)
                | "groebner" ->
                    let vars = rawParse (need "var")
                    bestCert (certCandidates (need "code")) (fun p -> certGroebner session show p vars (strProp "order") v)
                | "simplify" | "expand" | "factor" | "together" | "apart" ->
                    certEquivalence session show (certCandidates (need "code")) v
                | "equivalent" ->
                    match equivOutcome.Value with
                    | Some (r, a, b) when r.Verdict = "true" ->
                        certOf "equivalence" "true" ("символьно: " + r.Method)
                            [ "first", DStr (show a); "second", DStr (show b) ]
                    | Some (r, a, b) when r.Verdict = "false" -> certCounterexample session show a b r
                    | Some (r, _, _) -> certSkipped "none" ("ответ unknown: " + r.Why)
                    | None -> certSkipped "none" "проверка не выполнена"
                | "diff" -> certSkipped "none" "дифференцирование выполняется по правилам; независимой проверки нет"
                | "linear-algebra" ->
                    // шаг LA.4: проверки — внутри linalg (ошибка вместо ответа, если не прошли); у спектра и блоков независимой проверки нет
                    match strProp "fn" with
                    | Some ("jordan_form" | "diagonalize") -> certOf "linear_algebra" "true" "P·X·P⁻¹ = A и det P ≠ 0 (проверено в linalg)" [ "answer", DStr (show v) ]
                    | Some "eigenvectors" -> certOf "linear_algebra" "true" "A·v = λ·v для каждого вектора (проверено в linalg)" [ "answer", DStr (show v) ]
                    | Some "mat_exp" -> certOf "linear_algebra" "true" "d/dt E = A·E и E(0) = I (проверено в linalg)" [ "answer", DStr (show v) ]
                    | Some "mat_power" -> certOf "linear_algebra" "numeric" "совпадение с прямыми степенями в 7 точках n (проверено в linalg)" [ "answer", DStr (show v) ]
                    | Some "mat_fn" -> certOf "linear_algebra" "true" "f(A)·A = A·f(A) и f(A)·v = f(λ)·v (проверено в linalg)" [ "answer", DStr (show v) ]
                    | _ -> certSkipped "linear_algebra" "для спектра, блоков и признака диагонализуемости независимой проверки нет"
                | "linear-programming" ->
                    // Шаг LP.3: сертификат ЛП — lp-check (умножения и сравнения, независимо от решателя):
                    // optimal — допустимость + двойственные цены y (cᵀx = bᵀy); infeasible — лемма Фаркаша;
                    // unbounded — допустимая точка + луч d (cᵀd > 0). ILP — повторный счёт дерева ветвления
                    // (ilp-check, лимит узлов 100000).
                    let dir = defaultArg (strProp "dir") "max"
                    let mp (what: string) (s: string) : LispValue =
                        try withCapturedOutput session output (fun () -> evalMathTree session (MathReader.mathParse s))
                        with ex -> protocolError $"linear-programming: не удалось разобрать {what} «{s}»: {ex.Message}"
                    let field (name: string) = match strProp name with Some s -> s | None -> protocolError $"Не указано поле {name}"
                    let cv = mp "code" (need "code")
                    let Av = mp "A" (field "A")
                    let bv = mp "b" (field "b")
                    let relv = mp "relations" (defaultArg (strProp "relations") "[\"<=\"]")
                    let q (x: LispValue) = LispList [LispSym "quote"; x]
                    let checkForm =
                        let q (x: LispValue) = LispList [LispSym "quote"; x]
                        match strProp "integer" with
                        | Some isv ->
                            let intv = mp "integer" isv
                            LispList [ LispSym "math-ilp-check"; q v; q (LispSym dir); q cv; q Av; q bv; q relv; q intv ]
                        | None -> LispList [ LispSym "math-lp-check"; q v; q (LispSym dir); q cv; q Av; q bv; q relv ]
                    let ilp = strProp "integer" |> Option.isSome
                    let methodText =
                        if ilp then
                            match v with
                            | LispList (LispSym "optimal" :: _) -> "целочисленный оптимум: точка целая и допустима, оптимальность — повторный счёт дерева ветвления (ilp-check)"
                            | LispList (LispSym "infeasible" :: _) -> "целочисленных допустимых точек нет: повторный счёт дерева ветвления (ilp-check)"
                            | _ -> "сертификат проверен повторным счётом (ilp-check)"
                        else
                            match v with
                            | LispList (LispSym "optimal" :: _) -> "оптимум: Ax ∘ b, x ≥ 0, двойственная допустимость y, cᵀx = value = bᵀy (проверено lp-check)"
                            | LispList (LispSym "infeasible" :: _) -> "несовместность: сертификат леммы Фаркаша — знаки y, yᵀA ≤ 0, yᵀb < 0 (проверено lp-check)"
                            | LispList (LispSym "unbounded" :: _) -> "неограниченность: допустимая x и луч d ≥ 0, Ad ∘ 0, cᵀd > 0 (проверено lp-check)"
                            | _ -> "сертификат проверен повторным счётом (lp-check)"
                    let ok =
                        let r =
                            try eval checkForm session
                            with _ -> LispBool false
                        match r with
                        | LispBool b -> b
                        | _ -> false
                    match ok, v with
                    | true, LispList (LispSym "unknown" :: _) ->
                        certOf "linear_programming" "skipped"
                            "лимит узлов ветвления: ответ unknown, лучшая найденная точка и граница не обязательно оптимальны"
                            [ "answer", DStr (show v) ]
                    | true, _ -> certOf "linear_programming" "true" methodText [ "answer", DStr (show v) ]
                    | false, _ -> certSkipped "linear_programming" "сертификат не прошёл независимую проверку (lp-check/ilp-check)"
                | "sum" ->
                    // шаг 21l.7: сумма — проверка оракулом sum-check (прямая сумма в пробных точках);
                    // ответ-рекуррентность — recurrence-check-sum (рекуррентность против прямых сумм)
                    let k = LispSym (need "var")
                    let lo = match strProp "from" with Some a -> rawParse a | None -> LispInteger 0I
                    let hi = rawParse (need "to")
                    if isRecurrence v then
                        match firstSym hi with
                        | Some n ->
                            let body = rawParse (need "code")
                            let q (x: LispValue) = LispList [LispSym "quote"; x]
                            let r =
                                try eval (LispList [ LispSym "recurrence-check-sum"; q v; q body; q k; q (LispSym n) ]) session with _ -> LispSym "unknown"
                            let ok = match r with LispBool b -> b | _ -> false
                            if ok then
                                certOf "recurrence" "true" "рекуррентность проверена прямыми суммами в начальных точках"
                                    [ "recurrence", DStr (show v); "method", DStr "recurrence-check-sum: прямые суммы" ]
                            else certSkipped "recurrence" "рекуррентность не прошла численную проверку прямыми суммами"
                        | None -> certSkipped "recurrence" "верхняя граница не содержит переменной n — проверить рекуррентность нельзя"
                    else
                        let body = rawParse (need "code")
                        let how =
                            let q (x: LispValue) = LispList [LispSym "quote"; x]
                            try eval (LispList [ LispSym "sum-check-how"; q v; q body; q k; q lo; q hi ]) session
                            with ex -> raise (failwith ("sum-check-how: " + ex.Message))
                        let numeric = match how with LispSym "numeric" -> true | _ -> false
                        if numeric then
                            certOf "sum" "numeric" "прямая сумма в целых точках совпала с ответом"
                                [ "answer", DStr (show v); "method", DStr "sum-check: numeric" ]
                        else certSkipped "sum" "численная проверка прямой суммой не выполнена (skip)"
                | "limit" | "series" -> certSkipped "none" "для пределов и рядов проверка ответа не реализована"
                | _ -> certSkipped "none" "сертификат строится для операций integrate, solve, simplify, expand, factor, together, apart, groebner, equivalent"
            | Some v when status = Nonelementary ->
                // шаг 21k.4: утверждение «первообразной нет» доказано алгоритмом Риша; независимой проверки у него нет
                certOf "nonelementary" "skipped" "алгоритм Риша (теорема Лиувилля): независимой проверки нет"
                    [ "integral", DStr (show v); "reason", DStr (defaultArg note "") ]
            | _ ->
                certSkipped kind (match note with Some n -> "ответ не получен — проверять нечего (" + n + ")" | None -> "ответ не получен — проверять нечего")
        // проверка входит в общий timeout_s: не уложилась — verified "timeout", ответ не теряется
        let buildCertificate (mode: CertRequest) (c: Computed) (status: Status) (note: string option) : CertificateEntry =
            let timeoutCert () =
                Cancel.clear ()
                let kind = if mode = CertLean then "lean" else certKind (defaultArg (strProp "op") "")
                certOf kind "timeout" "нет"
                    [ "reason", DStr "проверка не уложилась в timeout_s; ответ получен, но не проверен" ]
            try
                let r = match mode with
                        | CertLean -> certificateLean c status
                        | _ -> certificateFor c status note
                if Cancel.requested then timeoutCert () else r
            with
            | _ when Cancel.requested -> timeoutCert ()
            | ex -> certSkipped "none" ("проверка не выполнена: " + plainErrorMessage ex)
        ConditionLog.Conditions.Clear()
        // Шаг D3c: буфер проглоченных ошибок начинается с запроса (LISP_DEBUG=1/set-debug! включён заранее)
        Debug.swallowedClear ()
        let startSteps = StepLog.Journal.Steps.Length
        // Шаг D2a: steps: attempts — журнал ПОПЫТОК (неудачные рамки with-step с причиной и временем; повторы ×N)
        let c, steps, attempts, stepsNote, stepsWarnings =
            match stepsDetail with
            | Some StepLog.Attempts ->
                let c, tree, note = AlgoBuiltins.captureAttemptsRaw stepsLang compute
                c, [], tree, note, []
            | Some d ->
                let c, steps, note, w = AlgoBuiltins.captureStepsLang stepsLang (Some d) compute
                c, steps, [], note, w
            | None when StepLog.Journal.Enabled ->
                // журнал включён в сессии (step-log-on) — шаги, записанные за время запроса (как full)
                let c = compute ()
                let sel = StepLog.select StepLog.Full (List.skip (min startSteps StepLog.Journal.Steps.Length) StepLog.Journal.Steps)
                let localized, missing = StepDict.localize stepsLang sel.Steps
                c, localized, [], StepDict.truncationNote stepsLang sel, (StepDict.missingWarning missing |> Option.toList)
            | None -> compute (), [], [], None, []
        // флаг отмены поднят, а вычисление вернуло значение (исключение отмены проглотил catch-all код) — значение
        // может быть неполным: ответ timeout
        if Cancel.requested then raise (Cancel.CancelledException Cancel.reason)
        let status, note, warnings =
            match List.tryLast c.Values with
            | Some v -> classify session c.LastForm v
            | None -> Answer, None, []
        let note = match c.Note with Some _ -> c.Note | None -> note
        // сертификат (по запросу): статус не меняет; verified = false — тревожный сигнал в warnings
        let certificate = if certMode <> CertNone then Some (buildCertificate certMode c status note) else None
        let warnings =
            match certificate with
            | Some cc when cc.Verified = "false" ->
                warnings @ [ $"ответ не прошёл проверку (certificate.kind = {cc.Kind}, verified = false): {cc.Method}" ]
            | _ -> warnings
        let warnings = match stepsNote with Some n -> warnings @ [ n ] | None -> warnings
        let warnings = warnings @ stepsWarnings
        // Шаг D2a: steps: attempts — вместо шагов выдаётся дерево попыток (level = "attempt")
        let stepsField =
            if not attempts.IsEmpty then Some (List.map (attemptEntryLang stepsLang) attempts)
            elif wantSteps || not steps.IsEmpty then Some (List.map (stepEntryLang stepsLang) steps)
            else None
        // Шаг D3c: ошибки, проглоченные try с обработчиком (в отладочном режиме — в warnings ответа)
        let warnings = warnings @ (Debug.swallowed () |> List.map (fun m -> "проглоченная ошибка (try): " + m))
        let result, pretty =
            match c.Values with
            | [] -> "nil", "nil"
            | vs -> String.concat "\n" (List.map prettyPrint vs), String.concat "\n" (List.map c.Show vs)
        // Шаг TEX.1: LaTeX-запись ответа (для KaTeX в браузере и LLM)
        let latex =
            match c.Values with
            | [] -> "nil"
            | vs -> String.concat "\n" (List.map LatexPrinter.latexPrint vs)
        finish
            { empty status with
                Result = Some result; Pretty = Some pretty; Latex = Some latex; Note = note; Warnings = warnings; Certificate = certificate
                Conditions = conditionEntries ()
                Steps = stepsField }
    with
    | ProtocolError msg -> finish { empty Error with Error = Some msg; Stack = Some [] }
    | _ when Cancel.requested -> interrupted Cancel.reason
    | ex ->
        recordError session ex
        let status, note = classifyError ex
        // математический режим — только сообщение (без стека Lisp); Шаг 15b: иначе stack — кадры стека Lisp
        // (самый глубокий первый), для не-Lisp ошибок пуст
        let msg, stack =
            match Debug.wrap ex with
            | LispError (msg, stack, _) when not isMath -> msg, Debug.frameLines stack |> List.map (fun l -> l.TrimStart())
            | LispError (msg, _, _) -> msg, []
            | other -> other.Message, []
        finish { empty status with Note = note; Error = Some msg; Stack = Some stack; TimedOut = (status = Timeout) }

let handleJsonRequest (session: Env) (json: string) : string = toJson (handleRequest session json)

// CLI-режим: читаем JSON-запросы из stdin (по одной строке), пишем ответы в stdout
let runCliJsonLoop () : unit =
    let session = makeSession ()
    let mutable running = true
    while running do
        let line = Console.ReadLine()
        if line = null then
            running <- false
        elif line.Trim() = "exit" then
            running <- false
        elif String.IsNullOrWhiteSpace line then
            ()
        else
            Console.WriteLine(handleJsonRequest session line)
