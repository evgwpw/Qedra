// Builtins единого контракта алгоритмов (шаг 21h'): счётчики, переключатели алгоритмов, журнал шагов.
// Механизмы — в Cas.Algebra (AlgoStats, Algorithms, StepLog, Outcome); здесь только разбор аргументов и представление в Lisp.
//   (algo-stats)  (algo-stats 'группа)  — значения счётчиков текущего потока: ((группа (счётчик значение) ...) ...)
//   (algo-stats-reset)  (algo-stats-reset 'группа)
//   (algorithms) — ((имя текущее (допустимые ...)) ...);  (algorithm 'gcd) — текущее значение;
//   (set-algorithm 'gcd 'zippel) — установить (возвращает прежнее значение); начальное значение — переменная среды LISP_GCD
//   (step-log-on) (step-log-off) (step-log-enabled?) (step-log-clear) (step-log)
//   (record-step 'rule "заголовок" "пояснение" до после [уровень]) — шаг S.1; старая форма из 4 аргументов работает
//   (call-with-step 'rule "заголовок" до thunk [пояснение уровень после-f]) — рамка (макрос with-step — lib\steps.lisp)
//   (capture-step-log thunk [уровень]) — выполнить thunk с включённым чистым журналом: (результат шаги [пометка])
//   (steps-text шаги [пометка]) — дерево шагов строкой
//   (record-condition условие "причина") (conditions) (conditions-clear) (capture-conditions thunk) — канал условий (ConditionLog)
module AlgoBuiltins

open System
open Types
open Builtins

let private nameOf (who: string) (v: LispValue) : string =
    match v with
    | LispSym s | LispStr s -> s
    | other -> failwithf "%s: ожидался символ или строка, получено %s" who (Printer.prettyPrint other)

let private sym (s: string) : LispValue = LispSym s

// Значение для журнала → Lisp: выражение Lisp как есть, прочее (например, многочлен MPoly) — строкой
let private payload (o: obj) : LispValue =
    match o with
    | :? LispValue as v -> v
    | null -> LispNil
    | other -> LispStr (sprintf "%A" other)

// --- Шаг S.1: шаги как данные Lisp, печать дерева, захват с уровнем ---
// Шаг в Lisp — список (rule title comment before after level children omitted): rule и level — символы
// (groebner-basis, main | detail), title/comment — строки, children — список шагов, omitted — число скрытых обрезкой
// вложенных шагов. Доступ — step-rule, step-title, ... (lib\steps.lisp)

let stepToLispValue (s: StepLog.Step) : LispValue =
    let rec conv (s: StepLog.Step) =
        LispList [ LispSym s.Rule; LispStr s.Title; LispStr s.Comment; payload s.Before; payload s.After
                   LispSym (StepLog.levelName s.Level); LispList (List.map conv s.Children); LispInteger (bigint s.Omitted) ]
    conv s

let private stepToLisp = stepToLispValue

let private listItems (who: string) (v: LispValue) : LispValue list =
    match v with
    | LispList xs -> xs
    | LispNil -> []
    | other -> failwithf "%s: ожидался список шагов, получено %s" who (Printer.prettyPrint other)

// Обратное преобразование (для steps-text над данными): список из 8 элементов (или 7 — без omitted)
let rec stepOfLisp (who: string) (v: LispValue) : StepLog.Step =
    let text (x: LispValue) = match x with LispStr s | LispSym s -> s | LispNil -> "" | o -> Printer.prettyPrint o
    match v with
    | LispList (rule :: title :: comment :: before :: after :: level :: children :: rest) ->
        { Rule = text rule; Title = text title; Comment = text comment; Before = box before; After = box after
          Level = (match level with LispSym "detail" | LispStr "detail" -> StepLog.Detail | _ -> StepLog.Main)
          Children = listItems who children |> List.map (stepOfLisp who)
          Omitted = (match rest with LispInteger n :: _ -> int n | _ -> 0) }
    | other -> failwithf "%s: шаг — список (rule title comment before after level children omitted), получено %s"
                        who (Printer.prettyPrint other)

// Запись значения шага на входном языке: (list a b) и списки выражений — вектором [a, b]
let rec payloadText (v: LispValue) : string =
    match v with
    | LispList (LispSym "list" :: xs) -> "[" + (xs |> List.map payloadText |> String.concat ", ") + "]"
    | LispList ((LispList _ :: _) as xs) -> "[" + (xs |> List.map payloadText |> String.concat ", ") + "]"
    | LispNil | LispList [] -> ""
    | other -> MathPrinter.mathPrintLang other

// Шаг S.5: язык шагов ("ru" | "en"); по-русски совокупность решений печатается «x = 2 или x = 3», по-английски — «or»
let showPayloadLang (lang: string) (o: obj) : string =
    match o with
    | :? LispValue as v -> if lang = "en" then payloadText v else MathPrinter.withOrWord "или" (fun () -> payloadText v)
    | null -> ""
    | other -> sprintf "%A" other

let showPayload (o: obj) : string = showPayloadLang "ru" o

// Печать дерева шагов: «1. Заголовок: до ⇒ после», пояснение — строкой ниже, вложенные — «1.1», отступ 3 пробела
// на уровень; обрезка помечается строкой «… скрыто шагов: N». Длинные выражения — до maxChars символов.
// Шаг S.5: lang = "en" — заголовки и пояснения переводятся словарём StepDict (шаги без перевода остаются русскими, о них
// сообщает последняя строка)
let stepsTextLang (lang: string) (steps0: StepLog.Step list) (note: string option) : string =
    let steps, missing = StepDict.localize lang steps0
    let showPayload = showPayloadLang lang
    let maxChars = 300
    let cut (s: string) = if s.Length > maxChars then s.Substring(0, maxChars) + " …" else s
    let sb = Text.StringBuilder()
    let line (s: string) = sb.Append(s).Append('\n') |> ignore
    let rec walk (indent: string) (prefix: string) (ss: StepLog.Step list) =
        ss |> List.iteri (fun i s ->
            let num = if prefix = "" then sprintf "%d." (i + 1) else sprintf "%s.%d" prefix (i + 1)
            let label = if s.Title <> "" then s.Title else s.Rule
            let b, a = cut (showPayload s.Before), cut (showPayload s.After)
            let body =
                match b, a with
                | "", "" -> ""
                | "", a -> ": " + a
                | b, "" -> ": " + b
                | b, a -> sprintf ": %s ⇒ %s" b a
            line (sprintf "%s%s %s%s" indent num label body)
            let sub = indent + String(' ', num.Length + 1)
            if s.Comment <> "" then line (sub + s.Comment)
            walk sub (num.TrimEnd('.')) s.Children
            if s.Omitted > 0 then line (sub + StepDict.omittedText lang s.Omitted))
    if List.isEmpty steps then line (StepDict.noStepsText lang)
    walk "" "" steps
    match note with
    | Some n -> line ("… " + n)
    | None -> ()
    match StepDict.missingWarning missing with
    | Some w -> line ("… " + w)
    | None -> ()
    sb.ToString().TrimEnd('\n')

let stepsText (steps: StepLog.Step list) (note: string option) : string = stepsTextLang "ru" steps note

// --- Шаг D2a: журнал попыток (attempts) ---

// Attempt → Lisp-значение (форма шага: rule title comment before after level children omitted):
// comment = «успех: пояснение» | «отказ: причина», after = до (Before), level = "attempt",
// omitted используется как Repeats (×N повтора при выдаче)
let attemptToLisp (a: StepLog.Attempt) : LispValue =
    let rec conv (x: StepLog.Attempt) =
        let status = if x.Ok then "успех: " + x.Reason else "отказ: " + x.Reason
        let repeats = if x.Repeats > 1 then sprintf " ×%d" x.Repeats else ""
        LispList [ LispSym x.Rule; LispStr x.Title; LispStr (status + repeats + sprintf " — %.1f мс" x.Ms)
                   payload x.Before; LispNil
                   LispSym "attempt"; LispList (List.map conv x.Children); LispInteger 0I ]
    conv a

// печать дерева попыток: «правило — успех/отказ: причина — N мс [×k]», отступ 2 пробела на уровень,
// вложенность — дети попытки; пометка об обрезке (selectAttempts) строкой в конце
let attemptsTextLang (lang: string) (tree: StepLog.Attempt list) (note: string option) : string =
    let sb = Text.StringBuilder()
    let line (s: string) = sb.Append(s).Append('\n') |> ignore
    let rec walk (indent: string) (ss: StepLog.Attempt list) =
        ss |> List.iter (fun a ->
            let status = if a.Ok then "успех" else "отказ"
            let label = if a.Title <> "" then a.Title else a.Rule
            let why = if a.Reason <> "" then ": " + a.Reason else ""
            let repeats = if a.Repeats > 1 then sprintf " ×%d" a.Repeats else ""
            line (sprintf "%s%s — %s%s%s — %.1f мс" indent label status why repeats a.Ms)
            walk (indent + "  ") a.Children)
    if List.isEmpty tree then line (StepDict.noStepsText lang)
    walk "" tree
    match note with
    | Some n -> line ("… " + n)
    | None -> ()
    sb.ToString().TrimEnd('\n')

// захват попыток: (результат, отобранное дерево, пометка об обрезке)
let captureAttemptsRaw (lang: string) (f: unit -> 'a) : 'a * StepLog.Attempt list * string option =
    let r, attempts = StepLog.Journal.CaptureAttempts f
    let sel = StepLog.selectAttempts attempts
    let note =
        if sel.Shown < sel.Total
        then Some (sprintf "попытки обрезаны: показано %d из %d (не больше %d, глубина до %d)"
                     sel.Shown sel.Total StepLog.MaxNodes StepLog.MaxDepth)
        else None
    r, sel.Tree, note

// Выполнить f с журналом: None — все шаги без отбора (как capture-step-log без уровня); Some уровень — отбор и лимиты
// (trace — плюс шаги упрощателя). → результат, шаги, пометка об обрезке
// Шаг S.5: lang ("ru" | "en") влияет только на текст пометки об обрезке; шаги не переводятся (см. captureStepsLang)
let captureStepsRaw (lang: string) (detail: StepLog.Detail option) (f: unit -> 'a) : 'a * StepLog.Step list * string option =
    match detail with
    | None ->
        let r, steps = StepLog.Journal.Capture f
        r, steps, None
    | Some d ->
        let r, steps =
            match d with
            | StepLog.Trace -> StepLog.Journal.Capture(fun () -> Debug.withSimplifyJournal f)
            | _ -> StepLog.Journal.Capture f
        let sel = StepLog.select d steps
        r, sel.Steps, StepDict.truncationNote lang sel

let captureSteps (detail: StepLog.Detail option) (f: unit -> 'a) : 'a * StepLog.Step list * string option =
    captureStepsRaw "ru" detail f

// Шаг S.5: захват с языком: шаги переведены (lang = "en"), пометка об обрезке на языке, предупреждения словаря
// (правила без перевода). → результат, шаги, пометка, предупреждения
let captureStepsLang (lang: string) (detail: StepLog.Detail option) (f: unit -> 'a)
    : 'a * StepLog.Step list * string option * string list =
    let r, steps, note = captureStepsRaw lang detail f
    let localized, missing = StepDict.localize lang steps
    r, localized, note, (StepDict.missingWarning missing |> Option.toList)

// Язык шагов из значения Lisp ('en, "ru", #f — по умолчанию ru)
let private langOf (who: string) (v: LispValue) : string =
    match v with
    | LispBool false | LispNil -> "ru"
    | LispSym s | LispStr s when StepDict.isLang s -> s
    | other -> failwithf "%s: язык шагов — \"ru\" или \"en\", получено %s" who (Printer.prettyPrint other)

let private detailOf (who: string) (v: LispValue) : StepLog.Detail =
    let s = match v with LispSym s | LispStr s -> s | o -> Printer.prettyPrint o
    match StepLog.tryParseDetail s with
    | Some d -> d
    | None -> failwithf "%s: уровень шагов brief | full | trace, получено %s" who s

let private levelOf (who: string) (v: LispValue) : StepLog.Level =
    match v with
    | LispSym "main" | LispStr "main" | LispBool false | LispNil -> StepLog.Main
    | LispSym "detail" | LispStr "detail" -> StepLog.Detail
    | other -> failwithf "%s: уровень шага main | detail, получено %s" who (Printer.prettyPrint other)

let private isProc (v: LispValue) = match v with LispFunc _ | LispBuiltin _ -> true | _ -> false

let private conditionToLisp (c: ConditionLog.Condition) : LispValue =
    LispList [ payload c.Condition; LispStr c.Reason ]

let all : (string * LispValue) list = [
    builtin "algo-stats" (fun args ->
        AlgoRegistry.init ()
        let group =
            match args with
            | [] -> None
            | [g] ->
                let name = nameOf "algo-stats" g
                if (AlgoStats.tryFind name).IsNone then
                    let known = AlgoStats.groups () |> List.map (fun x -> x.Name) |> String.concat ", "
                    failwithf "algo-stats: неизвестная группа %s (есть: %s)" name known
                Some name
            | _ -> failwith "algo-stats: (algo-stats) или (algo-stats 'группа)"
        LispList [ for (g, cs) in AlgoStats.snapshot group ->
                     LispList (sym g :: [ for (c, v) in cs -> LispList [ sym c; LispInteger (bigint v) ] ]) ])

    builtin "algo-stats-reset" (fun args ->
        AlgoRegistry.init ()
        let group =
            match args with
            | [] -> None
            | [g] -> Some (nameOf "algo-stats-reset" g)
            | _ -> failwith "algo-stats-reset: (algo-stats-reset) или (algo-stats-reset 'группа)"
        if AlgoStats.reset group then LispBool true
        else failwithf "algo-stats-reset: неизвестная группа %s" (defaultArg group ""))

    // Шаг 21i: счётчики и переключатели для алгоритмов, написанных на Lisp (раньше группы заводил только F#-код)
    // (algo-stats-register 'группа '(счётчик ...)) → #t; повторная регистрация возвращает ту же группу
    builtin "algo-stats-register" (fun args ->
        match args with
        | [g; LispList cs] ->
            let names = cs |> List.map (nameOf "algo-stats-register") |> Array.ofList
            let grp = AlgoStats.register (nameOf "algo-stats-register" g) names
            if grp.Counters <> names then
                failwithf "algo-stats-register: группа %s уже зарегистрирована с другими счётчиками" grp.Name
            LispBool true
        | _ -> failwith "algo-stats-register: (algo-stats-register 'группа '(счётчик ...))")

    // (algo-count 'группа 'счётчик [n]) — прибавить n (по умолчанию 1) к счётчику текущего потока; → новое значение
    builtin "algo-count" (fun args ->
        let bump g c (n: int) =
            let gname = nameOf "algo-count" g
            let cname = nameOf "algo-count" c
            match AlgoStats.tryFind gname with
            | None -> failwithf "algo-count: неизвестная группа %s" gname
            | Some grp ->
                let i = Array.IndexOf(grp.Counters, cname)
                if i < 0 then failwithf "algo-count: в группе %s нет счётчика %s" gname cname
                let vs = grp.Values
                vs.[i] <- int (min (int64 vs.[i] + int64 n) (int64 Int32.MaxValue))   // насыщение: «масса» бит не переполняет int
                LispInteger (bigint vs.[i])
        match args with
        | [g; c] -> bump g c 1
        | [g; c; LispInteger n] -> bump g c (int n)
        | _ -> failwith "algo-count: (algo-count 'группа 'счётчик [n])")

    // (algorithm-register 'имя '(значение ...) 'умолчание) → текущее значение (среда LISP_<ИМЯ> учитывается)
    builtin "algorithm-register" (fun args ->
        match args with
        | [n; LispList vs; d] ->
            let values = vs |> List.map (nameOf "algorithm-register") |> Array.ofList
            let s =
                try Algorithms.register (nameOf "algorithm-register" n) values (nameOf "algorithm-register" d)
                with :? ArgumentException as ex -> failwithf "algorithm-register: %s" ex.Message
            if s.Values <> values then
                failwithf "algorithm-register: алгоритм %s уже зарегистрирован с другими значениями" s.Name
            sym s.Value
        | _ -> failwith "algorithm-register: (algorithm-register 'имя '(значение ...) 'умолчание)")

    builtin "algorithms" (fun args ->
        AlgoRegistry.init ()
        match args with
        | [] ->
            LispList [ for s in Algorithms.all () ->
                         LispList [ sym s.Name; sym s.Value; LispList [ for v in s.Values -> sym v ] ] ]
        | _ -> failwith "algorithms: без аргументов")

    builtin "algorithm" (fun args ->
        AlgoRegistry.init ()
        match args with
        | [n] ->
            let name = nameOf "algorithm" n
            match Algorithms.tryFind name with
            | Some s -> sym s.Value
            | None -> failwithf "algorithm: неизвестный алгоритм %s" name
        | _ -> failwith "algorithm: (algorithm 'имя)")

    // (set-algorithm 'gcd 'zippel) → прежнее значение; (set-algorithm 'gcd 'auto) — вернуть умолчание
    builtin "set-algorithm" (fun args ->
        AlgoRegistry.init ()
        match args with
        | [n; v] ->
            let name = nameOf "set-algorithm" n
            let value = nameOf "set-algorithm" v
            match Algorithms.tryFind name with
            | None ->
                let known = Algorithms.all () |> List.map (fun s -> s.Name) |> String.concat ", "
                failwithf "set-algorithm: неизвестный алгоритм %s (есть: %s)" name known
            | Some s ->
                let old = s.Value
                try s.Set value
                with :? ArgumentException as ex -> failwithf "set-algorithm: %s" ex.Message
                sym old
        | _ -> failwith "set-algorithm: (set-algorithm 'имя 'значение)")

    // --- журнал шагов ---
    builtin "step-log-on" (fun _ -> StepLog.Journal.Enabled <- true; LispBool true)
    builtin "step-log-off" (fun _ -> StepLog.Journal.Enabled <- false; LispBool false)
    builtin "step-log-enabled?" (fun _ -> LispBool StepLog.Journal.Enabled)
    builtin "step-log-clear" (fun _ -> StepLog.Journal.Clear(); LispBool true)
    builtin "step-log" (fun _ -> LispList (StepLog.Journal.Steps |> List.map stepToLisp))
    // (record-step 'rule "Заголовок" "пояснение" до после ['main|'detail]) — шаг S.1; старая запись (шаг 21h')
    // (record-step "приём" "комментарий" до после) — см. StepLog.legacyRuleTitle. При выключенном журнале ничего не делает
    builtin "record-step" (fun args ->
        let who = "record-step"
        match args with
        | [rule; comment; before; after] ->
            if StepLog.Journal.Enabled then
                StepLog.Journal.Record(nameOf who rule, nameOf who comment, box before, box after)
            LispBool StepLog.Journal.Enabled
        | rule :: title :: comment :: before :: after :: rest when rest.Length <= 1 ->
            if StepLog.Journal.Enabled then
                let level = match rest with [l] -> levelOf who l | _ -> StepLog.Main
                StepLog.Journal.Record(nameOf who rule, nameOf who title, nameOf who comment, box before, box after, level)
            LispBool StepLog.Journal.Enabled
        | _ -> failwith "record-step: (record-step 'rule \"заголовок\" \"пояснение\" до после ['main|'detail]) или (record-step \"приём\" \"комментарий\" до после)")
    // (call-with-step 'rule "Заголовок" до thunk [пояснение [уровень [после-f]]]) — рамка: шаги внутри thunk становятся
    // детьми; после = результат thunk (или (после-f результат)); пояснение — строка или функция результата → строка.
    // Результат #f (неудача в каскаде) или ошибка — рамка отбрасывается вместе с детьми. Возвращает результат thunk.
    // Макрос with-step (lib\steps.lisp) не вычисляет заголовок и «до» при выключенном журнале
    builtin "call-with-step" (fun args ->
        let who = "call-with-step"
        match args with
        | rule :: title :: before :: thunk :: opts when opts.Length <= 3 ->
            if not StepLog.Journal.Enabled then Objects.applyHook thunk []
            else
                let opt i = if opts.Length > i then opts.[i] else LispBool false
                let level = levelOf who (opt 1)
                let token = StepLog.Journal.Open(nameOf who rule, nameOf who title, box before, level)
                let r =
                    try Objects.applyHook thunk []
                    with ex ->
                        StepLog.Journal.DiscardReason(token, ex.Message)
                        reraise ()
                match r with
                | LispBool false -> StepLog.Journal.DiscardReason(token, "нет результата (#f)")
                | _ ->
                    try
                        let comment =
                            match opt 0 with
                            | LispBool false | LispNil -> ""
                            | f when isProc f -> nameOf who (Objects.applyHook f [r])
                            | c -> nameOf who c
                        let after = match opt 2 with f when isProc f -> Objects.applyHook f [r] | _ -> r
                        StepLog.Journal.Close(token, comment, box after)
                    with _ ->
                        StepLog.Journal.Discard token
                        reraise ()
                r
        | _ -> failwith "call-with-step: (call-with-step 'rule \"заголовок\" до thunk [пояснение [уровень [после-f]]])")
    // (call-quietly thunk) — вызвать thunk с выключенным журналом (внутренние вычисления — проверки, вспомогательные
    // производные — не должны писать шаги); прежнее состояние восстанавливается. Шаг S.3
    builtin "call-quietly" (fun args ->
        match args with
        | [thunk] ->
            let was = StepLog.Journal.Enabled
            StepLog.Journal.Enabled <- false
            try Objects.applyHook thunk []
            finally StepLog.Journal.Enabled <- was
        | _ -> failwith "call-quietly: (call-quietly thunk)")
    // (capture-step-log thunk) → (результат шаги) — все шаги без отбора; (capture-step-log thunk 'brief|'full|'trace) →
    // (результат шаги пометка): отбор по уровню и лимиты (глубина 8, 200 узлов), пометка — строка об обрезке или #f.
    // Прежнее состояние журнала восстанавливается
    builtin "capture-step-log" (fun args ->
        match args with
        | [thunk] ->
            let (result, steps, _) = captureSteps None (fun () -> Objects.applyHook thunk [])
            LispList [ result; LispList (steps |> List.map stepToLisp) ]
        | [thunk; level] ->
            let d = detailOf "capture-step-log" level
            let (result, steps, note) = captureSteps (Some d) (fun () -> Objects.applyHook thunk [])
            LispList [ result; LispList (steps |> List.map stepToLisp)
                       (match note with Some n -> LispStr n | None -> LispBool false) ]
        | [thunk; level; lang] ->
            // шаг S.5: третий аргумент — язык пометки об обрезке (шаги остаются русскими: переводит steps-text/steps-translate)
            let d = detailOf "capture-step-log" level
            let (result, steps, note) =
                captureStepsRaw (langOf "capture-step-log" lang) (Some d) (fun () -> Objects.applyHook thunk [])
            LispList [ result; LispList (steps |> List.map stepToLisp)
                       (match note with Some n -> LispStr n | None -> LispBool false) ]
        | _ -> failwith "capture-step-log: (capture-step-log thunk ['brief|'full|'trace [язык]])")
    // (steps-text шаги [пометка [язык]]) → строка: дерево шагов с нумерацией 1., 1.1, … (печать steps); язык 'ru | 'en
    builtin "steps-text" (fun args ->
        let who = "steps-text"
        let text lang steps note = LispStr (stepsTextLang lang (listItems who steps |> List.map (stepOfLisp who)) note)
        match args with
        | [steps] -> text "ru" steps None
        | [steps; note] ->
            let n = match note with LispStr s -> Some s | _ -> None
            text "ru" steps n
        | [steps; note; lang] ->
            let n = match note with LispStr s -> Some s | _ -> None
            text (langOf who lang) steps n
        | _ -> failwith "steps-text: (steps-text шаги [пометка [язык]])")
    // (steps-translate язык шаги) → шаги с заголовками и пояснениями на языке ('en — словарь StepDict; 'ru — как есть)
    builtin "steps-translate" (fun args ->
        let who = "steps-translate"
        match args with
        | [lang; steps] ->
            let translated, _ = StepDict.localize (langOf who lang) (listItems who steps |> List.map (stepOfLisp who))
            LispList (translated |> List.map stepToLisp)
        | _ -> failwith "steps-translate: (steps-translate язык шаги)")

    // --- Шаг D2a: журнал попыток ---
    // (explain выражение) — вычислить выражение с журналом и напечатать дерево попыток
    // («стратегия — успех/отказ: причина — мс», повторы ×N), вернуть значение. Сокращение для
    // (capture-attempts (lambda () выражение)) + печать; уровень языка — 'ru | 'en (второй аргумент explain-call)
    builtin "capture-attempts" (fun args ->
        match args with
        | [thunk] ->
            let (r, tree, note) = captureAttemptsRaw "ru" (fun () -> Objects.applyHook thunk [])
            LispList [ r; LispList (tree |> List.map attemptToLisp)
                       (match note with Some n -> LispStr n | None -> LispBool false) ]
        | [thunk; lang] ->
            let (r, tree, note) = captureAttemptsRaw (langOf "capture-attempts" lang) (fun () -> Objects.applyHook thunk [])
            LispList [ r; LispList (tree |> List.map attemptToLisp)
                       (match note with Some n -> LispStr n | None -> LispBool false) ]
        | _ -> failwith "capture-attempts: (capture-attempts thunk [язык])")
    // (attempts-text дерево [пометка [язык]]) — строка: дерево попыток (печать explain); дерево — из capture-attempts
    builtin "attempts-text" (fun args ->
        let who = "attempts-text"
        let rec ofLisp (v: LispValue) : StepLog.Attempt =
            // из формы шага (rule title comment before after level children): comment → статус/причина/время
            match v with
            | LispList (rule :: title :: comment :: before :: _after :: _level :: children :: _) ->
                let text (x: LispValue) = match x with LispStr s | LispSym s -> s | _ -> ""
                let c = text comment
                let ok = c.StartsWith "успех"
                // comment = «успех: пояснение» | «отказ: причина» [+ « ×N»] + « — M мс» (attemptToLisp);
                // для повторной печати восстанавливаем reason/repeats/ms
                let body = if c.Length > 7 && c.IndexOf ':' >= 0 then c.Substring(c.IndexOf ':' + 2) else ""
                let ms, repeats, reason =
                    let m = System.Text.RegularExpressions.Regex.Match(body, @"^(.*?)(?: ×(\d+))? — ([\d.]+) мс$")
                    if m.Success then
                        (try float m.Groups.[3].Value with _ -> 0.0),
                        (try int m.Groups.[2].Value with _ -> 1),
                        m.Groups.[1].Value
                    else 0.0, 1, body
                { Rule = text rule; Title = text title; Before = box before; Ok = ok
                  Reason = reason; Ms = ms; Repeats = repeats
                  Children = listItems who children |> List.map ofLisp }
            | other -> failwithf "%s: попытка — список (rule title comment before after level children), получено %s"
                            who (Printer.prettyPrint other)
        let noteOf (v: LispValue) : string option = match v with LispStr s -> Some s | _ -> None
        match args with
        | [tree] -> LispStr (attemptsTextLang "ru" (listItems who tree |> List.map ofLisp) None)
        | [tree; note] ->
            LispStr (attemptsTextLang "ru" (listItems who tree |> List.map ofLisp) (noteOf note))
        | [tree; note; lang] ->
            LispStr (attemptsTextLang (langOf who lang) (listItems who tree |> List.map ofLisp) (noteOf note))
        | _ -> failwith "attempts-text: (attempts-text дерево [пометка [язык]])")
    // (attempt-fail \"причина\") — шаг D2b (заготовка D2a): явная причина отказа для текущей рамки with-step;
    // приоритетнее автоматической («нет результата (#f)» / сообщение ошибки)
    builtin "attempt-fail" (fun args ->
        match args with
        | [LispStr reason] -> StepLog.Journal.NoteFail reason; LispBool true
        | [v] -> Printer.expectError "attempt-fail" 1 "ожидалась строка-причина" v
        | _ -> failwith "attempt-fail: (attempt-fail \"причина\")")

    // --- канал условий применимости ответа (подшаг 22.2; всегда включён) ---
    // (record-condition '(/= a 0) "причина") → #t, если условие новое, #f — уже записано (дубликаты не накапливаются)
    builtin "record-condition" (fun args ->
        match args with
        | [cond; reason] ->
            let r = match reason with LispStr s -> s | other -> failwithf "record-condition: причина — строка, получено %s" (Printer.prettyPrint other)
            LispBool (ConditionLog.Conditions.Record(Printer.prettyPrint cond, box cond, r))
        | _ -> failwith "record-condition: (record-condition условие \"причина\")")
    // (conditions) → ((условие "причина") ...) по порядку записи
    builtin "conditions" (fun _ -> LispList (ConditionLog.Conditions.All |> List.map conditionToLisp))
    builtin "conditions-clear" (fun _ -> ConditionLog.Conditions.Clear(); LispBool true)
    // (capture-conditions thunk) → (результат ((условие "причина") ...)); внешний канал не меняется
    builtin "capture-conditions" (fun args ->
        match args with
        | [thunk] ->
            let (result, cs) = ConditionLog.Conditions.Capture(fun () -> Objects.applyHook thunk [])
            LispList [ result; LispList (cs |> List.map conditionToLisp) ]
        | _ -> failwith "capture-conditions: (capture-conditions thunk)")
]
