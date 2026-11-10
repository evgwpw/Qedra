// Шаг S.5: английский словарь шагов (StepDict), язык шагов lang ru|en, «или» в печати, сквозной набор задач шага S
// (diff, simplify, integrate, solve, limit, series, groebner): дерево не пусто, корень — ожидаемый rule, checkSteps без
// ложных, brief ⊂ full, en и ru — одна структура, при выключенном журнале шагов нет и ответы те же
module StepsFinalTests

open System
open System.IO
open System.Text.Json
open System.Text.RegularExpressions
open Xunit
open Types
open Reader
open Evaluator
open Printer

let private call (session: Env) (json: string) : JsonElement =
    JsonDocument.Parse(AgentApi.handleJsonRequest session json).RootElement

let private mathReq (session: Env) (code: string) : JsonElement =
    call session (JsonSerializer.Serialize({| op = "math"; code = code |}))

let private runLisp (s: Env) (code: string) : string =
    readAll code |> List.fold (fun _ e -> eval e s) LispNil |> prettyPrint

let private sys = "(list '(= (+ (^ x 2) (^ y 2)) 5) '(= (* x y) 2))"

// --- Словарь ---

let private repoRoot : Lazy<string> =
    lazy (
        let rec find (dir: DirectoryInfo) =
            if isNull dir then failwith "не найден корень репозитория (Lisp.slnx)"
            elif File.Exists(Path.Combine(dir.FullName, "Lisp.slnx")) then dir.FullName
            else find dir.Parent
        find (DirectoryInfo AppContext.BaseDirectory))

// rule, встречающиеся в коде: with-step / record-step / st-filter-step в lib\*.lisp, строки rule в solve/limit/series
// (рамки с вычисляемым rule), F#-правила Differentiate.fs
let private rulesInSource () : Set<string> =
    let root = repoRoot.Value
    let lispFiles =
        Directory.GetFiles(Path.Combine(root, "lib"), "*.lisp", SearchOption.AllDirectories)
        |> Array.filter (fun f -> not (f.Contains "mathlang"))
    let found = Collections.Generic.HashSet<string>()
    let add (m: Match) = if m.Success then found.Add m.Groups.[1].Value |> ignore
    for f in lispFiles do
        let text = File.ReadAllText f
        for m in Regex.Matches(text, @"\((?:with-step \(|record-step |rs-note |alg-step |st-filter-step )'([a-z][a-z0-9:_.-]*)") do add m
        // правила defrule библиотеки (в начале строки): шаг simplify:rule:имя с заголовком :title
        for m in Regex.Matches(text, @"(?m)^\(defrule\s+([a-z][a-z0-9-]*)") do
            if m.Success then found.Add("simplify:rule:" + m.Groups.[1].Value) |> ignore
        let name = Path.GetFileName f
        // рамки с вычисляемым rule (solve-deg-rule, invert-rule) и ключи ser-/lim-: все квотированные rule семейства
        if name = "solve.lisp" then for m in Regex.Matches(text, @"'(solve-[a-z-]+)") do add m
        if name = "limit.lisp" then for m in Regex.Matches(text, @"'(limit(?:-[a-z]+)*)[ )]") do add m
        if name = "series.lisp" then for m in Regex.Matches(text, @"'(series(?:-[a-z]+)*)[ )]") do add m
    let diffText = File.ReadAllText(Path.Combine(root, "src", "Lisp.Core", "Differentiate.fs"))
    for m in Regex.Matches(diffText, "\"((?:diff-|differentiation|simplify-result)[a-z-]*)\"") do add m
    let dbg = File.ReadAllText(Path.Combine(root, "src", "Lisp.Core", "Debug.fs"))
    for m in Regex.Matches(dbg, "\\| \"([a-z-]+)\" -> \"[^\"]+\"") do found.Add("simplify:" + m.Groups.[1].Value) |> ignore
    found.Add "simplification" |> ignore
    Set.ofSeq found

[<Fact>]
let ``словарь: покрывает все rule, встречающиеся в коде (lib, Differentiate, Debug)`` () =
    let rules = rulesInSource ()
    Assert.True(rules.Count > 80, sprintf "найдено rule: %d" rules.Count)
    let known = Set.ofList StepDict.knownRules
    let missing = rules |> Set.filter (fun r -> not (known.Contains r))
    Assert.True(missing.IsEmpty, "нет перевода для rule: " + String.Join(" ", missing))
    // и обратно: в словаре нет опечаток — каждый ключ встречается в коде
    let extra = known |> Set.filter (fun r -> not (rules.Contains r))
    Assert.True(extra.IsEmpty, "в словаре лишние rule: " + String.Join(" ", extra))
    // каждая запись непуста: заголовок переводится (формулы-пояснения могут быть без пар)
    for r in StepDict.knownRules do
        let e = (StepDict.tryFind r).Value
        Assert.False(e.Title.IsEmpty, r)
        for (ru, en) in e.Title @ e.Comment do
            Assert.False(StepDict.hasCyrillic en, sprintf "%s: перевод содержит русские буквы: %s" r en)

[<Fact>]
let ``словарь: семейства simplify:rule:имя, simplify:method:имя; неизвестный rule — русский текст и предупреждение`` () =
    let mk rule title comment : StepLog.Step =
        { Rule = rule; Title = title; Comment = comment; Before = null; After = null; Level = StepLog.Main; Children = []; Omitted = 0 }
    let out, missing =
        StepDict.localize "en" [ mk "simplify:rule:foo" "правило foo" ""; mk "simplify:method:bar" "метод bar" ""
                                 mk "simplify:zzz" "упрощение: zzz" ""; mk "mystery-rule" "Тайна" "пояснение" ]
    Assert.Equal<string list>([ "rule foo"; "method bar"; "simplification: zzz"; "Тайна" ], out |> List.map (fun s -> s.Title))
    Assert.Equal<string list>([ "mystery-rule" ], missing)
    Assert.Equal("no English translation for step rules: mystery-rule (Russian text kept)", (StepDict.missingWarning missing).Value)
    // rule известен, но фраза пояснения не покрыта — поле остаётся русским, rule в списке
    let out2, missing2 = StepDict.localize "en" [ mk "limit-abs" "Раскрытие модуля" "новая неизвестная фраза" ]
    Assert.Equal("Removing the absolute value", out2.Head.Title)
    Assert.Equal("новая неизвестная фраза", out2.Head.Comment)
    Assert.Equal<string list>([ "limit-abs" ], missing2)
    // ru — без изменений
    let same, none = StepDict.localize "ru" [ mk "mystery-rule" "Тайна" "пояснение" ]
    Assert.Equal("Тайна", same.Head.Title)
    Assert.Empty(none)

// --- lang в --json, языке, MCP ---

[<Fact>]
let ``lang: JSON — английские заголовки, rule и структура те же, ошибка для неизвестного языка`` () =
    let s = AgentApi.makeSession ()
    let req (lang: string option) =
        let basic = {| op = "solve"; code = "x^2-5*x+6 = 0"; var = "x"; syntax = "math"; steps = "full" |}
        match lang with
        | None -> call s (JsonSerializer.Serialize basic)
        | Some l -> call s (JsonSerializer.Serialize({| op = "solve"; code = "x^2-5*x+6 = 0"; var = "x"; syntax = "math"; steps = "full"; lang = l |}))
    let ru = (req None).GetProperty("steps").[0]
    let en = (req (Some "en")).GetProperty("steps").[0]
    Assert.Equal("Решение уравнения относительно x", ru.GetProperty("title").GetString())
    Assert.Equal("Solving the equation for x", en.GetProperty("title").GetString())
    Assert.Equal(ru.GetProperty("rule").GetString(), en.GetProperty("rule").GetString())
    let f = en.GetProperty("children").[0]
    Assert.Equal("solve-factor", f.GetProperty("rule").GetString())
    Assert.Equal("Factoring", f.GetProperty("title").GetString())
    Assert.Equal("a product is zero when at least one factor is zero: x - 2 = 0 or x - 3 = 0", f.GetProperty("comment").GetString())
    Assert.Equal("(x - 2)(x - 3) = 0", f.GetProperty("after_pretty").GetString())
    Assert.Equal("Linear equation", f.GetProperty("children").[0].GetProperty("title").GetString())
    // lang: ru — как без параметра; «или» в совокупности решений по-русски, «or» — по-английски
    let q lang = (call s (JsonSerializer.Serialize({| op = "solve"; code = "x^2-2 = 0"; var = "x"; syntax = "math"; steps = "full"; lang = lang |}))).GetProperty("steps").[0].GetProperty("children").[0]
    Assert.Equal("x = 2^(1/2) или x = -2^(1/2)", (q "ru").GetProperty("after_pretty").GetString())
    Assert.Equal("x = 2^(1/2) or x = -2^(1/2)", (q "en").GetProperty("after_pretty").GetString())
    Assert.Equal("Квадратное уравнение", (q "ru").GetProperty("title").GetString())
    Assert.Equal("Quadratic equation", (q "en").GetProperty("title").GetString())
    // неизвестный язык — ошибка протокола
    let bad = call s (JsonSerializer.Serialize({| op = "solve"; code = "x = 1"; var = "x"; syntax = "math"; steps = "full"; lang = "de" |}))
    Assert.Equal("error", bad.GetProperty("status").GetString())
    Assert.Contains("Неизвестное значение lang", bad.GetProperty("error").GetString())
    // без steps язык ничего не меняет
    let none = call s (JsonSerializer.Serialize({| op = "solve"; code = "x^2-5*x+6 = 0"; var = "x"; syntax = "math"; lang = "en" |}))
    Assert.Equal("{2, 3}", none.GetProperty("pretty").GetString())

[<Fact>]
let ``lang: шаг без перевода — русский текст и предупреждение в warnings; пометка об обрезке на английском`` () =
    let s = AgentApi.makeSession ()
    let r = call s (JsonSerializer.Serialize({| op = "eval"; code = "(begin (record-step 'zz-mystery \"Тайна\" \"пояснение\" 1 2) 5)"; steps = "full"; lang = "en" |}))
    let st = r.GetProperty("steps").[0]
    Assert.Equal("zz-mystery", st.GetProperty("rule").GetString())
    Assert.Equal("Тайна", st.GetProperty("title").GetString())
    let warns = [ for w in r.GetProperty("warnings").EnumerateArray() -> w.GetString() ]
    Assert.Contains("no English translation for step rules: zz-mystery (Russian text kept)", warns)
    // по-русски предупреждения нет
    let ru = call s (JsonSerializer.Serialize({| op = "eval"; code = "(begin (record-step 'zz-mystery \"Тайна\" \"пояснение\" 1 2) 5)"; steps = "full" |}))
    Assert.True(ru.GetProperty("warnings").ValueKind = JsonValueKind.Null)
    // обрезка: английская пометка
    let deep = "(begin (define (zdeep n) (if (= n 0) 0 (with-step ('solve-linear \"Линейное уравнение\" n) (zdeep (- n 1)) n))) (zdeep 10))"
    let d = call s (JsonSerializer.Serialize({| op = "eval"; code = deep; steps = "full"; lang = "en" |}))
    let dw = [ for w in d.GetProperty("warnings").EnumerateArray() -> w.GetString() ]
    Assert.Contains("steps truncated: showing 8 of 10 (depth up to 8)", dw)

// шаги алгебраического Риша: --json/MCP steps = brief возвращает ключевые шаги (rule alg-*) вложенными в integration,
// без шума дифференцирования; английский вариант — без русских букв
[<Fact>]
let ``шаги Риша: JSON steps brief — ключевые шаги алгебраического интеграла (кручение 7), en без русских букв`` () =
    let s = AgentApi.makeSession ()
    let req (lang: string) =
        call s (JsonSerializer.Serialize({| op = "integrate"; code = "(28 - 5*x)/(x*sqrt(4*x^3 - 15*x^2 + 8*x + 16))"; var = "x"; syntax = "math"; steps = "brief"; lang = lang |}))
    let childRules (n: JsonElement) = [ for c in n.GetProperty("children").EnumerateArray() -> c.GetProperty("rule").GetString() ]
    let rec texts (n: JsonElement) : string list =
        [ yield n.GetProperty("title").GetString()
          yield n.GetProperty("comment").GetString()
          for c in n.GetProperty("children").EnumerateArray() do yield! texts c ]
    let ru = req "ru"
    let top = ru.GetProperty("steps").[0]
    Assert.Equal("integration", top.GetProperty("rule").GetString())
    Assert.Equal<string list>([ "alg-integration" ], childRules top)
    let alg = top.GetProperty("children").[0]
    let rules = childRules alg
    for r in [ "alg-curve"; "alg-hermite"; "alg-residues"; "alg-torsion-bound"; "alg-principal"; "alg-certificate" ] do
        Assert.Contains(r, rules)
    Assert.DoesNotContain("differentiation", rules)
    let all = texts top
    Assert.Contains(all, fun t -> t.Contains "B = НОД = 7")
    Assert.Contains(all, fun t -> t.Contains "вычеты: 7 в (x = 0, y = 4); -7 в (x = 0, y = -4)")
    let en = (req "en").GetProperty("steps").[0]
    let cyr = texts en |> List.filter StepDict.hasCyrillic
    Assert.True(cyr.IsEmpty, sprintf "русские буквы в английском: %A" cyr)
    Assert.Contains(texts en, fun t -> t.Contains "B = gcd = 7")

[<Fact>]
let ``lang: язык — steps(e, "full", "en"), step_list с языком, Lisp-форма steps, ошибка языка`` () =
    let s = AgentApi.makeSession ()
    let out (code: string) = (mathReq s code).GetProperty("output").GetString()
    let en = out "steps(solve(x^2-5*x+6=0, x), \"full\", \"en\")"
    Assert.Contains("1. Solving the equation for x: x^2 - 5x + 6 = 0 ⇒ {2, 3}", en)
    Assert.Contains("1.1 Factoring: x^2 - 5x + 6 = 0 ⇒ (x - 2)(x - 3) = 0", en)
    Assert.Contains("a product is zero when at least one factor is zero: x - 2 = 0 or x - 3 = 0", en)
    Assert.Contains("1.1.1 Linear equation: x - 2 = 0 ⇒ x = 2", en)
    Assert.Contains("ax + b = 0 ⇒ x = −b/a; here a = 1, b = -2", en)
    Assert.False(StepDict.hasCyrillic en, en)
    let ru = out "steps(solve(x^2-5*x+6=0, x), \"full\")"
    Assert.Contains("1.1 Разложение на множители: x^2 - 5x + 6 = 0 ⇒ (x - 2)(x - 3) = 0", ru)
    Assert.Contains("x - 2 = 0 или x - 3 = 0", ru)
    // brief по умолчанию + язык
    let brief = out "steps(diff(x^2*sin(x), x), \"brief\", \"en\")"
    Assert.Contains("1. Differentiation with respect to x:", brief)
    // step_list: заголовки на языке, rule тот же
    let rows = (mathReq s "step_list(solve(x^2-5*x+6=0, x), \"full\", \"en\")").GetProperty("pretty").GetString()
    Assert.Contains("Solving the equation for x", rows)
    Assert.Contains("solve-factor", rows)
    Assert.DoesNotContain("Решение", rows)
    // ошибка в языке
    let bad = mathReq s "steps(1 + 2, \"full\", \"de\")"
    Assert.Equal("error", bad.GetProperty("status").GetString())
    // Lisp-форма: (steps e 'full 'en) и steps-translate
    let r = runLisp s "(steps-text (steps-translate 'en (cadr (capture-step-log (lambda () (solve '(= (+ (^ x 2) -3 x) 0) 'x))))))"
    Assert.Contains("Solving the equation for x", r)
    Assert.Contains("(шаги не записаны)", runLisp s "(steps-text '())")
    Assert.Contains("(no steps recorded)", runLisp s "(steps-text '() #f 'en)")

[<Fact>]
let ``lang: MCP — параметр lang в схеме и в запросе AgentApi`` () =
    let tool n = McpHost.tools |> List.find (fun t -> t.Name = n)
    for n in [ "math"; "evaluate"; "simplify"; "diff"; "integrate"; "solve"; "limit"; "series"; "groebner"; "expand" ] do
        let schema = McpHost.inputSchema (tool n)
        let lang = schema.GetProperty("properties").GetProperty("lang")
        Assert.Equal("ru en", lang.GetProperty("enum").EnumerateArray() |> Seq.map (fun e -> e.GetString()) |> String.concat " ")
    let args = Collections.Generic.Dictionary<string, JsonElement>()
    args["expr"] <- JsonSerializer.SerializeToElement "x^2"
    args["var"] <- JsonSerializer.SerializeToElement "x"
    args["steps"] <- JsonSerializer.SerializeToElement "full"
    args["lang"] <- JsonSerializer.SerializeToElement "en"
    let req = JsonDocument.Parse(McpHost.buildRequest (tool "diff") (args :> Collections.Generic.IDictionary<_, _>)).RootElement
    Assert.Equal("en", req.GetProperty("lang").GetString())

// --- Сквозной набор задач шага S ---

// (код, ожидаемый корневой rule)
// Ускорение тестов: основной набор (по одной задаче каждого вида) идёт в быстром режиме, дополнительный (больше вариантов
// пояснений) — теми же проверками во вторых тестах с Category=Slow; полный прогон покрывает оба.
let private coreTasks : (string * string) list =
    [ "(diff 'x '(* (^ x 2) (sin x)))", "differentiation"
      "(diff 'x '(/ (+ x 1) (- x 1)))", "differentiation"
      "(diff 'x '(exp (^ x 2)))", "differentiation"
      "(step-simplify '(+ (^ (sin x) 2) (^ (cos x) 2)))", "simplification"
      "(integrate '(* x (exp x)) 'x)", "integration"
      "(integrate '(* 2 x (cos (^ x 2))) 'x)", "integration"
      "(integrate '(/ 1 (- (^ x 2) 1)) 'x)", "integration"
      "(integrate '(^ x 2) 'x 0 1)", "int-definite"
      "(solve '(= (+ (^ x 2) (* -5 x) 6) 0) 'x)", "solve-equation"
      "(solve '(= (- (^ x 2) 2) 0) 'x)", "solve-equation"
      "(solve '(= (sin x) 1/2) 'x)", "solve-equation"
      "(solve '(= (sqrt x) (- x 2)) 'x)", "solve-equation"
      "(solve '(= (/ 1 x) x) 'x)", "solve-equation"
      "(solve (list '(= (+ x y) 3) '(= (- x y) 1)) '(x y))", "solve-linear-system"
      sprintf "(solve %s '(x y))" sys, "polynomial-system"
      "(limit '(/ (sin x) x) 'x 0)", "limit"
      "(limit '(/ (exp x) (^ x 2)) 'x 'inf)", "limit"
      "(series '(exp (sin x)) 'x 0 5)", "series"
      "(series '(tan x) 'x 0 6)", "series"
      "(groebner (list '(- (+ (^ x 2) (^ y 2)) 1) '(- x y)) '(x y))", "groebner-basis" ]

// больше вариантов пояснений: каждая фраза словаря проходит через en-перевод хотя бы раз
let private extraTasks : (string * string) list =
    [ "(integrate '(* (exp x) (sin x)) 'x)", "integration"
      "(integrate '(^ (sin x) 3) 'x)", "integration"
      "(integrate '(^ (sin x) 2) 'x)", "integration"
      "(integrate '(* (sin x) (cos (* 2 x))) 'x)", "integration"
      "(integrate '(/ 1 (+ (^ x 3) x 1)) 'x)", "integration"
      "(integrate '(/ 1 (^ (+ (^ x 3) x 1) 2)) 'x)", "integration"
      "(integrate '(sqrt (+ (^ x 2) 1)) 'x)", "integration"
      "(integrate '(^ x -2) 'x 1 'inf)", "int-definite"
      "(integrate '(/ (+ (^ x 2) 1) (- (^ x 3) x)) 'x)", "integration"
      "(integrate '(/ 1 (^ (+ x 1) 3)) 'x)", "integration"
      "(integrate '(/ 1 (+ (^ x 2) x 1)) 'x)", "integration"
      "(integrate '(log x) 'x)", "integration"
      "(solve '(= (+ (* a x) b) 0) 'x)", "solve-equation"
      "(solve '(= (+ (sin x) (cos x)) 0) 'x)", "solve-equation"
      "(solve '(= (- (^ x 3) 2) 0) 'x)", "solve-equation"
      "(solve '(= (abs x) 3) 'x)", "solve-equation"
      "(solve '(= (log x) 2) 'x)", "solve-equation"
      "(solve '(= (/ (- (^ x 2) 1) (- x 1)) 0) 'x)", "solve-equation"
      "(solve '(= (+ (^ x 4) (* -5 (^ x 2)) 4) 0) 'x)", "solve-equation"
      "(solve '(= (^ x 2) 4) 'x)", "solve-equation"
      "(limit '(- (exp x) x) 'x 'inf)", "limit"
      "(limit '(/ (abs x) x) 'x 0 'plus)", "limit"
      "(limit '(^ x x) 'x 0 'plus)", "limit"
      "(limit '(* x (log x)) 'x 0 'plus)", "limit"
      "(limit '(^ x 2) 'x 3)", "limit"
      "(series '(/ 1 (* x (- 1 x))) 'x 0 3)", "series"
      "(series '(sqrt (+ 1 x)) 'x 0 4)", "series"
      "(series '(exp x) 'x 1 2)", "series"
      "(series '(* (exp x) (cos (* 2 x))) 'x 0 4)", "series"
      "(series '(/ 1 (^ (- 1 x) 2)) 'x 0 4)", "series"
      "(step-simplify '(+ x x (sin (* 1/2 pi))))", "simplification" ]

let private flatRules (ss: StepLog.Step list) : string list =
    let rec go (ss: StepLog.Step list) = ss |> List.collect (fun s -> s.Rule :: go s.Children)
    go ss

// структура дерева: rule, уровень и число детей каждого шага в порядке обхода
let rec private shape (ss: StepLog.Step list) : string list =
    ss |> List.collect (fun s -> sprintf "%s/%s/%d/%d" s.Rule (StepLog.levelName s.Level) s.Children.Length s.Omitted :: shape s.Children)

let rec private texts (ss: StepLog.Step list) : string list =
    ss |> List.collect (fun s -> s.Title :: s.Comment :: texts s.Children)

let private checkTree (tasks: (string * string) list) =
    let s = AgentApi.makeSession ()
    for (code, root) in tasks do
        let _, steps, _ = AlgoBuiltins.captureSteps None (fun () -> eval (List.head (readAll code)) s)
        Assert.True(not steps.IsEmpty, code)
        Assert.Equal(root, steps.Head.Rule)
        let checks = AgentApi.checkSteps s [] steps
        Assert.True(checks.Length >= 1, code)
        Assert.True((AgentApi.failedSteps checks).IsEmpty, sprintf "%s: ложный шаг %A" code (AgentApi.failedSteps checks))

[<Fact>]
let ``сквозной набор: дерево не пусто, корень — ожидаемый rule, checkSteps без ложных`` () = checkTree coreTasks

[<Fact; Trait("Category", "Slow")>]
let ``сквозной набор (дополнительные задачи): дерево не пусто, корень — ожидаемый rule, checkSteps без ложных`` () = checkTree extraTasks

let private checkBriefLang (tasks: (string * string) list) =
    let s = AgentApi.makeSession ()
    for (code, root) in tasks do
        let capture lang detail =
            let _, steps, _, warns = AlgoBuiltins.captureStepsLang lang (Some detail) (fun () -> eval (List.head (readAll code)) s)
            steps, warns
        let briefSteps, _ = capture "ru" StepLog.Brief
        let fullRu, warnsRu = capture "ru" StepLog.Full
        let fullEn, warnsEn = capture "en" StepLog.Full
        Assert.Equal(root, fullRu.Head.Rule)
        // brief ⊂ full: rule главных шагов верхнего уровня есть среди rule полного дерева, brief не длиннее
        Assert.True(Set.isSubset (Set.ofList (flatRules briefSteps)) (Set.ofList (flatRules fullRu)), code)
        Assert.True(briefSteps.Length >= 1 && briefSteps.Length <= fullRu.Length, code)
        Assert.True(briefSteps |> List.forall (fun b -> b.Children.IsEmpty), code)
        // en и ru: одинаковая структура (rule, уровень, число детей), нет предупреждений, нет русских букв в переводе
        Assert.Equal<string list>(shape fullRu, shape fullEn)
        Assert.Empty(warnsRu)
        Assert.True(warnsEn.IsEmpty, sprintf "%s: %A" code warnsEn)
        let cyr = texts fullEn |> List.filter StepDict.hasCyrillic
        Assert.True(cyr.IsEmpty, sprintf "%s: русские буквы в английском: %A" code cyr)
        // а по-русски перевод не применяется: русский текст есть
        Assert.True(texts fullRu |> List.exists StepDict.hasCyrillic, code)

[<Fact>]
let ``сквозной набор: brief — подмножество full, en и ru — одна структура, перевод без русских букв`` () = checkBriefLang coreTasks

[<Fact; Trait("Category", "Slow")>]
let ``сквозной набор (дополнительные задачи): brief — подмножество full, en и ru — одна структура, перевод без русских букв`` () = checkBriefLang extraTasks

let private checkJournalOff (tasks: (string * string) list) =
    let s = AgentApi.makeSession ()
    StepLog.Journal.Clear()
    Assert.False(StepLog.Journal.Enabled)
    for (code, _) in tasks do
        let off = runLisp s code
        Assert.Empty(StepLog.Journal.Steps)
        let on = runLisp s (sprintf "(car (capture-step-log (lambda () %s)))" code)
        Assert.Equal(off, on)
        // и на английском захват даёт тот же ответ
        let en = runLisp s (sprintf "(car (capture-step-log (lambda () %s) 'full 'en))" code)
        Assert.Equal(off, en)
    Assert.False(StepLog.Journal.Enabled)
    Assert.Empty(StepLog.Journal.Steps)
    // ответ MCP/--json без steps не содержит шагов
    let r = call s (JsonSerializer.Serialize({| op = "solve"; code = "x^2-5*x+6 = 0"; var = "x"; syntax = "math"; lang = "en" |}))
    Assert.True(r.GetProperty("steps").ValueKind = JsonValueKind.Null)

[<Fact>]
let ``сквозной набор: журнал выключен — шагов нет, ответы те же; ответ с захватом и без совпадают`` () = checkJournalOff coreTasks

[<Fact; Trait("Category", "Slow")>]
let ``сквозной набор (дополнительные задачи): журнал выключен — шагов нет, ответы те же; ответ с захватом и без совпадают`` () = checkJournalOff extraTasks

[<Fact>]
let ``trace: шаги упрощателя переводятся (simplify:имя), без предупреждений`` () =
    let s = AgentApi.makeSession ()
    let codes =
        [ "(simplify '(+ x x (sin (* 1/2 pi))))"; "(simplify '(* (exp x) (exp y)))"; "(simplify '(^ (^ x 2) 3))"
          "(simplify '(+ (^ (sin x) 2) (^ (cos x) 2)))"; "(simplify '(sqrt 12))"; "(simplify '(^ %i 5))"
          "(simplify '(* 2 (^ x 3) (^ x 4)))"; "(simplify '(* -1 (+ a b)))"; "(simplify '(^ (* a b) 2))" ]
    let mutable seen = Set.empty
    for code in codes do
        let _, en, _, warns = AlgoBuiltins.captureStepsLang "en" (Some StepLog.Trace) (fun () -> eval (List.head (readAll code)) s)
        Assert.True(warns.IsEmpty, sprintf "%s: %A" code warns)
        Assert.True(texts en |> List.forall (fun t -> not (StepDict.hasCyrillic t)), code)
        seen <- Set.union seen (Set.ofList (flatRules en))
    Assert.True(seen.Count >= 4, sprintf "%A" seen)
    // семейство simplify:rule:имя
    let fam : StepLog.Step =
        { Rule = "simplify:rule:my-rule"; Title = "правило my-rule"; Comment = ""; Before = null; After = null
          Level = StepLog.Detail; Children = []; Omitted = 0 }
    Assert.Equal("rule my-rule", (StepDict.localize "en" [ fam ] |> fst).Head.Title)

[<Fact>]
let ``честные шаги: квадратное уравнение — разложение при рациональных корнях, дискриминант при иррациональных и комплексных`` () =
    let s = AgentApi.makeSession ()
    let rules (code: string) =
        let _, steps, _ = AlgoBuiltins.captureSteps None (fun () -> eval (List.head (readAll code)) s)
        flatRules steps
    // рациональные корни — solve-factor с вложенными линейными, без solve-quadratic
    Assert.Equal<string list>([ "solve-equation"; "solve-factor"; "solve-linear"; "solve-linear" ], rules "(solve '(= (+ (^ x 2) (* -5 x) 6) 0) 'x)")
    Assert.Equal<string list>([ "solve-equation"; "solve-factor"; "solve-linear" ], rules "(solve '(= (+ (^ x 2) (* 4 x) 4) 0) 'x)")   // кратный корень
    Assert.Equal<string list>([ "solve-equation"; "solve-factor"; "solve-linear"; "solve-linear" ], rules "(solve '(= (- (^ x 2) 4) 0) 'x)")
    Assert.Equal<string list>([ "solve-equation"; "solve-factor"; "solve-linear"; "solve-linear" ], rules "(solve '(= (+ (* 2 (^ x 2)) (* -3 x) 1) 0) 'x)")
    // иррациональные и комплексные корни — формула с дискриминантом
    Assert.Equal<string list>([ "solve-equation"; "solve-quadratic" ], rules "(solve '(= (+ (^ x 2) (* -5 x) 3) 0) 'x)")
    Assert.Equal<string list>([ "solve-equation"; "solve-quadratic" ], rules "(solve '(= (+ (^ x 2) 1) 0) 'x)")
    // символьные коэффициенты: неприводимый многочлен — формула
    Assert.Equal<string list>([ "solve-equation"; "solve-quadratic" ], rules "(solve '(= (+ (* a (^ x 2)) (* b x) c) 0) 'x)")
    // шаг solve-quadratic не подменяет приём: дискриминант в пояснении есть, а у solve-factor его нет
    let _, steps, _ = AlgoBuiltins.captureSteps None (fun () -> eval (List.head (readAll "(solve '(= (+ (^ x 2) (* -5 x) 6) 0) 'x)")) s)
    Assert.DoesNotContain("дискриминант", String.Join(" ", texts steps))
