// Шаг S.1: механизм пошаговых решений — рамки with-step, нулевая стоимость, уровни brief/full/trace, печать дерева,
// steps()/step_list() языка, дерево в ToolResponse/MCP, помощник проверки эквивалентности шагов (AgentApi.checkSteps)
module StepsTests

open System.Text.Json
open Xunit
open Types
open Reader
open Evaluator
open Printer

let private run (env: Env) (src: string) : string =
    readAll src |> List.fold (fun _ e -> eval e env) LispNil |> prettyPrint

// значение-строка (steps-text) без экранирования печати
let private runStr (env: Env) (src: string) : string =
    match readAll src |> List.fold (fun _ e -> eval e env) LispNil with
    | LispStr s -> s
    | other -> failwithf "ожидалась строка, получено %s" (prettyPrint other)

let private call (session: Env) (json: string) : JsonElement =
    JsonDocument.Parse(AgentApi.handleJsonRequest session json).RootElement

let private mathReq (session: Env) (code: string) (steps: string) : JsonElement =
    call session (JsonSerializer.Serialize({| op = "math"; code = code; steps = steps |}))

let private sys = "(list '(= (+ (^ x 2) (^ y 2)) 5) '(= (* x y) 2))"

[<Fact>]
let ``with-step: вложенность, after и comment-функция, отбрасывание при #f и ошибке`` () =
    let env = newEnv ()
    run env """
      (define (st1-try ok) (with-step ('attempt "Попытка" 'e) (record-step 'noise "Шум" "" 1 2) (if ok 'да #f)))
      (define (st1-fail) (with-step ('boom "Ошибка" 'e) (record-step 'noise "Шум" "" 1 2) (error "сбой")))
      (define (st1-main)
        (with-step ('outer "Внешний" '(+ a b) :comment (lambda (r) (string-append "получено " (to-string r)))
                    :after (lambda (r) (list '* 2 r)))
          (st1-try #f)
          (try (st1-fail) (lambda (e) #f))
          (with-step ('inner "Внутренний" 'u :level 'detail) (record-step 'leaf "Лист" "к" 1 1) 'v)
          (st1-try #t)
          'w))
    """ |> ignore
    let r = run env "(capture-step-log st1-main)"
    Assert.Equal("(w ((outer \"Внешний\" \"получено w\" (+ a b) (* 2 w) main ((inner \"Внутренний\" \"\" u v detail ((leaf \"Лист\" \"к\" 1 1 main () 0)) 0) (attempt \"Попытка\" \"\" e да main ((noise \"Шум\" \"\" 1 2 main () 0)) 0)) 0)))", r)
    Assert.Equal("(outer inner leaf attempt noise)", run env "(step-rules (cadr (capture-step-log st1-main)))")
    Assert.Equal("detail", run env "(step-level (step-find 'inner (cadr (capture-step-log st1-main))))")
    Assert.Equal("#f", run env "(step-find 'boom (cadr (capture-step-log st1-main)))")
    // ошибка в теле пробрасывается, рамка не остаётся открытой: следующий шаг — на верхнем уровне
    Assert.Equal("(ok ((after-error \"\" \"\" 1 2 main () 0)))",
                 run env "(capture-step-log (lambda () (try (st1-fail) (lambda (e) #f)) (record-step 'after-error \"\" \"\" 1 2) 'ok))")
    // неверные опции — ошибка раскрытия
    Assert.Contains("with-step: опции", (Assert.ThrowsAny<exn>(fun () -> run env "(with-step ('a \"t\" 1 :bad 2) 3)" |> ignore)).Message)

[<Fact>]
let ``with-step: нулевая стоимость — при выключенном журнале rule, заголовок, «до» и опции не вычисляются`` () =
    let env = newEnv ()
    run env "(step-log-off)" |> ignore
    run env """
      (define st2-count 0)
      (define (st2-cost x) (set! st2-count (+ st2-count 1)) x)
      (define (st2-f) (with-step ((st2-cost 'r) (st2-cost "Т") (st2-cost 'до) :comment (st2-cost "к") :after (st2-cost (lambda (v) v))) 42))
    """ |> ignore
    Assert.Equal("42", run env "(st2-f)")
    Assert.Equal("0", run env "st2-count")
    // включён — вычисляются (rule, заголовок, до, comment, after — 5 раз)
    Assert.Equal("(42 ((r \"Т\" \"к\" до 42 main () 0)))", run env "(capture-step-log (lambda () (st2-f)))")
    Assert.Equal("5", run env "st2-count")
    // record-step при выключенном журнале — #f; call-with-step без журнала просто вызывает thunk
    Assert.Equal("#f", run env "(record-step 'a \"t\" \"c\" 1 2)")
    Assert.Equal("7", run env "(call-with-step 'a \"t\" 1 (lambda () 7))")

[<Fact>]
let ``capture-step-log с уровнем: brief, full, trace; steps-text — дерево с нумерацией`` () =
    let env = newEnv ()
    let rulesAt (level: string) = run env (sprintf "(step-rules (cadr (capture-step-log (lambda () (solve %s '(x y))) '%s)))" sys level)
    Assert.Equal("(polynomial-system)", rulesAt "brief")
    Assert.Equal("(polynomial-system triangular-system groebner-basis fglm)", rulesAt "full")
    Assert.Equal("#f", run env (sprintf "(caddr (capture-step-log (lambda () (solve %s '(x y))) 'full))" sys))
    // trace — плюс шаги упрощателя (detail, rule simplify:имя)
    let tr = run env "(step-rules (cadr (capture-step-log (lambda () (simplify '(+ x x (sin (* 1/2 pi))))) 'trace)))"
    Assert.Equal("(simplify:exact-value simplify:collect-terms)", tr)
    Assert.Equal("()", run env "(cadr (capture-step-log (lambda () (simplify '(+ x x))) 'full))")
    // simplify-steps внутри trace по-прежнему работает
    Assert.Equal("((collect-terms (+ x x) (* 2 x)))", run env "(car (capture-step-log (lambda () (simplify-steps '(+ x x))) 'trace))")
    Assert.Contains("уровень шагов brief | full | trace", (Assert.ThrowsAny<exn>(fun () -> run env "(capture-step-log (lambda () 1) 'zzz)" |> ignore)).Message)
    // печать дерева
    let text = runStr env (sprintf "(steps-text (cadr (capture-step-log (lambda () (solve %s '(x y))) 'full)))" sys)
    let lines = text.Split('\n')
    Assert.StartsWith("1. Нелинейная система: метод базисов Грёбнера: [-5 + x^2 + y^2, -2 + x*y] ⇒ [[x = ", lines.[0])
    Assert.Equal("   система многочленов приводится к треугольному виду, затем решается обратной подстановкой", lines.[1])
    Assert.StartsWith("   1.1 Приведение к треугольному виду", lines.[2])
    Assert.StartsWith("       1.1.1 Базис Грёбнера: ", lines.[4])
    Assert.StartsWith("       1.1.2 Смена порядка мономов (FGLM): ", lines.[6])
    Assert.Equal("(шаги не записаны)", runStr env "(steps-text '())")
    // обрезка: пометка и «скрыто вложенных шагов»
    let deep = "(define (st3-deep n) (if (= n 0) 0 (with-step ('level \"Уровень\" n) (st3-deep (- n 1)) n)))"
    run env deep |> ignore
    let cut = runStr env "(let ((r (capture-step-log (lambda () (st3-deep 10)) 'full))) (steps-text (cadr r) (caddr r)))"
    Assert.Contains("1.1.1.1.1.1.1.1 Уровень: 3 ⇒ 3", cut)
    Assert.Contains("… скрыто вложенных шагов: 2", cut)
    Assert.Contains("… шаги обрезаны: показано 8 из 10 (глубина до 8)", cut)
    Assert.Equal("2", run env "(step-omitted (car (step-children (car (step-children (car (step-children (car (step-children (car (step-children (car (step-children (car (step-children (car (cadr (capture-step-log (lambda () (st3-deep 10)) 'full))))))))))))))))))")
    // глубина 6 теперь показывается целиком
    Assert.DoesNotContain("скрыто", runStr env "(let ((r (capture-step-log (lambda () (st3-deep 6)) 'full))) (steps-text (cadr r) (caddr r)))")

[<Fact>]
let ``язык: steps() печатает дерево и возвращает значение; step_list() — записи с путём`` () =
    let s = AgentApi.makeSession ()
    let r = mathReq s "steps(solve([x^2 + y^2 = 5, x*y = 2], [x, y]))" "none"
    Assert.Equal("answer", r.GetProperty("status").GetString())
    Assert.StartsWith("{[x = -2, y = -1]", r.GetProperty("pretty").GetString())
    let out = r.GetProperty("output").GetString()
    Assert.StartsWith("1. Нелинейная система: метод базисов Грёбнера:", out)
    Assert.DoesNotContain("1.1", out)                                   // brief по умолчанию
    let full = (mathReq s "steps(solve([x^2 + y^2 = 5, x*y = 2], [x, y]), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("   1.1 Приведение к треугольному виду", full)
    Assert.Contains("1.1.2 Смена порядка мономов (FGLM)", full)
    let none = (mathReq s "steps(1 + 2)" "none")
    Assert.Equal("3", none.GetProperty("pretty").GetString())
    Assert.Equal("(шаги не записаны)", none.GetProperty("output").GetString().Trim())
    // step_list: вектор записей [путь, rule, заголовок, пояснение, до, после, уровень, скрыто]
    let sl = mathReq s "L := step_list(solve([x^2 + y^2 = 5, x*y = 2], [x, y])); [L[1][1], L[2][1], L[3][2], L[4][2], L[3][7]]" "none"
    Assert.Equal("[\"1\", \"1.1\", \"groebner-basis\", \"fglm\", \"main\"]", sl.GetProperty("pretty").GetString().Split('\n') |> Array.last)
    Assert.Equal("error", (mathReq s "steps()" "none").GetProperty("status").GetString())
    Assert.Equal("error", (mathReq s "steps(x, \"много\")" "none").GetProperty("status").GetString())

[<Fact>]
let ``ToolResponse: steps — дерево с rule/title/level/children; brief и full различаются; trace`` () =
    let s = AgentApi.makeSession ()
    let code = "solve([x^2 + y^2 = 5, x*y = 2], [x, y])"
    let brief = (mathReq s code "brief").GetProperty("steps")
    Assert.Equal(1, brief.GetArrayLength())
    let top = brief.[0]
    Assert.Equal<string list>([ "rule"; "title"; "comment"; "before"; "before_pretty"; "before_latex"; "after"; "after_pretty"; "after_latex"; "level"; "children" ],
                              top.EnumerateObject() |> Seq.map (fun p -> p.Name) |> List.ofSeq)
    Assert.Equal("polynomial-system", top.GetProperty("rule").GetString())
    Assert.Equal("Нелинейная система: метод базисов Грёбнера", top.GetProperty("title").GetString())
    Assert.Equal("main", top.GetProperty("level").GetString())
    Assert.Equal("[-5 + x^2 + y^2, -2 + x*y]", top.GetProperty("before_pretty").GetString())
    Assert.Equal("(list (+ -5 (^ x 2) (^ y 2)) (+ -2 (* x y)))", top.GetProperty("before").GetString())
    Assert.Equal(0, top.GetProperty("children").GetArrayLength())
    let full = (mathReq s code "full").GetProperty("steps").[0]
    let tri = full.GetProperty("children").[0]
    Assert.Equal("triangular-system", tri.GetProperty("rule").GetString())
    let kids = tri.GetProperty("children").EnumerateArray() |> Seq.map (fun e -> e.GetProperty("rule").GetString()) |> List.ofSeq
    Assert.Equal<string list>([ "groebner-basis"; "fglm" ], kids)
    // trace: шаги упрощателя — detail
    let tr = (call s "{\"op\":\"simplify\",\"code\":\"x + x\",\"syntax\":\"math\",\"steps\":\"trace\"}").GetProperty("steps")
    Assert.True(tr.EnumerateArray() |> Seq.exists (fun e -> e.GetProperty("rule").GetString() = "simplify:collect-terms"
                                                             && e.GetProperty("level").GetString() = "detail"))
    Assert.Equal(0, (call s "{\"op\":\"simplify\",\"code\":\"x + x\",\"syntax\":\"math\",\"steps\":\"full\"}").GetProperty("steps").GetArrayLength())
    Assert.Equal("error", (mathReq s "1" "много").GetProperty("status").GetString())
    // обрезка — пометка в warnings и omitted у узла
    let deep = "(define (st5-deep n) (if (= n 0) 0 (with-step ('level \"Уровень\" n) (st5-deep (- n 1)) n)))"
    call s (JsonSerializer.Serialize({| op = "eval"; code = deep |})) |> ignore
    let d = call s (JsonSerializer.Serialize({| op = "eval"; code = "(st5-deep 10)"; steps = "full" |}))
    let rec deepest (e: JsonElement) = let ch = e.GetProperty("children") in if ch.GetArrayLength() = 0 then e else deepest ch.[0]
    Assert.Equal(2, (deepest (d.GetProperty("steps").[0])).GetProperty("omitted").GetInt32())
    Assert.Contains("шаги обрезаны: показано 8 из 10", d.GetProperty("warnings").[0].GetString())

[<Fact>]
let ``MCP: steps — enum с trace, обрезка дерева по MaxSteps и длине выражений`` () =
    let spec = McpHost.tools |> List.find (fun t -> t.Name = "solve")
    let p = spec.Params |> List.find (fun p -> p.Name = "steps")
    Assert.Equal(McpHost.PEnum [ "none"; "brief"; "full"; "trace" ], p.Kind)
    let leaf (r: string) : ToolResponse.StepEntry =
        { Rule = r; Title = ""; Comment = ""; Before = String.replicate 50 "x"; BeforePretty = "b"; BeforeLatex = ""
          After = "a"; AfterPretty = "a"; AfterLatex = ""
          Level = "main"; Children = []; Omitted = 0 }
    let tree = [ { leaf "p" with Children = [ leaf "c1"; leaf "c2"; leaf "c3" ] }; leaf "q" ]
    let r = { ToolResponse.empty ToolResponse.Answer with Steps = Some tree }
    let limited = McpHost.limitResponse { McpHost.defaultLimits with MaxSteps = 3; MaxStepChars = 10 } 1000 0L r
    let st = limited.Steps.Value
    Assert.Equal(1, st.Length)
    Assert.Equal<string list>([ "c1"; "c2" ], st.Head.Children |> List.map (fun e -> e.Rule))
    Assert.Equal("xxxxxxxxxx …", st.Head.Before)
    Assert.Contains("steps обрезаны: показаны первые 3 из 5 шагов", limited.Warnings)

[<Fact>]
let ``checkSteps: инвариант «каждый шаг эквивалентен» — true, false с контрпримером, skipped`` () =
    let s = AgentApi.makeSession ()
    run s """
      (define (st6-demo)
        (with-step ('expand-square "Раскрытие квадрата" '(^ (+ x 1) 2))
          (record-step 'good "Верно" "" '(* 2 (+ x 1)) '(+ 2 (* 2 x)))
          (record-step 'bad "Неверно" "" '(^ (+ x 1) 2) '(+ (^ x 2) 1))
          (record-step 'solve-eq "Уравнение" "" '(= x 1) '(list 1))
          '(+ 1 (* 2 x) (^ x 2))))""" |> ignore
    let _, steps, _ = AlgoBuiltins.captureSteps None (fun () -> eval (List.head (readAll "(st6-demo)")) s)
    let checks = AgentApi.checkSteps s [] steps
    Assert.Equal<string list>([ "1"; "1.1"; "1.2"; "1.3" ], checks |> List.map (fun c -> c.StepPath))
    Assert.Equal<string list>([ "true"; "true"; "false"; "skipped" ], checks |> List.map (fun c -> c.Verdict))
    let failed = AgentApi.failedSteps checks
    Assert.Equal<string list>([ "bad" ], failed |> List.map (fun c -> c.StepRule))
    Assert.Contains("контрпример", failed.Head.Why)
    Assert.Equal("skipped", (AgentApi.checkSteps s [ "bad" ] steps |> List.find (fun c -> c.StepRule = "bad")).Verdict)
    // сквозной пример: шаги solve-системы — не равенства выражений (списки) → skipped, ложных нет
    let _, solveSteps = AgentApi.mathSteps s "solve([x^2 + y^2 = 5, x*y = 2], [x, y])"
    let sc = AgentApi.checkSteps s [] solveSteps
    Assert.Equal(4, sc.Length)
    Assert.Empty(AgentApi.failedSteps sc)

// --- Шаг S.2: шаги diff и simplify ---

// rule всех шагов в порядке обхода в глубину (step-rules) для кода Lisp
let private rulesOf (env: Env) (code: string) : string =
    run env (sprintf "(step-rules (cadr (capture-step-log (lambda () %s) 'full)))" code)

[<Fact>]
let ``defrule :title — заголовок шага; без :title — «правило имя»; условие и :ac в любом порядке с :title`` () =
    let s = AgentApi.makeSession ()
    try
        run s "(defrule ttl-rule-a (ttl-fa ?x) ?x :title \"Мой заголовок\")" |> ignore
        run s "(defrule ttl-rule-b (ttl-fb ?x) ?x)" |> ignore
        run s "(defrule ttl-rule-c (ttl-fc (+ ?x ?r...)) ?x (integer? 1) :title \"Третье\" :ac)" |> ignore
        let probe (name: string) (expr: string) (getter: string) =
            run s (sprintf "(%s (step-find 'simplify:rule:%s (cadr (capture-step-log (lambda () (step-simplify '%s)) 'full))))" getter name expr)
        Assert.Contains("Мой заголовок", probe "ttl-rule-a" "(ttl-fa 1)" "step-title")
        Assert.Contains("правило ttl-rule-b", probe "ttl-rule-b" "(ttl-fb 1)" "step-title")
        Assert.Contains("Третье", probe "ttl-rule-c" "(ttl-fc (+ p q r))" "step-title")
        Assert.Contains("остальные слагаемые", probe "ttl-rule-c" "(ttl-fc (+ p q r))" "step-comment")
    finally
        for n in [ "ttl-rule-a"; "ttl-rule-b"; "ttl-rule-c" ] do run s (sprintf "(remove-rule '%s)" n) |> ignore

[<Fact>]
let ``diff: правила — произведение + степенная + trig; цепное правило; частное`` () =
    let s = AgentApi.makeSession ()
    Assert.Equal("(differentiation diff-product diff-power diff-trig simplify-result)",
                 rulesOf s "(diff 'x '(* (^ x 2) (sin x)))")
    Assert.Equal("(differentiation diff-chain diff-exp diff-power simplify-result)",
                 rulesOf s "(diff 'x '(exp (^ x 2)))")
    Assert.Equal("(differentiation diff-quotient diff-sum diff-variable diff-constant diff-sum diff-variable diff-constant simplify-result)",
                 rulesOf s "(diff 'x '(/ (+ x 1) (- x 1)))")
    // постоянный множитель: ни шага для 3, ни для x; сумма: константа — detail
    Assert.Equal("(differentiation diff-sum diff-constant-multiple diff-power diff-constant simplify-result)",
                 rulesOf s "(diff 'x '(+ (* 3 (^ x 2)) 5))")
    // x — переменная: единственный лист; результат уже прост — шага упрощения нет
    Assert.Equal("(differentiation diff-variable)", rulesOf s "(diff 'x 'x)")
    Assert.Equal("(differentiation diff-constant)", rulesOf s "(diff 'x 7)")

[<Fact>]
let ``diff: brief — один шаг, full — дерево; comment и before/after в шагах`` () =
    let s = AgentApi.makeSession ()
    let code = "diff(x^2*sin(x), x)"
    let brief = (mathReq s code "brief").GetProperty("steps")
    Assert.Equal(1, brief.GetArrayLength())
    Assert.Equal("differentiation", brief.[0].GetProperty("rule").GetString())
    Assert.Equal("Дифференцирование по x", brief.[0].GetProperty("title").GetString())
    Assert.Equal(0, brief.[0].GetProperty("children").GetArrayLength())
    let full = (mathReq s code "full").GetProperty("steps").[0]
    let kids = full.GetProperty("children").EnumerateArray() |> List.ofSeq
    Assert.Equal<string list>([ "diff-product"; "simplify-result" ], kids |> List.map (fun e -> e.GetProperty("rule").GetString()))
    Assert.Equal("d/dx(x^2*sin(x))", kids.[0].GetProperty("before_pretty").GetString())
    Assert.Equal("(u·v)' = u'·v + u·v'", kids.[0].GetProperty("comment").GetString())
    Assert.Equal("2x*sin(x) + x^2*cos(x)", kids.[0].GetProperty("after_pretty").GetString())
    Assert.Equal("detail", kids.[1].GetProperty("level").GetString())
    // печать дерева в языке
    let out = (mathReq s "steps(diff(x^2*sin(x), x), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("1. Дифференцирование по x: d/dx(x^2*sin(x)) ⇒ 2x*sin(x) + x^2*cos(x)", out)
    Assert.Contains("1.1.2 Производная тригонометрической функции: d/dx(sin(x)) ⇒ cos(x)", out)
    // внешняя функция цепного правила — по формальной переменной
    let chain = (mathReq s "steps(diff(sin(x^2), x), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("Цепное правило (сложная функция): d/dx(sin(x^2)) ⇒ 2x*cos(x^2)", chain)
    Assert.Contains("Производная тригонометрической функции: d/du(sin(u)) ⇒ cos(u)", chain)

[<Fact>]
let ``diff: каждый шаг — эквивалентное преобразование (checkSteps), в том числе d/dx(...)`` () =
    let s = AgentApi.makeSession ()
    let exprs =
        [ "(* (^ x 2) (sin x))"; "(exp (^ x 2))"; "(/ (+ x 1) (- x 1))"; "(+ (* 3 (^ x 2)) 5 (log x))"
          "(sqrt (+ 1 (^ x 2)))"; "(^ x x)"; "(* x (atan (* 2 x)) (cosh x))"; "(/ 1 (tan x))"; "(- (^ (+ x 1) 3))" ]
    for e in exprs do
        let _, steps, _ = AlgoBuiltins.captureSteps None (fun () -> eval (List.head (readAll (sprintf "(diff 'x '%s)" e))) s)
        let checks = AgentApi.checkSteps s [] steps
        Assert.True(checks.Length >= 3, e)
        Assert.Empty(AgentApi.failedSteps checks)
        // все шаги, кроме разве что численно подтверждённых, доказаны символьно или численно: «true»/«unknown» без контрпримера
        Assert.True(checks |> List.forall (fun c -> c.Verdict = "true" || c.Verdict = "unknown"), e)
        Assert.True((checks |> List.filter (fun c -> c.Verdict = "true")).Length * 2 >= checks.Length, e)

[<Fact>]
let ``simplify: шаг simplification с преобразованиями упрощателя; неизменное выражение шага не даёт`` () =
    let s = AgentApi.makeSession ()
    Assert.Equal("(simplification simplify:pythagorean)", rulesOf s "(step-simplify '(+ (^ (sin x) 2) (^ (cos x) 2)))")
    Assert.Equal("(simplification simplify:merge-powers simplify:exact-value simplify:collect-terms)",
                 rulesOf s "(step-simplify '(+ (* x (^ x 2)) (* 2 (^ x 3)) (sin 0)))")
    Assert.Equal("nil", rulesOf s "(step-simplify '(+ x y))")
    // язык: steps(simplify(e)) берёт выражение как записано, русские заголовки; brief — только итог
    let full = (mathReq s "steps(simplify(sin(x)^2 + cos(x)^2), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("1. Упрощение: sin(x)^2 + cos(x)^2 ⇒ 1", full)
    Assert.Contains("1.1 основное тригонометрическое тождество: sin(x)^2 + cos(x)^2 ⇒ 1", full)
    let brief = (mathReq s "steps(simplify(sin(x)^2 + cos(x)^2))" "none").GetProperty("output").GetString()
    Assert.DoesNotContain("1.1", brief)
    // MCP simplify: дерево в ответе; шаги упрощения — detail
    let r = call s "{\"op\":\"simplify\",\"code\":\"(+ (^ (sin x) 2) (^ (cos x) 2))\",\"steps\":\"full\"}"
    let top = r.GetProperty("steps").[0]
    Assert.Equal("simplification", top.GetProperty("rule").GetString())
    let ch = top.GetProperty("children").[0]
    Assert.Equal("simplify:pythagorean", ch.GetProperty("rule").GetString())
    Assert.Equal("detail", ch.GetProperty("level").GetString())
    let b = call s "{\"op\":\"simplify\",\"code\":\"(+ (^ (sin x) 2) (^ (cos x) 2))\",\"steps\":\"brief\"}"
    Assert.Equal(0, b.GetProperty("steps").[0].GetProperty("children").GetArrayLength())
    // каждое преобразование эквивалентно
    let _, steps, _ = AlgoBuiltins.captureSteps None (fun () -> eval (List.head (readAll "(step-simplify '(+ (* x (^ x 2)) (* 2 (^ x 3)) (sin 0)))")) s)
    Assert.Empty(AgentApi.failedSteps (AgentApi.checkSteps s [] steps))

[<Fact>]
let ``AC.3: шаг simplify:rule:имя для правила :ac с привязками в пояснении (ru и en)`` () =
    let s = AgentApi.makeSession ()
    Assert.Equal("(simplification simplify:rule:pythagorean-common-factor)",
                 rulesOf s "(step-simplify '(+ 3 (* z (^ (sin x) 2)) (* z (^ (cos x) 2)) y))")
    let full = (mathReq s "steps(simplify(3 + z*sin(x)^2 + z*cos(x)^2 + y), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("Основное тригонометрическое тождество (общий множитель)", full)
    Assert.Contains("u = x, множитель c = z, остальные слагаемые: 3 + y", full)
    let en = (mathReq s "steps(simplify(3 + z*sin(x)^2 + z*cos(x)^2 + y), \"full\", \"en\")" "none").GetProperty("output").GetString()
    Assert.Contains("Pythagorean trigonometric identity (common factor)", en)
    Assert.Contains("u = x, factor c = z, remaining terms: 3 + y", en)
    Assert.DoesNotMatch("[а-яА-Я]", en)
    // числовой коэффициент — прежний шаг упрощателя, правило не срабатывает второй раз
    Assert.Equal("(simplification simplify:pythagorean)", rulesOf s "(step-simplify '(+ 3 (* 2 (^ (sin x) 2)) (* 2 (^ (cos x) 2)) y))")
    // правило :ac без привязок-остатков: пояснение пустое; каждое преобразование эквивалентно
    let _, steps, _ = AlgoBuiltins.captureSteps None (fun () -> eval (List.head (readAll "(step-simplify '(+ 3 (* z (^ (sin x) 2)) (* z (^ (cos x) 2)) y))")) s)
    Assert.Empty(AgentApi.failedSteps (AgentApi.checkSteps s [] steps))

[<Fact>]
let ``diff/simplify: нулевая стоимость — журнал выключен, шаги не строятся, результат тот же`` () =
    let s = AgentApi.makeSession ()
    Assert.False(StepLog.Journal.Enabled)
    StepLog.Journal.Clear()
    let exprs = [ "(* (^ x 2) (sin x))"; "(exp (^ x 2))"; "(/ (+ x 1) (- x 1))"; "(^ x x)"; "(integrate (* x (exp x)) x)" ]
    for e in exprs do
        let code = sprintf "(diff 'x '%s)" e
        let off = run s code
        Assert.Empty(StepLog.Journal.Steps)
        let on = run s (sprintf "(car (capture-step-log (lambda () %s)))" code)
        Assert.Equal(off, on)
    run s "(step-simplify '(+ (^ (sin x) 2) (^ (cos x) 2)))" |> ignore
    Assert.Empty(StepLog.Journal.Steps)
    Assert.False(StepLog.Journal.Enabled)
    // после захвата признак trace упрощателя не остаётся включённым
    Assert.False(StepLog.Journal.TraceSimplify)

// --- Шаг S.3: шаги integrate ---

// rule всех шагов в порядке обхода в глубину — полное дерево, без лимитов уровней (capture-step-log без уровня)
let private allRulesOf (env: Env) (code: string) : string =
    run env (sprintf "(step-rules (cadr (capture-step-log (lambda () %s))))" code)

[<Fact>]
let ``AC.4: табличный интеграл через ac-match — тот же шаг int-table, привязки в пояснении (ru и en)`` () =
    let s = AgentApi.makeSession ()
    Assert.Equal("(integration int-table)", allRulesOf s "(integrate '(^ (+ a b (* 3 (^ x 2))) -3/2) 'x)")
    let full = (mathReq s "steps(integrate(1/(a+b+3*x^2)^(3/2), x), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("Табличный интеграл", full)
    Assert.Contains("∫ 1/(c + k*u^2)^(3/2) du = u/(c*(c + k*u^2)^(1/2)) (c ≠ 0, k ≠ 0); c = a + b, k = 3", full)
    let en = (mathReq s "steps(integrate(1/(a+b+3*x^2)^(3/2), x), \"full\", \"en\")" "none").GetProperty("output").GetString()
    Assert.Contains("Table integral", en)
    Assert.Contains("c = a + b, k = 3", en)
    Assert.DoesNotMatch("[а-яА-Я]", en)
    // шаг — верное равенство; единица коэффициента (c − u²): k = −1
    let _, steps, _ = AlgoBuiltins.captureSteps None (fun () -> eval (List.head (readAll "(integrate '(^ (+ 1 (* -1 (^ x 2))) -3/2) 'x)")) s)
    Assert.Contains("c = 1, k = -1", (mathReq s "steps(integrate(1/(1-x^2)^(3/2), x), \"full\")" "none").GetProperty("output").GetString())
    Assert.Empty(AgentApi.failedSteps (AgentApi.checkSteps s [] steps))

[<Fact>]
let ``integrate: деревья правил — по частям, подстановка, степени sin, простые дроби, линейность+таблица`` () =
    let s = AgentApi.makeSession ()
    // по частям: ∫ x·e^x; неудавшаяся подстановка (int-usub пробует кандидаты) в журнал не попадает
    Assert.Equal("(integration int-by-parts int-parts-choice int-table int-parts-formula int-table)",
                 allRulesOf s "(integrate '(* x (exp x)) 'x)")
    // подстановка u = x²: константа 2 выносится, затем замена, интеграл по u, обратная замена
    Assert.Equal("(integration int-linearity int-substitution int-substitution-change int-linearity int-table int-back-substitution)",
                 allRulesOf s "(integrate '(* 2 x (cos (^ x 2))) 'x)")
    Assert.Equal("(integration int-trig-powers)", allRulesOf s "(integrate '(^ (sin x) 2) 'x)")
    Assert.Equal("(integration simplify-integrand int-partial-fractions apart int-partial-fraction-term int-partial-fraction-term)",
                 allRulesOf s "(integrate '(/ 1 (- (^ x 2) 1)) 'x)")
    Assert.Equal("(integration simplify-integrand int-partial-fractions apart int-partial-fraction-term int-partial-fraction-term int-partial-fraction-term)",
                 allRulesOf s "(integrate '(/ (+ (^ x 2) 1) (- (^ x 3) x)) 'x)")
    // перестановка слагаемых (x³ + 2x → 2x + x³) — не шаг
    Assert.Equal("(integration int-linearity int-linearity int-table int-table)",
                 allRulesOf s "(integrate '(+ (^ x 3) (* 2 x)) 'x)")
    // циклический случай и произведение sin·cos (N1: int-final разложил 1/2(...) — добавился simplify-result)
    Assert.Equal("(integration int-by-parts int-parts-choice int-table int-parts-formula int-parts-choice int-table int-parts-formula int-parts-cycle simplify-result)",
                 allRulesOf s "(integrate '(* (exp x) (sin x)) 'x)")
    Assert.Equal("(integration int-trig-product int-product-to-sum int-linearity int-linearity int-table int-table simplify-result)",
                 allRulesOf s "(integrate '(* (sin x) (cos (* 2 x))) 'x)")
    // рациональные функции: Эрмит + ЛРТ (rootsum), только ЛРТ
    Assert.Equal("(integration simplify-integrand int-rational-function int-rational-lrt)",
                 allRulesOf s "(integrate '(/ 1 (+ (^ x 3) x 1)) 'x)")
    Assert.Equal("(integration simplify-integrand int-rational-function int-rational-hermite int-rational-lrt)",
                 allRulesOf s "(integrate '(/ 1 (^ (+ (^ x 3) x 1) 2)) 'x)")
    // корень из квадратного трёхчлена
    Assert.Equal("(integration simplify-integrand int-sqrt-quad)", allRulesOf s "(integrate '(sqrt (+ (^ x 2) 1)) 'x)")

[<Fact>]
let ``integrate: определённый и несобственный интеграл — int-definite, int-limits, int-improper`` () =
    let s = AgentApi.makeSession ()
    Assert.Equal("(int-definite integration int-table int-limits)", allRulesOf s "(integrate '(^ x 2) 'x 0 1)")
    Assert.Equal("(int-definite integration int-table int-improper)", allRulesOf s "(integrate '(^ x -2) 'x 1 'inf)")
    // расходимость на [0, 1] доказана (definite): ответ невычисленный, шаги di-* остаются
    Assert.Equal("(di-definite di-divergent)", allRulesOf s "(integrate '(/ 1 x) 'x 0 1)")
    // Q.1: доказанный отказ Риша теперь виден и при вызове через integrate (невычисленный интеграл)
    Assert.Equal("(risch risch-nonelementary)", allRulesOf s "(integrate '(exp (^ x 2)) 'x)")
    Assert.Equal("nil", allRulesOf s "(integrate '(/ 1 (- (^ x 2) 1)) 'x 0 2)")
    // язык: печать определённого интеграла и подстановки пределов
    let out = (mathReq s "steps(integrate(x^2, x, 0, 1), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("1. Определённый интеграл: ∫_0^1 x^2 dx ⇒ 1/3", out)
    Assert.Contains("1.1 Интегрирование по x: ∫ x^2 dx ⇒ 1/3*x^3", out)
    Assert.Contains("1.2 Подстановка пределов: F(b) − F(a): 1/3*1^3 - 1/3*0^3 ⇒ 1/3", out)

[<Fact>]
let ``integrate: язык — пример с частями и подстановкой, brief и full, аргумент как записан`` () =
    let s = AgentApi.makeSession ()
    let full = (mathReq s "steps(integrate(x*exp(x), x), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("1. Интегрирование по x: ∫ x*exp(x) dx ⇒ x*exp(x) - exp(x)", full)
    Assert.Contains("1.1 Интегрирование по частям: ∫ x*exp(x) dx ⇒ x*exp(x) - exp(x)", full)
    Assert.Contains("∫ u dv = u·v − ∫ v du", full)
    // порядок как в учебнике: выбор u и dv (внутри — нахождение v), формула, интеграл ∫ v du
    Assert.Contains("1.1.1 Выбор u и dv: ∫ x*exp(x) dx ⇒ [u = x, dv = exp(x)*dx]", full)
    Assert.Contains("du = 1 dx; v = ∫ dv = exp(x)", full)
    Assert.Contains("1.1.1.1 Табличный интеграл: ∫ exp(x) dx ⇒ exp(x)", full)
    Assert.Contains("1.1.2 Формула интегрирования по частям: ∫ x*exp(x) dx ⇒ x*exp(x) - ∫ exp(x) dx", full)
    Assert.Contains("здесь u = x, v = exp(x), du = 1 dx", full)
    Assert.Contains("1.1.3 Табличный интеграл: ∫ exp(x) dx ⇒ exp(x)", full)
    Assert.Contains("∫ exp(u) du = exp(u)", full)
    let sub = (mathReq s "steps(integrate(2*x*cos(x^2), x), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("Метод подстановки: ∫ x*cos(x^2) dx ⇒ 1/2*sin(x^2)", sub)
    Assert.Contains("u = x^2, du = 2x dx", sub)
    Assert.Contains("Замена переменной: ∫ x*cos(x^2) dx ⇒ ∫ 1/2*cos(u) du", sub)
    Assert.Contains("Обратная замена: 1/2*sin(u) ⇒ 1/2*sin(x^2)", sub)
    // brief — один шаг
    let brief = (mathReq s "steps(integrate(x*exp(x), x))" "none").GetProperty("output").GetString()
    Assert.Contains("1. Интегрирование по x", brief)
    Assert.DoesNotContain("1.1", brief)
    // аргумент берётся как записан: (x+1)/(x-1) — правило частного видно в diff
    let dq = (mathReq s "steps(diff((x+1)/(x-1), x), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("Правило частного: d/dx((x + 1)/(x - 1))", dq)
    // значения присвоенных имён подставляются; функции пользователя — обычное вычисление
    let named = (mathReq s "f := x^2; steps(integrate(f, x), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("1. Интегрирование по x: ∫ x^2 dx ⇒ 1/3*x^3", named)
    let userFn = (mathReq s "g(t) := t^3; steps(integrate(g(x), x), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("1. Интегрирование по x: ∫ x^3 dx ⇒ 1/4*x^4", userFn)
    mathReq s "clear()" "none" |> ignore
    // ответ тот же, что без steps
    Assert.Equal("x*exp(x) - exp(x)", (mathReq s "integrate(x*exp(x), x)" "none").GetProperty("pretty").GetString())

[<Fact>]
let ``integrate: ToolResponse — дерево шагов, before_pretty «∫ f dx», brief ≠ full`` () =
    let s = AgentApi.makeSession ()
    let full = (call s "{\"op\":\"integrate\",\"code\":\"x*exp(x)\",\"var\":\"x\",\"syntax\":\"math\",\"steps\":\"full\"}").GetProperty("steps").[0]
    Assert.Equal("integration", full.GetProperty("rule").GetString())
    Assert.Equal("Интегрирование по x", full.GetProperty("title").GetString())
    Assert.Equal("∫ x*exp(x) dx", full.GetProperty("before_pretty").GetString())
    Assert.Equal("x*exp(x) - exp(x)", full.GetProperty("after_pretty").GetString())
    let kids = full.GetProperty("children").EnumerateArray() |> List.ofSeq
    Assert.Equal<string list>([ "int-by-parts" ], kids |> List.map (fun e -> e.GetProperty("rule").GetString()))
    let brief = (call s "{\"op\":\"integrate\",\"code\":\"x*exp(x)\",\"var\":\"x\",\"syntax\":\"math\",\"steps\":\"brief\"}").GetProperty("steps").[0]
    Assert.Equal(0, brief.GetProperty("children").GetArrayLength())
    let def = (call s "{\"op\":\"integrate\",\"code\":\"x^2\",\"var\":\"x\",\"syntax\":\"math\",\"from\":\"0\",\"to\":\"1\",\"steps\":\"brief\"}").GetProperty("steps").[0]
    Assert.Equal("int-definite", def.GetProperty("rule").GetString())
    Assert.Equal("∫_0^1 x^2 dx", def.GetProperty("before_pretty").GetString())

[<Fact>]
let ``integrate: каждый шаг — эквивалентное преобразование (checkSteps, d/dx после = до)`` () =
    let s = AgentApi.makeSession ()
    let exprs =
        [ "(* x (exp x))"; "(* 2 x (cos (^ x 2)))"; "(^ (sin x) 2)"; "(/ 1 (- (^ x 2) 1))"; "(/ (+ (^ x 2) 1) (- (^ x 3) x))"
          "(+ (^ x 3) (* 2 x))"; "(* (exp x) (sin x))"; "(* (sin x) (cos (* 2 x)))"; "(/ 1 (^ (+ (^ x 3) x 1) 2))"
          "(/ 1 (^ (+ (^ x 2) 1) 2))"; "(* (^ x 2) (log x))"; "(/ 1 (sqrt (+ (^ x 2) 4)))"; "(* x (sqrt (+ 1 (^ x 2))))" ]
    for e in exprs do
        let _, steps, _ = AlgoBuiltins.captureSteps None (fun () -> eval (List.head (readAll (sprintf "(integrate '%s 'x)" e))) s)
        let checks = AgentApi.checkSteps s [] steps
        Assert.True(checks.Length >= 2, e)
        Assert.Empty(AgentApi.failedSteps checks)
        Assert.True((checks |> List.filter (fun c -> c.Verdict = "true" || c.Verdict = "unknown")).Length * 2 >= checks.Length, e)
        // верхний шаг integration проверен (d/dx F = f), а не пропущен
        Assert.True(checks.Head.Verdict <> "skipped", e)
    // определённый: подстановка пределов — эквивалентность выражений
    let _, dsteps, _ = AlgoBuiltins.captureSteps None (fun () -> eval (List.head (readAll "(integrate '(^ x 2) 'x 0 1)")) s)
    Assert.Empty(AgentApi.failedSteps (AgentApi.checkSteps s [] dsteps))
    // ложный шаг интеграла ловится
    let _, bad, _ =
        AlgoBuiltins.captureSteps None (fun () ->
            eval (List.head (readAll "(record-step 'int-bad \"Неверно\" \"\" '(int/dx (^ x 2)) '(^ x 2))")) s)
    Assert.Equal<string list>([ "int-bad" ], AgentApi.failedSteps (AgentApi.checkSteps s [] bad) |> List.map (fun c -> c.StepRule))

[<Fact>]
let ``integrate: нулевая стоимость — журнал выключен, шагов нет, ответы те же`` () =
    let s = AgentApi.makeSession ()
    Assert.False(StepLog.Journal.Enabled)
    StepLog.Journal.Clear()
    let exprs =
        [ "(* x (exp x))"; "(* 2 x (cos (^ x 2)))"; "(^ (sin x) 2)"; "(/ 1 (- (^ x 2) 1))"; "(/ 1 (+ (^ x 3) x 1))"
          "(* (exp x) (sin x))"; "(exp (^ x 2))" ]
    for e in exprs do
        let code = sprintf "(integrate '%s 'x)" e
        let off = run s code
        Assert.Empty(StepLog.Journal.Steps)
        let on = run s (sprintf "(car (capture-step-log (lambda () %s)))" code)
        Assert.Equal(off, on)
    Assert.Equal(run s "(integrate '(^ x 2) 'x 0 1)", run s "(car (capture-step-log (lambda () (integrate '(^ x 2) 'x 0 1))))")
    Assert.Empty(StepLog.Journal.Steps)
    Assert.False(StepLog.Journal.Enabled)
    // внутренние производные интегратора (проверка ответа, подстановка) не пишут шаги diff
    let rules = allRulesOf s "(integrate '(* 2 x (cos (^ x 2))) 'x)"
    Assert.DoesNotContain("diff", rules)
    Assert.DoesNotContain("differentiation", rules)

// --- Шаг S.4: шаги solve / limit / series, порядок шагов по частям, глубина full 8 ---

[<Fact>]
let ``solve: деревья правил — линейное, квадратное, разложение, обращение функций, радикал, знаменатель, система`` () =
    let s = AgentApi.makeSession ()
    Assert.Equal("(solve-equation solve-move-terms solve-linear)", allRulesOf s "(solve '(= (+ (* 2 x) 3) 7) 'x)")
    // шаг S.5: честный приём — рациональные корни находятся разложением на множители; формула с дискриминантом — только
    // для неприводимого квадратного трёхчлена (иррациональные/комплексные корни)
    Assert.Equal("(solve-equation solve-factor solve-linear solve-linear)", allRulesOf s "(solve '(= (+ (^ x 2) (* -5 x) 6) 0) 'x)")
    Assert.Equal("(solve-equation solve-quadratic)", allRulesOf s "(solve '(= (+ (^ x 2) (* -5 x) 3) 0) 'x)")
    Assert.Equal("(solve-equation solve-quadratic)", allRulesOf s "(solve '(= (- (^ x 2) 2) 0) 'x)")
    Assert.Equal("(solve-equation solve-factor solve-linear)", allRulesOf s "(solve '(= (+ (^ x 2) (* -2 x) 1) 0) 'x)")
    Assert.Equal("(solve-equation solve-factor solve-linear solve-linear solve-linear)", allRulesOf s "(solve '(= (- (^ x 3) x) 0) 'x)")
    // sin x = 1/2 и exp x = 2: перенос, замена t = ядро, линейное по t, обращение функции
    Assert.Equal("(solve-equation solve-move-terms solve-substitution solve-linear solve-inverse-function)", allRulesOf s "(solve '(= (sin x) 1/2) 'x)")
    Assert.Equal("(solve-equation solve-move-terms solve-substitution solve-linear solve-inverse-function)", allRulesOf s "(solve '(= (exp x) 2) 'x)")
    // радикал: возведение в квадрат, затем проверка отсеивает посторонний корень
    Assert.Equal("(solve-equation solve-move-terms solve-square solve-factor solve-linear solve-linear solve-check-roots)",
                 allRulesOf s "(solve '(= (sqrt x) (- x 2)) 'x)")
    // знаменатель с неизвестной
    Assert.Equal("(solve-equation solve-move-terms solve-clear-denominator solve-factor solve-linear solve-linear)",
                 allRulesOf s "(solve '(= (/ 1 x) x) 'x)")
    // линейная система — одна крупная рамка; нелинейная — по-прежнему polynomial-system (без шагов solve-expression внутри)
    Assert.Equal("(solve-linear-system)", allRulesOf s "(solve (list '(= (+ x y) 3) '(= (- x y) 1)) '(x y))")
    Assert.Equal("(polynomial-system triangular-system groebner-basis fglm)", allRulesOf s (sprintf "(solve %s '(x y))" sys))
    // нет решений в вещественных: пустой ответ — рамка сохраняется
    Assert.Equal("(solve-equation solve-quadratic)", allRulesOf s "(solve '(= (+ (^ x 2) 1) 0) 'x)")
    // не умеем — ошибка, шагов нет
    Assert.Equal("nil", allRulesOf s "(try (solve '(= (+ x (cos x)) 0) 'x) (lambda (e) 0))")

[<Fact>]
let ``solve: язык — квадратное уравнение, разложение, уравнение как записано, ответ тот же`` () =
    let s = AgentApi.makeSession ()
    let q = (mathReq s "steps(solve(x^2-5*x+6=0, x), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("1. Решение уравнения относительно x: x^2 - 5x + 6 = 0 ⇒ {2, 3}", q)
    // шаг S.5: рациональные корни — разложение на множители, а не формула с дискриминантом; «или» по-русски
    Assert.Contains("1.1 Разложение на множители: x^2 - 5x + 6 = 0 ⇒ (x - 2)(x - 3) = 0", q)
    Assert.Contains("произведение равно нулю, когда хотя бы один множитель равен нулю: x - 2 = 0 или x - 3 = 0", q)
    Assert.Contains("1.1.1 Линейное уравнение: x - 2 = 0 ⇒ x = 2", q)
    Assert.DoesNotContain("дискриминант", q)
    let qi = (mathReq s "steps(solve(x^2-2=0, x), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("1.1 Квадратное уравнение: x^2 - 2 = 0 ⇒ x = 2^(1/2) или x = -2^(1/2)", qi)
    Assert.Contains("дискриминант D = b² − 4ac = 0² − 4·1·(-2) = 8 > 0", qi)
    let f = (mathReq s "steps(solve(x^3-x=0, x), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("1.1 Разложение на множители: x^3 - x = 0 ⇒ x*(x - 1)(x + 1) = 0", f)
    Assert.Contains("1.1.2 Линейное уравнение: x - 1 = 0 ⇒ x = 1", f)
    // уравнение берётся как записано (не упрощённым: 3 + x)
    let w = (mathReq s "steps(solve(x + 3 = 5, x), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("1. Решение уравнения относительно x: x + 3 = 5 ⇒ {2}", w)
    Assert.Contains("1.1 Перенос слагаемых в левую часть: x + 3 = 5 ⇒ x - 2 = 0", w)
    let t = (mathReq s "steps(solve(sin(x)=1/2, x), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("Замена переменной", t)
    Assert.Contains("1.2.2 Обращение функции: sin(x) = 1/2 ⇒ x = 1/6*pi + 2k1*pi или x = 5/6*pi + 2k1*pi", t)
    // brief — один шаг; ответ тот же, что без steps
    let brief = (mathReq s "steps(solve(x^2-5*x+6=0, x))" "none").GetProperty("output").GetString()
    Assert.DoesNotContain("1.1", brief)
    Assert.Equal("{2, 3}", (mathReq s "solve(x^2-5*x+6=0, x)" "none").GetProperty("pretty").GetString())
    // система (вектор переменных) вычисляется как обычно
    let sy = (mathReq s "steps(solve([x+y=3, x-y=1], [x, y]), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("1. Линейная система: метод Гаусса–Жордана: [x + y = 3, x - y = 1] ⇒ [x = 2, y = 1]", sy)

[<Fact>]
let ``limit: деревья правил — подстановка, ряд, степень, Лопиталь, бесконечность, сумма, модуль`` () =
    let s = AgentApi.makeSession ()
    Assert.Equal("(limit limit-substitution)", allRulesOf s "(limit '(^ x 2) 'x 3)")
    Assert.Equal("(limit limit-series)", allRulesOf s "(limit '(/ (sin x) x) 'x 0)")
    // (1 + 1/x)^x при x → ∞: замена x = 1/t, ряд (ведущий член e)
    Assert.Equal("(limit limit-infinity limit-series)", allRulesOf s "(limit '(^ (+ 1 (/ 1 x)) x) 'x 'inf)")
    // Лопиталь: exp(x)/x² → ∞ (два применения)
    let lh = allRulesOf s "(limit '(/ (exp x) (^ x 2)) 'x 'inf)"
    Assert.StartsWith("(limit limit-lhopital limit-derivatives limit-lhopital limit-derivatives", lh)
    // разность растущих слагаемых и модуль
    Assert.StartsWith("(limit limit-factor-leading", allRulesOf s "(limit '(- (exp x) x) 'x 'inf)")
    Assert.Equal("(limit limit-abs)", allRulesOf s "(limit '(/ (abs x) x) 'x 0 'plus)")
    // предел не найден — шагов нет (до шага 21j.3 здесь был x·eˣ/(eˣ + 1) при x → −∞: теперь его берёт Грунц)
    Assert.Equal("nil", allRulesOf s "(limit '(* x (sin x)) 'x 'inf)")
    // Грунц — последний приём каскада: x − ln(1 + eˣ) старый каскад не берёт; шаги — крупные
    Assert.Equal("(limit limit-gruntz limit-gruntz-mrv limit-gruntz-lead)", allRulesOf s "(limit '(- x (log (+ 1 (exp x)))) 'x 'inf)")
    Assert.Equal("(limit limit-gruntz limit-gruntz-substitution limit-gruntz-mrv limit-gruntz-lead)",
                 allRulesOf s "(limit '(/ (exp (/ -1 x)) x) 'x 0 'plus)")

[<Fact>]
let ``limit: порядок каскада (21j.3') — башня exp-log идёт в Грунц первой, простое — прежним приёмом`` () =
    let s = AgentApi.makeSession ()
    // 8.1 (глубина 2) и 8.7 (глубина 3): первый (и единственный) приём — Грунц, без combine/рядов/Лопиталя
    let e81 = "(limit '(* (exp x) (- (exp (- (/ 1 x) (exp (- x)))) (exp (/ 1 x)))) 'x 'inf)"
    Assert.Equal("(limit limit-gruntz limit-gruntz-mrv limit-gruntz-lead)", allRulesOf s e81)
    let e87 = "(limit '(/ (exp (exp (exp x))) (exp (exp (exp (- x (exp (- (exp (exp x))))))))) 'x 'inf)"
    Assert.Equal("(limit limit-gruntz limit-gruntz-mrv limit-gruntz-lead)", allRulesOf s e87)
    // простое: eˣ/x² — Лопиталь, x ln x — прежний каскад, Грунц не вмешивается
    Assert.StartsWith("(limit limit-lhopital", allRulesOf s "(limit '(/ (exp x) (^ x 2)) 'x 'inf)")
    Assert.DoesNotContain("gruntz", allRulesOf s "(limit '(* x (log x)) 'x 0 'plus)")
    // не exp-log, но старый каскад отказывает — последняя попытка Грунца отвечает: √(x + √x) − √x → 1/2
    Assert.Equal("(limit limit-gruntz limit-gruntz-mrv limit-gruntz-lead)",
                 allRulesOf s "(limit '(- (sqrt (+ x (sqrt x))) (sqrt x)) 'x 'inf)")

[<Fact>]
let ``limit: шаги Грунца в языке — замена, MRV, ведущий член, английский`` () =
    let s = AgentApi.makeSession ()
    let g1 = (mathReq s "steps(limit(x - log(1 + exp(x)), x, inf), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("1.1 Сравнение скоростей роста (алгоритм Грунца)", g1)
    Assert.Contains("1.1.1 Самые быстрые подвыражения (MRV)", g1)
    Assert.Contains("множество MRV: {exp(t)}", g1)
    Assert.Contains("1.1.2 Ведущий член ω^e", g1)
    // x → 0+: замена x = 1/t
    let g2 = (mathReq s "steps(limit(exp(-1/x)/x, x, 0, plus), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("1.1.1 Замена x = 1/t", g2)
    Assert.Contains("⇒ limit(t*exp(-t), t, ∞, plus)", g2)
    // x → −∞: замена x = −t; английский
    let g3 = (mathReq s "steps(limit(x*exp(x)/(exp(x) + 1), x, -inf), \"full\", \"en\")" "none").GetProperty("output").GetString()
    Assert.Contains("1.1 Comparing growth rates (Gruntz's algorithm)", g3)
    Assert.Contains("1.1.1 Substitution x = -t", g3)
    Assert.Contains("the MRV set: ", g3)
    Assert.DoesNotMatch("[а-яА-Я]", g3)

[<Fact>]
let ``limit и series: язык — sin(x)/x, степень, подстановка, series(exp(sin(x))), аргумент как записан`` () =
    let s = AgentApi.makeSession ()
    let l1 = (mathReq s "steps(limit(sin(x)/x, x, 0), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("1. Предел при x → 0: limit(sin(x)/x, x, 0) ⇒ 1", l1)
    Assert.Contains("1.1 Разложение в ряд: ведущий член:", l1)
    Assert.Contains("ведущий член ряда 1 (степень 0): степень равна нулю, поэтому предел равен коэффициенту; ряд: 1 - 1/6*x^2", l1)
    // как записано: (x^2-1)/(x-1), а не упрощённая арифметикой языка форма
    let l2 = (mathReq s "steps(limit((x^2-1)/(x-1), x, 1), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("1. Предел при x → 1: limit((x^2 - 1)/(x - 1), x, 1) ⇒ 2", l2)
    let l3 = (mathReq s "steps(limit((1+1/x)^x, x, inf), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("1. Предел при x → +∞: limit((1 + 1/x)^x, x, ∞) ⇒ exp(1)", l3)
    Assert.Contains("1.1 Замена x = 1/t, t → 0+", l3)
    Assert.Contains("1.1.1 Разложение в ряд: ведущий член: limit((1 + t)^(1/t), t, 0, plus) ⇒ exp(1)", l3)
    let l4 = (mathReq s "steps(limit(x^2, x, 3), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("1.1 Прямая подстановка: limit(x^2, x, 3) ⇒ 9", l4)
    let l5 = (mathReq s "steps(limit(exp(x)/x^2, x, inf), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("1.1 Правило Лопиталя:", l5)
    Assert.Contains("неопределённость ∞/∞: числитель exp(x) → +∞, знаменатель x^2 → +∞", l5)
    Assert.Contains("1.1.1 Производные числителя и знаменателя: limit(exp(x)/x^2, x, ∞) ⇒ limit(exp(x)/(2x), x, ∞)", l5)
    Assert.Equal("1", (mathReq s "limit(sin(x)/x, x, 0)" "none").GetProperty("pretty").GetString())
    // series: композиция exp(sin x), операции над рядами
    let r1 = (mathReq s "steps(series(exp(sin(x)), x, 0, 5), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("1. Разложение в ряд Тейлора (Лорана) в точке 0 до порядка 5: series(exp(sin(x)), x, 0, 5) ⇒ 1 + x + 1/2*x^2 - 1/8*x^4 + O(x^5)", r1)
    Assert.Contains("1.1 Подстановка ряда аргумента: exp(sin(x)) ⇒ 1 + x + 1/2*x^2 - 1/8*x^4 + O(x^5)", r1)
    Assert.Contains("1.1.1 Стандартное разложение: sin(x) ⇒ x - 1/6*x^3 + O(x^5)", r1)
    Assert.Contains("1.1.2 Стандартное разложение: exp(u) ⇒ 1 + x + 1/2*x^2 - 1/8*x^4 + O(x^5)", r1)
    Assert.Contains("здесь u = x - 1/6*x^3 + O(x^5)", r1)
    let r2 = (mathReq s "steps(series(tan(x), x, 0, 6), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("Произведение рядов: sin(x)/cos(x)", r2)
    Assert.Contains("Отрицательная степень ряда: 1/cos(x)", r2)
    // brief — один шаг
    let rb = (mathReq s "steps(series(exp(sin(x)), x, 0, 5))" "none").GetProperty("output").GetString()
    Assert.DoesNotContain("1.1", rb)
    Assert.Equal("1 + x + 1/2*x^2 - 1/8*x^4 + O(x^5)", (mathReq s "series(exp(sin(x)), x, 0, 5)" "none").GetProperty("pretty").GetString())

[<Fact>]
let ``series: правила — известное разложение, композиция, арифметика; ряд Лорана; ненулевая точка`` () =
    let s = AgentApi.makeSession ()
    Assert.Equal("(series series-compose series-known series-known)", allRulesOf s "(series '(exp (sin x)) 'x 0 5)")
    Assert.Equal("(series series-arith series-arith series-known series-known)", allRulesOf s "(series '(tan x) 'x 0 6)")
    Assert.Equal("(series series-arith series-known series-known)", allRulesOf s "(series '(* (exp x) (cos (* 2 x))) 'x 0 4)")
    Assert.Equal("(series series-known)", allRulesOf s "(series '(sin x) 'x 0 5)")
    Assert.Equal("(series series-arith)", allRulesOf s "(series '(/ 1 (^ (- 1 x) 2)) 'x 0 4)")
    // ряд Лорана и разложение в ненулевой точке
    let laurent = (mathReq s "steps(series(1/(x*(1-x)), x, 0, 3), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("ряд Лорана: есть члены с отрицательными степенями", laurent)
    let at1 = (mathReq s "steps(series(exp(x), x, 1, 2), \"full\")" "none").GetProperty("output").GetString()
    Assert.Contains("в точке 1 до порядка 2", at1)
    Assert.Contains("exp(1) + exp(1)(x - 1) + O((x - 1)^2)", at1)

[<Fact>]
let ``solve, limit, series: ToolResponse — дерево шагов и порядок полей`` () =
    let s = AgentApi.makeSession ()
    let sv = (call s "{\"op\":\"solve\",\"code\":\"x^2-5*x+6 = 0\",\"var\":\"x\",\"syntax\":\"math\",\"steps\":\"full\"}").GetProperty("steps").[0]
    Assert.Equal("solve-equation", sv.GetProperty("rule").GetString())
    Assert.Equal("Решение уравнения относительно x", sv.GetProperty("title").GetString())
    // инструмент solve с syntax: math получает уравнение, уже упрощённое арифметикой языка (как записано — только в steps(...))
    Assert.Equal("6 - 5x + x^2 = 0", sv.GetProperty("before_pretty").GetString())
    Assert.Equal("{2, 3}", sv.GetProperty("after_pretty").GetString())
    Assert.Equal("solve-factor", sv.GetProperty("children").[0].GetProperty("rule").GetString())
    let lm = (call s "{\"op\":\"limit\",\"code\":\"sin(x)/x\",\"var\":\"x\",\"point\":\"0\",\"syntax\":\"math\",\"steps\":\"full\"}").GetProperty("steps").[0]
    Assert.Equal("limit", lm.GetProperty("rule").GetString())
    Assert.Equal("Предел при x → 0", lm.GetProperty("title").GetString())
    Assert.Equal("limit-series", lm.GetProperty("children").[0].GetProperty("rule").GetString())
    let sr = (call s "{\"op\":\"series\",\"code\":\"exp(sin(x))\",\"var\":\"x\",\"point\":\"0\",\"order\":5,\"syntax\":\"math\",\"steps\":\"full\"}").GetProperty("steps").[0]
    Assert.Equal("series", sr.GetProperty("rule").GetString())
    Assert.Equal("1 + x + 1/2*x^2 - 1/8*x^4 + O(x^5)", sr.GetProperty("after_pretty").GetString())
    let brief = (call s "{\"op\":\"limit\",\"code\":\"sin(x)/x\",\"var\":\"x\",\"point\":\"0\",\"syntax\":\"math\",\"steps\":\"brief\"}").GetProperty("steps").[0]
    Assert.Equal(0, brief.GetProperty("children").GetArrayLength())

[<Fact>]
let ``solve, limit, series: каждый шаг — эквивалентное преобразование (checkSteps без ложных)`` () =
    let s = AgentApi.makeSession ()
    let codes =
        [ "(solve '(= (+ (* 2 x) 3) 7) 'x)"; "(solve '(= (+ (^ x 2) (* -5 x) 6) 0) 'x)"; "(solve '(= (- (^ x 3) x) 0) 'x)"
          "(solve '(= (sin x) 1/2) 'x)"; "(solve '(= (exp x) 2) 'x)"; "(solve '(= (sqrt x) (- x 2)) 'x)"
          "(solve '(= (/ 1 x) x) 'x)"; "(solve (list '(= (+ x y) 3) '(= (- x y) 1)) '(x y))"
          "(limit '(/ (sin x) x) 'x 0)"; "(limit '(^ (+ 1 (/ 1 x)) x) 'x 'inf)"; "(limit '(/ (exp x) (^ x 2)) 'x 'inf)"
          "(limit '(- (exp x) x) 'x 'inf)"; "(limit '(^ x 2) 'x 3)"
          "(series '(exp (sin x)) 'x 0 5)"; "(series '(tan x) 'x 0 6)"; "(series '(* (exp x) (cos (* 2 x))) 'x 0 4)" ]
    for c in codes do
        let _, steps, _ = AlgoBuiltins.captureSteps None (fun () -> eval (List.head (readAll c)) s)
        let checks = AgentApi.checkSteps s [] steps
        Assert.True(checks.Length >= 1, c)
        Assert.Empty(AgentApi.failedSteps checks)

[<Fact>]
let ``solve, limit, series: нулевая стоимость — журнал выключен, шагов нет, ответы те же`` () =
    let s = AgentApi.makeSession ()
    Assert.False(StepLog.Journal.Enabled)
    StepLog.Journal.Clear()
    let codes =
        [ "(solve '(= (+ (^ x 2) (* -5 x) 6) 0) 'x)"; "(solve '(= (sin x) 1/2) 'x)"; "(solve '(= (sqrt x) (- x 2)) 'x)"
          "(solve (list '(= (+ x y) 3) '(= (- x y) 1)) '(x y))"; "(limit '(/ (sin x) x) 'x 0)"
          "(limit '(/ (exp x) (^ x 2)) 'x 'inf)"; "(limit '(^ (+ 1 (/ 1 x)) x) 'x 'inf)"
          "(series '(exp (sin x)) 'x 0 5)"; "(series '(tan x) 'x 0 6)" ]
    for c in codes do
        let off = run s c
        Assert.Empty(StepLog.Journal.Steps)
        let on = run s (sprintf "(car (capture-step-log (lambda () %s)))" c)
        Assert.Equal(off, on)
    Assert.False(StepLog.Journal.Enabled)
    // внутренние производные Лопиталя и пределы несобственного интеграла шагов diff/limit в чужих рамках не пишут
    let lh = allRulesOf s "(limit '(/ (exp x) (^ x 2)) 'x 'inf)"
    Assert.DoesNotContain("differentiation", lh)
    Assert.DoesNotContain("diff-", lh)
    Assert.Equal("(int-definite integration int-table int-improper)", allRulesOf s "(integrate '(^ x -2) 'x 1 'inf)")

[<Fact>]
let ``шаги: глубина full — 8, подстановка и части внутри интегралов показываются целиком`` () =
    let s = AgentApi.makeSession ()
    let sub = (mathReq s "steps(integrate(2*x*cos(x^2), x), \"full\")" "none").GetProperty("output").GetString()
    Assert.DoesNotContain("скрыто", sub)
    Assert.Contains("Обратная замена", sub)
    let parts = (mathReq s "steps(integrate(x^2*exp(x), x), \"full\")" "none").GetProperty("output").GetString()
    Assert.DoesNotContain("скрыто", parts)
    Assert.Equal(8, StepLog.MaxDepth)
    Assert.Equal(200, StepLog.MaxNodes)
