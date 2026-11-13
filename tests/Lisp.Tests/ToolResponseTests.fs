// Шаг 22.1: единый формат ответа ToolResponse в --json (AgentApi.handleJsonRequest): порядок полей, статусы,
// совместимость прежних полей ok/result/pretty/error/stack/output, timing, assumptions, steps
module ToolResponseTests

open System.Text.Json
open System.Text.Json.Nodes
open Xunit

let private call (session: Types.Env) (json: string) : JsonElement =
    JsonDocument.Parse(AgentApi.handleJsonRequest session json).RootElement

let private math (session: Types.Env) (code: string) : JsonElement =
    call session (JsonSerializer.Serialize({| op = "math"; code = code |}))

let private str (r: JsonElement) (name: string) : string = r.GetProperty(name).GetString()
let private isNull (r: JsonElement) (name: string) : bool = r.GetProperty(name).ValueKind = JsonValueKind.Null
let private strs (r: JsonElement) (name: string) : string list =
    r.GetProperty(name).EnumerateArray() |> Seq.map (fun e -> e.GetString()) |> List.ofSeq

// conditions — массив объектов {condition, sexpr, reason}; записи языка
let private conds (r: JsonElement) : string list =
    r.GetProperty("conditions").EnumerateArray() |> Seq.map (fun e -> e.GetProperty("condition").GetString()) |> List.ofSeq

let private fieldOrder =
    [ "status"; "result"; "pretty"; "latex"; "note"; "conditions"; "assumptions"; "certificate"; "steps"; "warnings"; "output"
      "timing"; "ok"; "error"; "stack" ]

[<Fact>]
let ``ToolResponse: стабильный порядок полей в ответе и при ошибке`` () =
    let s = AgentApi.makeSession ()
    for r in [ math s "x^2 + 1"; math s "1/0"; call s "{\"op\":\"zzz\",\"code\":\"1\"}"; call s "{\"op\":\"eval\",\"code\":\"(+ 1 2)\"}" ] do
        Assert.Equal<string list>(fieldOrder, r.EnumerateObject() |> Seq.map (fun p -> p.Name) |> List.ofSeq)

[<Fact>]
let ``ToolResponse: answer — новые поля и прежние ok/result/pretty/output`` () =
    let r = math (AgentApi.makeSession ()) "integrate(x^2, x)"
    Assert.Equal("answer", str r "status")
    Assert.True(r.GetProperty("ok").GetBoolean())
    Assert.Equal("(* 1/3 (^ x 3))", str r "result")
    Assert.Equal("1/3*x^3", str r "pretty")
    Assert.Equal("", str r "output")
    for f in [ "note"; "conditions"; "assumptions"; "certificate"; "steps"; "warnings"; "error"; "stack" ] do
        Assert.True(isNull r f, f)
    let t = r.GetProperty("timing")
    Assert.True(t.GetProperty("ms").GetInt64() >= 0L)
    Assert.False(t.GetProperty("timeout").GetBoolean())

[<Fact>]
let ``ToolResponse: unknown — невычисленная форма integrate, limit, sum`` () =
    let s = AgentApi.makeSession ()
    // 21k.5: exp(x^2), 21k″: sin(x)/x доказанно неэлементарны (status nonelementary) — для unknown берётся |x| (модуль вне рамок)
    let r = math s "integrate(abs(x), x)"
    Assert.Equal("unknown", str r "status")
    Assert.True(r.GetProperty("ok").GetBoolean())
    Assert.Equal("(integrate (abs x) x)", str r "result")
    Assert.Contains("невычисленная форма", str r "note")
    Assert.Equal("unknown", str (math s "limit(sin(1/x), x, 0)") "status")
    Assert.Equal("unknown", str (math s "sum(1/k^3, k, 1, inf)") "status")
    // op integrate (Lisp-запрос) — то же правило
    Assert.Equal("unknown", str (call s "{\"op\":\"integrate\",\"code\":\"(abs x)\",\"var\":\"x\"}") "status")
    // невычисленная форма внутри ответа — answer с предупреждением
    let p = math s "x + integrate(exp(t^2), t)"
    Assert.Equal("answer", str p "status")
    Assert.Equal<string list>([ "результат содержит невычисленную форму integrate(...)" ], strs p "warnings")
    // неизвестная функция пользователя — не «не знаю», а ответ
    Assert.Equal("answer", str (math s "g(b)") "status")

[<Fact>]
let ``ToolResponse: no-solution — пустое множество solve; пустое множество не из solve — answer`` () =
    let s = AgentApi.makeSession ()
    let r = math s "solve([x + y = 1, x + y = 2], [x, y])"
    Assert.Equal("no-solution", str r "status")
    Assert.True(r.GetProperty("ok").GetBoolean())
    Assert.Equal("{}", str r "pretty")
    Assert.Contains("решений нет", str r "note")
    // декларации лежат в plist символов — общие для процесса (тесты идут параллельно): своё имя и снятие в finally
    try
        Assert.Equal("no-solution", str (math s "m := solve(trz^2 + 1 = 0, trz); trz :∈ ℝ; solve(trz^2 + 1 = 0, trz)") "status")
        Assert.Equal("no-solution", str (call s "{\"op\":\"eval\",\"code\":\"(solve '(= (^ trz 2) -4) 'trz)\"}") "status")
    finally
        math s "trz :∈" |> ignore
    Assert.Equal("answer", str (math s "{1} ∩ {2}") "status")
    // Lisp-исключение с данными (no-solution "причина") — тот же статус, причина в note
    let e = call s "{\"op\":\"eval\",\"code\":\"(raise (list 'no-solution \\\"нет корней\\\"))\"}"
    Assert.Equal("no-solution", str e "status")
    Assert.Equal("нет корней", str e "note")
    Assert.False(e.GetProperty("ok").GetBoolean())

[<Fact>]
let ``ToolResponse: error — исключение и ошибка протокола; «не умею» — unknown`` () =
    let s = AgentApi.makeSession ()
    let r = math s "1/0"
    Assert.Equal("error", str r "status")
    Assert.False(r.GetProperty("ok").GetBoolean())
    Assert.Equal("Деление на ноль", str r "error")
    Assert.Equal(0, r.GetProperty("stack").GetArrayLength())
    Assert.True(isNull r "result")
    let p = call s "{\"op\":\"zzz\",\"code\":\"1\"}"
    Assert.Equal("error", str p "status")
    Assert.Equal("Неизвестная операция: zzz", str p "error")
    Assert.Equal("error", str (call s "{\"op\":\"math\",\"code\":\"1\",\"steps\":\"много\"}") "status")
    let u = math s "solve(sin(x)^3 + x = 2, x)"
    Assert.Equal("unknown", str u "status")
    Assert.False(u.GetProperty("ok").GetBoolean())
    Assert.StartsWith("solve: не умею решать", str u "error")
    Assert.Equal(str u "error", str u "note")

[<Fact>]
let ``ToolResponse: assumptions — действующие декларации сессии`` () =
    let s = AgentApi.makeSession ()
    Assert.True(isNull (math s "1") "assumptions")
    try
        math s "tra :∈ ℝ; trb :∈ (0, 1)" |> ignore
        Assert.Equal<string list>([ "tra ∈ ℝ"; "trb ∈ (0, 1)" ], strs (math s "tra + trb") "assumptions")
        Assert.Equal<string list>([ "tra ∈ ℝ"; "trb ∈ (0, 1)" ], strs (call s "{\"op\":\"eval\",\"code\":\"1\"}") "assumptions")
        math s "trb :∈" |> ignore
        Assert.Equal<string list>([ "tra ∈ ℝ" ], strs (math s "1") "assumptions")
    finally
        math s "tra :∈; trb :∈" |> ignore

[<Fact>]
let ``ToolResponse: steps по запросу — записи журнала; conditions из solve с параметрами`` () =
    let s = AgentApi.makeSession ()
    let req (code: string) (steps: string) = call s (JsonSerializer.Serialize({| op = "math"; code = code; steps = steps |}))
    // шаг S.1: brief — только рамка верхнего уровня, full — дерево
    let r = req "solve([a*x^2 = 1, y - x = b], [x, y])" "brief"
    let rules (steps: JsonElement) = steps.EnumerateArray() |> Seq.map (fun e -> e.GetProperty("rule").GetString()) |> List.ofSeq
    Assert.Equal<string list>([ "polynomial-system" ], rules (r.GetProperty("steps")))
    let f = req "solve([a*x^2 = 1, y - x = b], [x, y])" "full"
    Assert.Equal<string list>([ "parametric-basis"; "generic-parameters" ], rules (f.GetProperty("steps").[0].GetProperty("children")))
    let step0 = r.GetProperty("steps").[0]
    Assert.Equal<string list>([ "rule"; "title"; "comment"; "before"; "before_pretty"; "before_latex"; "after"; "after_pretty"; "after_latex"; "level"; "children" ],
                              step0.EnumerateObject() |> Seq.map (fun p -> p.Name) |> List.ofSeq)
    Assert.Equal<string list>([ "a ≠ 0" ], conds r)
    // шаги запрошены, но не записаны — пустой массив; не запрошены — null
    Assert.Equal(0, (req "x + 1" "full").GetProperty("steps").GetArrayLength())
    Assert.True(isNull (math s "solve([a*x^2 = 1, y - x = b], [x, y])") "steps")
    Assert.True(isNull (req "x + 1" "none") "steps")

[<Fact>]
let ``ToolResponse: conditions из канала — без включения шагов, формат, очистка между запросами`` () =
    let s = AgentApi.makeSession ()
    // шаги не запрошены и журнал выключен — условия всё равно есть
    let r = math s "solve([a*x^2 = 1, y - x = b], [x, y])"
    Assert.True(isNull r "steps")
    Assert.Equal<string list>([ "a ≠ 0" ], conds r)
    let c0 = r.GetProperty("conditions").[0]
    Assert.Equal<string list>([ "condition"; "sexpr"; "reason" ], c0.EnumerateObject() |> Seq.map (fun p -> p.Name) |> List.ofSeq)
    Assert.Equal("(/= a 0)", str c0 "sexpr")
    Assert.Contains("общих значений параметров", str c0 "reason")
    // без параметров — null; канал очищен в начале запроса
    Assert.True(isNull (math s "solve([x + y = 3, x - y = 1], [x, y])") "conditions")
    Assert.True(isNull (math s "1 + 1") "conditions")
    // одно уравнение с параметром: деление на коэффициент
    Assert.Equal<string list>([ "a ≠ 0" ], conds (math s "solve(a*x = 1, x)"))
    // дубликаты не накапливаются (оба решения квадрата дают одно условие)
    Assert.Equal<string list>([ "a ≠ 0" ], conds (math s "solve(a*x^2 = 1, x)"))
    // интегратор: параметр считается положительным (1/(x^2+c) теперь даёт piecewise по знаку c — другой пример)
    Assert.Equal<string list>([ "c > 0" ], conds (math s "integrate(1/sqrt(c - x^2), x)"))
    // eval: record-condition из Lisp-кода; следующий запрос начинается с пустого канала
    let e = call s "{\"op\":\"eval\",\"code\":\"(record-condition '(/= q 0) \\\"проверка\\\") (record-condition '(/= q 0) \\\"ещё\\\")\"}"
    Assert.Equal<string list>([ "q ≠ 0" ], conds e)
    Assert.Equal("проверка", str (e.GetProperty("conditions").[0]) "reason")
    Assert.True(isNull (call s "{\"op\":\"eval\",\"code\":\"(+ 1 2)\"}") "conditions")
    // capture-conditions в eval не протекает наружу
    let cap = call s "{\"op\":\"eval\",\"code\":\"(capture-conditions (lambda () (record-condition '(/= z 0) \\\"п\\\")))\"}"
    Assert.True(isNull cap "conditions")

[<Fact>]
let ``ToolResponse: JSON без \u-экранирования кириллицы и математических символов`` () =
    let s = AgentApi.makeSession ()
    try
        let raw = AgentApi.handleJsonRequest s (JsonSerializer.Serialize({| op = "math"; code = "trc :∈ ℝ; solve(trc^2 + 1 = 0, trc)" |}))
        Assert.Contains("\"assumptions\":[\"trc ∈ ℝ\"]", raw)
        Assert.Contains("\"note\":\"solve: решений нет (пустое множество)\"", raw)
    finally
        math s "trc :∈" |> ignore

// --- Шаг WASM.JSON: браузер (Lisp.Wasm) вызывает тот же AgentApi.handleJsonRequest с {"op":"math"} ---

[<Fact>]
let ``WASM.JSON: интеграл с отказом — status unknown, note`` () =
    let r = math (AgentApi.makeSession ()) "integrate(((a+b*(log(c*((d+e1*(x^(1/2)))^n))))^2)/(x^3), x)"
    Assert.Equal("unknown", str r "status")
    Assert.False(isNull r "note")

[<Fact>]
let ``WASM.JSON: explain даёт output с журналом попыток`` () =
    let r = math (AgentApi.makeSession ()) "explain(integrate(sin(sin(x)), x))"
    Assert.False(System.String.IsNullOrEmpty(str r "output"))
    Assert.Contains("Интегрирование по x — отказ", str r "output")

// Ответ общей функции совпадает с ответом настоящего `Lisp --json` (отдельный процесс); timing.ms не сравниваем
[<Fact>]
let ``WASM.JSON: ответ совпадает с Lisp --json на 5 примерах`` () =
    let reqs =
        [ "integrate(x^2, x)"                                              // answer
          // unknown: быстрый отказ; тяжёлый пример упирался в бюджеты стратегий (INT.FIX3) — ответ зависел от скорости машины
          "integrate(sin(sin(x)), x)"
          "integrate(exp(x^2), x)"                                         // nonelementary
          "1 +"                                                            // error
          "trc :∈ ℝ; solve(trc^2 + 1 = 0, trc)" ]                                      // solve без решений
        |> List.map (fun c -> JsonSerializer.Serialize({| op = "math"; code = c |}))
    let strip (json: string) =
        let n = JsonNode.Parse json
        n.["timing"].["ms"] <- JsonValue.Create 0
        n.ToJsonString()
    let session = AgentApi.makeSession ()
    let inProc = reqs |> List.map (fun q -> strip (AgentApi.handleJsonRequest session q))
    let psi = System.Diagnostics.ProcessStartInfo("dotnet", "\"" + System.IO.Path.Combine(System.AppContext.BaseDirectory, "Lisp.dll") + "\" --json")
    psi.RedirectStandardInput <- true
    psi.RedirectStandardOutput <- true
    psi.StandardOutputEncoding <- System.Text.Encoding.UTF8
    psi.UseShellExecute <- false
    use p = System.Diagnostics.Process.Start psi
    for q in reqs do p.StandardInput.WriteLine q
    p.StandardInput.WriteLine "exit"
    p.StandardInput.Close()
    let lines = [ for _ in reqs -> p.StandardOutput.ReadLine() ]
    p.WaitForExit()
    let statuses = inProc |> List.map (fun j -> JsonDocument.Parse(j).RootElement.GetProperty("status").GetString())
    Assert.Equal<string list>([ "answer"; "unknown"; "nonelementary"; "error"; "no-solution" ], statuses)
    Assert.Equal<string list>(inProc, lines |> List.map strip)
