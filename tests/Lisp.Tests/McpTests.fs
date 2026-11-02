// Шаг 22.3: MCP-сервер (режим --mcp, McpServer.fs): таблица инструментов и схемы, перевод аргументов в запрос AgentApi,
// syntax math у операций --json; интеграционный тест — процесс «Lisp --mcp»: initialize → tools/list → tools/call,
// ответы JSON-RPC и поля ToolResponse, stdout содержит только сообщения протокола
module McpTests

open System
open System.Collections.Generic
open System.Diagnostics
open System.IO
open System.Text
open System.Text.Json
open Xunit

let private el (s: string) : JsonElement = JsonSerializer.SerializeToElement s

let private args (kvs: (string * JsonElement) list) : IDictionary<string, JsonElement> =
    let d = Dictionary<string, JsonElement>()
    for k, v in kvs do d[k] <- v
    d :> IDictionary<_, _>

let private parse (json: string) : JsonElement = JsonDocument.Parse(json).RootElement
let private str (r: JsonElement) (name: string) : string = r.GetProperty(name).GetString()
let private has (r: JsonElement) (name: string) : bool = fst (r.TryGetProperty name)

// --- В памяти ---

[<Fact>]
let ``MCP: таблица инструментов и схемы входа`` () =
    let names = McpHost.tools |> List.map (fun t -> t.Name)
    Assert.Equal<string list>(
        [ "math"; "evaluate"; "simplify"; "diff"; "integrate"; "sum"; "linear-algebra"; "linear-programming"; "solve"; "expand"; "factor"; "together"; "apart"; "limit"; "series"
          "groebner"; "declare"; "undeclare"; "declarations"; "equivalent"; "guide"; "code"; "reset" ], names)
    for t in McpHost.tools do
        Assert.False(String.IsNullOrWhiteSpace t.Description, t.Name)
    let schemaOf name = McpHost.inputSchema (McpHost.tools |> List.find (fun t -> t.Name = name))
    let required (s: JsonElement) = s.GetProperty("required").EnumerateArray() |> Seq.map (fun e -> e.GetString()) |> List.ofSeq
    Assert.Equal<string list>([ "equations"; "vars" ], required (schemaOf "solve"))
    Assert.Equal<string list>([ "expr"; "var" ], required (schemaOf "integrate"))
    let steps = (schemaOf "diff").GetProperty("properties").GetProperty("steps")
    Assert.Equal("none brief full trace", steps.GetProperty("enum").EnumerateArray() |> Seq.map (fun e -> e.GetString()) |> String.concat " ")
    Assert.Equal("integer", (schemaOf "diff").GetProperty("properties").GetProperty("order").GetProperty("type").GetString())
    Assert.False((schemaOf "reset").GetProperty("additionalProperties").GetBoolean())

[<Fact>]
let ``MCP: аргументы инструмента → запрос AgentApi (syntax по умолчанию math, массивы → вектор)`` () =
    let tool n = McpHost.tools |> List.find (fun t -> t.Name = n)
    let r = parse (McpHost.buildRequest (tool "solve") (args [ "equations", JsonSerializer.SerializeToElement [| "x + y = 3"; "x - y = 1" |]
                                                               "vars", JsonSerializer.SerializeToElement [| "x"; "y" |] ]))
    Assert.Equal("solve", str r "op")
    Assert.Equal("[x + y = 3, x - y = 1]", str r "code")
    Assert.Equal("[x, y]", str r "var")
    Assert.Equal("math", str r "syntax")
    let l = parse (McpHost.buildRequest (tool "solve") (args [ "equations", el "(= x 1)"; "vars", JsonSerializer.SerializeToElement [| "x" |]
                                                               "syntax", el "lisp" ]))
    Assert.Equal("(x)", str l "var")
    let d = parse (McpHost.buildRequest (tool "diff") (args [ "expr", el "x^3"; "var", el "x"; "order", JsonSerializer.SerializeToElement 2 ]))
    Assert.Equal(2, d.GetProperty("order").GetInt32())
    let e = parse (McpHost.buildRequest (tool "evaluate") (args [ "code", el "(+ 1 2)" ]))
    Assert.Equal("eval", str e "op")
    Assert.False(has e "syntax")

[<Fact>]
let ``MCP: вызов инструментов в памяти — сессия, ошибки аргументов, reset`` () =
    let s = McpHost.Server()
    let call name kvs = s.Call(name, args kvs)
    let r = call "math" [ "code", el "g(x) := x^2 + 1" ]
    Assert.Equal(ToolResponse.Answer, r.Status)
    // функция языка видна следующему вызову другого инструмента
    let d = call "diff" [ "expr", el "g(x)"; "var", el "x" ]
    Assert.Equal(Some "2x", d.Pretty)
    let bad = call "simplify" [ "expr", el "x"; "bogus", el "1" ]
    Assert.Equal(ToolResponse.Error, bad.Status)
    Assert.Contains("bogus", bad.Error.Value)
    let missing = call "integrate" [ "expr", el "x" ]
    Assert.Equal(ToolResponse.Error, missing.Status)
    let half = call "integrate" [ "expr", el "x"; "var", el "x"; "from", el "0" ]
    Assert.Equal(ToolResponse.Error, half.Status)
    Assert.Equal(ToolResponse.Answer, (call "reset" []).Status)
    Assert.Equal(Some "g(x)", (call "simplify" [ "expr", el "g(x)" ]).Pretty)
    Assert.Throws<ModelContextProtocol.McpProtocolException>(fun () -> call "nope" [] |> ignore) |> ignore

[<Fact>]
let ``--json: syntax math у операций simplify/diff/integrate/solve/limit/series`` () =
    let s = AgentApi.makeSession ()
    let call (json: string) = parse (AgentApi.handleJsonRequest s json)
    let r = call """{"op":"integrate","code":"x*exp(x)","var":"x","syntax":"math"}"""
    Assert.Equal("answer", str r "status")
    Assert.Equal("", str r "output")
    let def = call """{"op":"integrate","code":"x^2","var":"x","from":"0","to":"3","syntax":"math"}"""
    Assert.Equal("9", str def "pretty")
    let defLisp = call """{"op":"integrate","code":"(^ x 2)","var":"x","from":"0","to":"3"}"""
    Assert.Equal("9", str defLisp "result")
    Assert.Equal("6", str (call """{"op":"diff","code":"x^3","var":"x","order":3,"syntax":"math"}""") "pretty")
    Assert.Equal("6", str (call """{"op":"diff","code":"(^ x 3)","var":"x","order":3}""") "result")
    let sol = call """{"op":"solve","code":"x^2 - 5x + 6 = 0","var":"x","syntax":"math"}"""
    Assert.Equal("answer", str sol "status")
    Assert.Equal("{2, 3}", str sol "pretty")
    let solLisp = call """{"op":"solve","code":"(= (* x x) 4)","var":"x"}"""
    Assert.Equal("answer", str solLisp "status")
    Assert.Equal("no-solution", str (call """{"op":"solve","code":"[x + y = 1, x + y = 2]","var":"[x, y]","syntax":"math"}""") "status")
    Assert.Equal("1", str (call """{"op":"limit","code":"sin(x)/x","var":"x","point":"0","syntax":"math"}""") "pretty")
    Assert.Equal("answer", str (call """{"op":"series","code":"exp(x)","var":"x","order":3,"syntax":"math"}""") "status")
    let bad = call """{"op":"simplify","code":"x +","syntax":"math"}"""
    Assert.Equal("error", str bad "status")
    Assert.Equal("error", str (call """{"op":"simplify","code":"x","syntax":"tex"}""") "status")

// --- Подшаг 22.5: остальные инструменты, equivalent, guide ---

let private num (n: int) : JsonElement = JsonSerializer.SerializeToElement n

[<Fact>]
let ``22.5: expand, factor, together, apart`` () =
    let s = McpHost.Server()
    let call name kvs = s.Call(name, args kvs)
    let r = call "expand" [ "expr", el "(x+1)^3" ]
    Assert.Equal(ToolResponse.Answer, r.Status)
    Assert.Equal(Some "1 + 3x + 3x^2 + x^3", r.Pretty)
    Assert.Equal(Some "(-1 + x)(1 + x)", (call "factor" [ "expr", el "x^2 - 1" ]).Pretty)
    Assert.Equal(Some "(x + y)/(x*y)", (call "together" [ "expr", el "1/x + 1/y" ]).Pretty)
    let a = call "apart" [ "expr", el "1/(x^2-1)"; "var", el "x" ]
    Assert.Equal(ToolResponse.Answer, a.Status)
    Assert.Equal(Some "1/(2(-1 + x)) - 1/(2(1 + x))", a.Pretty)
    Assert.Equal(ToolResponse.Error, (call "apart" [ "expr", el "1/(x^2-1)" ]).Status)
    // syntax lisp
    Assert.Equal(Some "(* (^ x -1) (^ y -1) (+ x y))", (call "together" [ "expr", el "(+ (/ 1 x) (/ 1 y))"; "syntax", el "lisp" ]).Result)

[<Fact>]
let ``22.5: limit и series — ответ, односторонний, unknown`` () =
    let s = McpHost.Server()
    let call name kvs = s.Call(name, args kvs)
    Assert.Equal(Some "1", (call "limit" [ "expr", el "sin(x)/x"; "var", el "x"; "point", el "0" ]).Pretty)
    Assert.Equal(Some "∞", (call "limit" [ "expr", el "1/x"; "var", el "x"; "point", el "0"; "side", el "plus" ]).Pretty)
    Assert.Equal(Some "-∞", (call "limit" [ "expr", el "1/x"; "var", el "x"; "point", el "0"; "side", el "minus" ]).Pretty)
    Assert.Equal(Some "1", (call "limit" [ "expr", el "x^(1/x)"; "var", el "x"; "point", el "∞" ]).Pretty)
    let unk = call "limit" [ "expr", el "sin(1/x)"; "var", el "x"; "point", el "0" ]
    Assert.Equal(ToolResponse.Unknown, unk.Status)
    Assert.Equal(Some "limit(sin(1/x), x, 0)", unk.Pretty)
    Assert.False(String.IsNullOrEmpty unk.Note.Value)
    Assert.Equal(ToolResponse.Error, (call "limit" [ "expr", el "x"; "var", el "x" ]).Status)
    let ser = call "series" [ "expr", el "sin(x)"; "var", el "x"; "point", el "0"; "order", num 5 ]
    Assert.Equal(ToolResponse.Answer, ser.Status)
    Assert.Equal(Some "x - 1/6*x^3 + O(x^5)", ser.Pretty)
    Assert.Equal(Some "x^-1 + O(x^3)", (call "series" [ "expr", el "1/x"; "var", el "x"; "order", num 3 ]).Pretty)

[<Fact>]
let ``22.5: groebner — базис, порядки, массивы строк`` () =
    let s = McpHost.Server()
    let call name kvs = s.Call(name, args kvs)
    let r = call "groebner" [ "polys", el "[x^2 + y, x*y - 1]"; "vars", el "[x, y]"; "order", el "grevlex" ]
    Assert.Equal(ToolResponse.Answer, r.Status)
    Assert.Equal(Some "[x^2 + y, -1 + x*y, x + y^2]", r.Pretty)
    let lex = call "groebner" [ "polys", JsonSerializer.SerializeToElement [| "x^2 + y"; "x*y - 1" |]; "vars", JsonSerializer.SerializeToElement [| "x"; "y" |] ]
    Assert.Equal(Some "[x + y^2, 1 + y^3]", lex.Pretty)
    Assert.Equal(ToolResponse.Error, (call "groebner" [ "polys", el "[x]"; "vars", el "[x]"; "order", el "bogus" ]).Status)

[<Fact>]
let ``22.5: declare влияет на simplify; undeclare и declarations`` () =
    let s = McpHost.Server()
    let call name kvs = s.Call(name, args kvs)
    Assert.Equal(Some "sqrt(dq^2)", (call "simplify" [ "expr", el "sqrt(dq^2)" ]).Pretty)
    let d = call "declare" [ "symbol", el "dq"; "domain", el "positive" ]
    Assert.Equal(ToolResponse.Answer, d.Status)
    Assert.Equal(Some "dq ∈ (0, ∞)", d.Pretty)
    Assert.Equal<string list>([ "dq ∈ (0, ∞)" ], d.Assumptions)
    Assert.Equal(Some "dq", (call "simplify" [ "expr", el "sqrt(dq^2)" ]).Pretty)
    // ℝ добавляется (пересечение), вещественный символ без других ограничений даёт abs
    call "declare" [ "symbol", el "dr"; "domain", el "ℝ" ] |> ignore
    Assert.Equal(Some "abs(dr)", (call "simplify" [ "expr", el "sqrt(dr^2)" ]).Pretty)
    let l = call "declarations" []
    Assert.Equal(ToolResponse.Answer, l.Status)
    Assert.Equal(Some "dq ∈ (0, ∞)\ndr ∈ ℝ", l.Pretty)
    let u = call "undeclare" [ "symbol", el "dq" ]
    Assert.Equal(ToolResponse.Answer, u.Status)
    Assert.Equal(Some "sqrt(dq^2)", (call "simplify" [ "expr", el "sqrt(dq^2)" ]).Pretty)
    Assert.Equal(Some "dr ∈ ℝ", (call "declarations" []).Pretty)
    // интервал и неверные аргументы
    Assert.Equal<string list>([ "dr ∈ ℝ"; "dt ∈ interval(0, 1)" ], (call "declare" [ "symbol", el "dt"; "domain", el "[0, 1]" ]).Assumptions)
    Assert.Equal(ToolResponse.Error, (call "declare" [ "symbol", el "dr; reset()"; "domain", el "ℝ" ]).Status)
    Assert.Equal(ToolResponse.Error, (call "declare" [ "symbol", el "dr"; "domain", el "ℝ; 1" ]).Status)
    Assert.Equal(ToolResponse.Error, (call "declare" [ "symbol", el "dr"; "domain", el "bogus" ]).Status)
    // reset снимает
    call "reset" [] |> ignore
    Assert.Equal(None, (call "declarations" []).Pretty |> Option.filter (fun p -> p <> "nil"))

[<Fact>]
let ``22.5: equivalent — true, false с контрпримером, unknown`` () =
    let s = McpHost.Server()
    let call kvs = s.Call("equivalent", args kvs)
    // символьно доказано
    let t = call [ "a", el "(x+1)^2"; "b", el "x^2 + 2x + 1" ]
    Assert.Equal(ToolResponse.Answer, t.Status)
    Assert.Equal(Some "true", t.Result)
    Assert.Contains("символьно", t.Note.Value)
    Assert.Equal(Some "true", (call [ "a", el "(x^2-1)/(x-1)"; "b", el "x+1" ]).Result)
    Assert.Equal(Some "true", (call [ "a", el "sin(x)^2 + cos(x)^2"; "b", el "1" ]).Result)
    // разные: контрпример (точка и значения)
    let f = call [ "a", el "x^2"; "b", el "x^2 + 1" ]
    Assert.Equal(ToolResponse.Answer, f.Status)
    Assert.Equal(Some "false", f.Result)
    Assert.Contains("контрпример: x = ", f.Note.Value)
    Assert.Contains("первое выражение", f.Note.Value)
    // без деклараций sqrt(x^2) ≠ x (при x < 0); с декларацией x > 0 — доказано
    Assert.Equal(Some "false", (call [ "a", el "sqrt(ex^2)"; "b", el "ex" ]).Result)
    s.Call("declare", args [ "symbol", el "ex"; "domain", el "positive" ]) |> ignore
    Assert.Equal(Some "true", (call [ "a", el "sqrt(ex^2)"; "b", el "ex" ]).Result)
    // не доказано символьно, но численно совпадает: unknown (не true!) с пометкой
    let u = call [ "a", el "sin(2x)"; "b", el "2*sin(x)*cos(x)" ]
    Assert.Equal(ToolResponse.Answer, u.Status)
    Assert.Equal(Some "unknown", u.Result)
    Assert.Contains("численно совпадают в", u.Note.Value)
    // не вычисляется численно вовсе: unknown
    Assert.Equal(Some "unknown", (call [ "a", el "fq(x)"; "b", el "gq(x)" ]).Result)
    // декларации учитываются: |n| = n на ℕ — доказано; на ℤ — контрпример с отрицательным n
    Assert.Equal(Some "false", (call [ "a", el "abs(nn)"; "b", el "nn" ]).Result)
    s.Call("declare", args [ "symbol", el "nn"; "domain", el "ℕ" ]) |> ignore
    Assert.Equal(Some "true", (call [ "a", el "abs(nn)"; "b", el "nn" ]).Result)
    s.Call("declare", args [ "symbol", el "zz"; "domain", el "ℤ" ]) |> ignore
    let zf = call [ "a", el "abs(zz)"; "b", el "zz" ]
    Assert.Equal(Some "false", zf.Result)
    Assert.Matches(@"zz = -\d+:", zf.Note.Value)
    // lisp-синтаксис и ошибки
    Assert.Equal(Some "true", (call [ "a", el "(* x x)"; "b", el "(^ x 2)"; "syntax", el "lisp" ]).Result)
    Assert.Equal(ToolResponse.Error, (call [ "a", el "x +"; "b", el "x" ]).Status)
    Assert.Equal(ToolResponse.Error, (call [ "a", el "x" ]).Status)

[<Fact>]
let ``22.5: guide возвращает ядро справки (GD.1); полный LLM-GUIDE — ресурс`` () =
    let s = McpHost.Server()
    let r = s.Call("guide", args [])
    Assert.Equal(ToolResponse.Answer, r.Status)
    Assert.Contains("CAS guide for LLMs", r.Result.Value)
    Assert.Contains("status", r.Result.Value)
    Assert.True(r.Result.Value.Length < McpHost.defaultLimits.MaxChars)
    Assert.True(McpHost.guideText.Length < McpHost.defaultLimits.MaxChars)
    // инструменты из таблицы упомянуты в руководстве
    for t in McpHost.tools do
        Assert.Contains("`" + t.Name + "`", McpHost.guideText)

// --- Подшаг 22.4: таймаут, отмена, лимиты, песочница, декларации по сессиям ---

[<Fact; Trait("Category", "Slow")>]
let ``22.4: бесконечный цикл Lisp и языка → timeout за ~таймаут, сессия работает дальше`` () =
    let s = McpHost.Server()
    let call name kvs = s.Call(name, args kvs)
    Assert.Equal(ToolResponse.Answer, (call "evaluate" [ "code", el "(define (spin n) (spin (+ n 1)))" ]).Status)
    let sw = Stopwatch.StartNew()
    let r = call "evaluate" [ "code", el "(spin 0)"; "timeout_s", num 1 ]
    Assert.Equal(ToolResponse.Timeout, r.Status)
    Assert.True(r.TimedOut)
    Assert.Contains("таймаут 1 с", r.Note.Value)
    Assert.True(sw.ElapsedMilliseconds < 4000L, sprintf "прерывание заняло %d мс" sw.ElapsedMilliseconds)
    Assert.False(Cancel.requested)
    Assert.Equal(Some "3", (call "evaluate" [ "code", el "(+ 1 2)" ]).Result)
    // нехвостовой цикл через map (checkStack) и try: обработчик не перехватывает прерывание
    let r2 = call "evaluate" [ "code", el "(try (spin 0) (lambda (e) 'caught))"; "timeout_s", num 1 ]
    Assert.Equal(ToolResponse.Timeout, r2.Status)
    // язык: хвостовая рекурсия функции языка
    Assert.Equal(ToolResponse.Answer, (call "math" [ "code", el "g(n) := g(n + 1)" ]).Status)
    let m = call "math" [ "code", el "print(\"start\"); g(0)"; "timeout_s", num 1 ]
    Assert.Equal(ToolResponse.Timeout, m.Status)
    Assert.Equal(Some "start", m.Output)        // перехват print закрыт и после прерывания
    Assert.Equal(Some "4", (call "math" [ "code", el "2 + 2" ]).Pretty)
    let json = ToolResponse.toJson m
    Assert.Contains("\"status\":\"timeout\"", json)
    Assert.Contains("\"timeout\":true", json)

[<Fact; Trait("Category", "Slow")>]
let ``22.4: прерывание внутри assuming восстанавливает декларации`` () =
    let s = McpHost.Server()
    let call name kvs = s.Call(name, args kvs)
    call "evaluate" [ "code", el "(define (spin n) (spin (+ n 1)))" ] |> ignore
    let r = call "evaluate" [ "code", el "(assuming ((tz reals)) (spin 0))"; "timeout_s", num 1 ]
    Assert.Equal(ToolResponse.Timeout, r.Status)
    Assert.Equal(Some "#t", (call "evaluate" [ "code", el "(null? (declarations 'tz))" ]).Result)
    Assert.Empty((call "evaluate" [ "code", el "1" ]).Assumptions)

[<Fact>]
let ``22.4: отмена клиентом (CancellationToken) прерывает вычисление`` () =
    let s = McpHost.Server()
    s.Call("evaluate", args [ "code", el "(define (spin n) (spin (+ n 1)))" ]) |> ignore
    use cts = new Threading.CancellationTokenSource(300)
    let sw = Stopwatch.StartNew()
    let r = s.Call("evaluate", args [ "code", el "(spin 0)" ], cts.Token, ignore)
    Assert.Equal(ToolResponse.Timeout, r.Status)
    Assert.Contains("отменён клиентом", r.Note.Value)
    Assert.True(sw.ElapsedMilliseconds < 5000L)
    Assert.Equal(Some "3", s.Call("evaluate", args [ "code", el "(+ 1 2)" ]).Result)

[<Fact; Trait("Category", "Slow")>]
let ``22.4: сторож — вычисление без проверок флага → onStuck через GraceS`` () =
    let stuck = ref ""
    let limits = { McpHost.defaultLimits with GraceS = 0.3 }
    let v = McpHost.runGuarded limits 0.2 Threading.CancellationToken.None (fun w -> stuck.Value <- w)
                (fun () -> Threading.Thread.Sleep 1500; 7)
    Assert.Equal(7, v)
    Assert.Contains("таймаут", stuck.Value)
    Assert.False(Cancel.requested)
    // быстрое вычисление — ни флага, ни onStuck
    let quiet = ref true
    Assert.Equal(1, McpHost.runGuarded limits 5.0 Threading.CancellationToken.None (fun _ -> quiet.Value <- false) (fun () -> 1))
    Assert.True(quiet.Value)

[<Fact>]
let ``22.4: огромный вывод и результат обрезаются с пометкой в warnings`` () =
    let s = McpHost.Server()
    let call name kvs = s.Call(name, args kvs)
    let saved = Console.Out
    s.CaptureConsole()
    let r =
        try
            call "evaluate"
                [ "code", el "(define (pr n) (if (> n 0) (begin (display \"abcdefghij\") (pr (- n 1))) 'done)) (pr 5000)" ]
        finally Console.SetOut saved
    Assert.Equal(ToolResponse.Answer, r.Status)
    Assert.True(r.Output.Value.Length <= McpHost.defaultLimits.MaxOutput + 2)
    Assert.Contains(r.Warnings, fun w -> w.StartsWith "output обрезан" && w.Contains "50000")
    let big =
        call "evaluate" [ "code", el "(define (rng n) (if (= n 0) '() (cons n (rng (- n 1))))) (rng 500)"; "max_chars", num 100 ]
    Assert.True((big.Status = ToolResponse.Answer), sprintf "%A" big.Error)
    Assert.True(big.Result.Value.Length <= 102)
    Assert.Contains(big.Warnings, fun w -> w.StartsWith "result обрезан")
    Assert.Contains(big.Warnings, fun w -> w.StartsWith "pretty обрезан")
    let bad = call "evaluate" [ "code", el "1"; "timeout_s", el "abc" ]
    Assert.Equal(ToolResponse.Error, bad.Status)

[<Fact>]
let ``22.4: песочница — load вне lib и --allow-dir запрещён, внутри разрешён; --unsafe снимает`` () =
    let dir = Path.Combine(Path.GetTempPath(), "lisp-sandbox-" + string (Guid.NewGuid()))
    Directory.CreateDirectory dir |> ignore
    let file = Path.Combine(dir, "sbx.lisp")
    File.WriteAllText(file, "(define sbx-v 42)")
    let mth = Path.Combine(dir, "sbx.mth")
    File.WriteAllText(mth, "sbxm := 6 * 7")
    let lispPath (p: string) = p.Replace("\\", "/")
    try
        let s = McpHost.Server()
        let call name kvs = s.Call(name, args kvs)
        Sandbox.configure true []
        let denied = call "evaluate" [ "code", el (sprintf "(load \"%s\")" (lispPath file)) ]
        Assert.Equal(ToolResponse.Error, denied.Status)
        Assert.Contains("запрещено", denied.Error.Value)
        Assert.Contains("--allow-dir", denied.Error.Value)
        let deniedMath = call "evaluate" [ "code", el (sprintf "(load-math \"%s\")" (lispPath mth)) ]
        Assert.Equal(ToolResponse.Error, deniedMath.Status)
        Assert.Contains("read-text-file", deniedMath.Error.Value)
        // библиотека — всегда
        Assert.Equal(ToolResponse.Answer, (call "evaluate" [ "code", el "(load (string-append lib-dir \"logic.lisp\"))" ]).Status)
        Assert.Equal(ToolResponse.Error, (call "evaluate" [ "code", el (sprintf "(load \"%s/../x.lisp\")" (lispPath (Path.Combine(Sandbox.libDir, "")))) ]).Status)
        // --allow-dir
        Sandbox.configure true [ dir ]
        Assert.Equal(Some "sbx-v", (call "evaluate" [ "code", el (sprintf "(load \"%s\")" (lispPath file)) ]).Result)
        Assert.Equal(Some "42", (call "evaluate" [ "code", el "sbx-v" ]).Result)
        let okMath = call "evaluate" [ "code", el (sprintf "(load-math \"%s\")" (lispPath mth)) ]
        Assert.Equal(ToolResponse.Answer, okMath.Status)
        Assert.Equal(Some "42", okMath.Result)
        // --unsafe
        Sandbox.configure false []
        Assert.Equal(ToolResponse.Answer, (call "evaluate" [ "code", el (sprintf "(load \"%s\")" (lispPath file)) ]).Status)
        // разбор параметров --mcp
        match McpHost.parseOptions [ "--allow-dir"; dir; "--allow-dir"; dir; "--unsafe"; "--max-memory-mb"; "512" ] with
        | Result.Ok o ->
            Assert.True o.Unsafe
            Assert.Equal(2, o.AllowDirs.Length)
            Assert.Equal(Some 512, o.MaxMemoryMB)
        | Result.Error e -> failwith e
        Assert.True(Result.isError (McpHost.parseOptions [ "--allow-dir"; Path.Combine(dir, "нет-такого") ]))
        Assert.True(Result.isError (McpHost.parseOptions [ "--bogus" ]))
    finally
        Sandbox.configure false []
        Directory.Delete(dir, true)

[<Fact>]
let ``22.4: декларации доменов — у каждой сессии свои; reset снимает; pi > 0 везде`` () =
    let s1 = AgentApi.makeSession ()
    let s2 = AgentApi.makeSession ()
    let call s (json: string) = parse (AgentApi.handleJsonRequest s json)
    let eval s code = str (call s (sprintf """{"op":"eval","code":"%s"}""" code)) "result"
    let math s code = call s (sprintf """{"op":"math","code":"%s"}""" code)
    // поочерёдно: s1 объявляет dz ∈ ℝ, s2 — dz > 0
    math s1 "dz :∈ ℝ" |> ignore
    Assert.Equal("#t", eval s2 "(null? (declarations 'dz))")
    math s2 "dz :∈ positive" |> ignore
    Assert.Equal("1", eval s1 "(length (declarations 'dz))")
    Assert.Equal("1", eval s2 "(length (declarations 'dz))")
    Assert.Equal("positive", eval s2 "(sign-of 'dz)")
    Assert.NotEqual<string>("positive", eval s1 "(sign-of 'dz)")
    // знак в упрощении — по декларациям своей сессии
    Assert.Equal("true", str (math s2 "dz > 0") "pretty")
    Assert.NotEqual<string>("true", str (math s1 "dz > 0") "pretty")
    // assumptions ответа — свои
    let a1 = (call s1 """{"op":"eval","code":"1"}""").GetProperty("assumptions").[0].GetString()
    Assert.Equal("dz ∈ ℝ", a1)
    // системная pi > 0 — в обеих сессиях и в глобальной
    Assert.Equal("positive", eval s1 "(sign-of 'pi)")
    Assert.Equal("positive", eval s2 "(sign-of 'pi)")
    let inGlobal (code: string) = Printer.prettyPrint (Evaluator.eval (List.head (Reader.readAll code)) Evaluator.globalEnv)
    Assert.Equal("positive", inGlobal "(sign-of 'pi)")
    // глобальное окружение (REPL) деклараций сессий не видит
    Assert.Equal("#t", inGlobal "(null? (declarations 'dz))")
    // сброс одной сессии не трогает другую
    eval s1 "(math-reset)" |> ignore
    Assert.Equal("#t", eval s1 "(null? (declarations))")
    Assert.Equal("1", eval s2 "(length (declarations))")
    Assert.Equal("positive", eval s1 "(sign-of 'pi)")
    // MCP: reset снимает декларации сессии сервера
    let srv = McpHost.Server()
    srv.Call("math", args [ "code", el "w :∈ ℤ" ]) |> ignore
    Assert.Equal<string list>([ "w ∈ ℤ" ], srv.Call("math", args [ "code", el "1" ]).Assumptions)
    srv.Call("reset", args []) |> ignore
    Assert.Empty(srv.Call("math", args [ "code", el "1" ]).Assumptions)
