// Шаг 22.6: сертификаты в ответе (certificate: true) — derivative, substitution, equivalence, counterexample,
// ideal_membership, none; verified false → warning; флаг выключен → null; проверка входит в timeout_s
module CertificateTests

open System.Collections.Generic
open System.Text.Json
open Xunit

let private el (s: string) : JsonElement = JsonSerializer.SerializeToElement s
let private flag (b: bool) : JsonElement = JsonSerializer.SerializeToElement b

let private args (kvs: (string * JsonElement) list) : IDictionary<string, JsonElement> =
    let d = Dictionary<string, JsonElement>()
    for k, v in kvs do d[k] <- v
    d :> IDictionary<_, _>

// вызов инструмента с certificate: true → поле certificate ответа (JSON)
let private cert (s: McpHost.Server) (tool: string) (kvs: (string * JsonElement) list) : JsonElement =
    let r = s.Call(tool, args (kvs @ [ "certificate", flag true ]))
    JsonDocument.Parse(ToolResponse.toJson r).RootElement.GetProperty("certificate")

let private str (c: JsonElement) (name: string) : string = c.GetProperty(name).GetString()
let private detail (c: JsonElement) (name: string) : JsonElement = c.GetProperty("detail").GetProperty(name)
let private verified (c: JsonElement) : string =
    let v = c.GetProperty("verified")
    match v.ValueKind with
    | JsonValueKind.True -> "true"
    | JsonValueKind.False -> "false"
    | _ -> v.GetString()

[<Fact>]
let ``22.6: integrate — kind derivative, верно символьно; определённый — подстановка пределов`` () =
    let s = McpHost.Server()
    let c = cert s "integrate" [ "expr", el "x*sin(x)"; "var", el "x" ]
    Assert.Equal("derivative", str c "kind")
    Assert.Equal(JsonValueKind.True, c.GetProperty("verified").ValueKind)
    Assert.Contains("символьно", str c "method")
    Assert.Equal("x*sin(x)", (detail c "derivative").GetString())
    Assert.Equal("0", (detail c "residual").GetString())
    let d = cert s "integrate" [ "expr", el "x^2"; "var", el "x"; "from", el "0"; "to", el "3" ]
    Assert.Equal("true", verified d)
    Assert.Equal("9", (detail d "F(b) - F(a)").GetString())
    Assert.Equal(2, (detail d "limits").GetArrayLength())
    // несобственный интеграл (шаг DI.3): kind definite, интервальная проверка definite-check; ненайденный — skipped
    let inf = cert s "integrate" [ "expr", el "exp(-x)"; "var", el "x"; "from", el "0"; "to", el "inf" ]
    Assert.Equal("definite", str inf "kind")
    Assert.Equal("true", verified inf)
    let unk = cert s "integrate" [ "expr", el "x*asin(x)"; "var", el "x" ]   // 21k.5: exp(x^2), 21k″: sin(x)/x — nonelementary; asin вне Риша
    Assert.Equal("skipped", verified unk)
    Assert.Equal("derivative", str unk "kind")

// Шаг DI.3: определённые интегралы через модуль definite — kind definite; расходящийся: unknown + условие divergent
[<Fact>]
let ``DI.3: integrate с бесконечным пределом — kind definite; расходящийся — unknown, note и conditions`` () =
    let s = McpHost.Server()
    let call (kvs: (string * JsonElement) list) = JsonDocument.Parse(ToolResponse.toJson (s.Call("integrate", args kvs))).RootElement
    let r = call [ "expr", el "1/(1+x^2)"; "var", el "x"; "from", el "-inf"; "to", el "inf"; "certificate", flag true ]
    Assert.Equal("answer", r.GetProperty("status").GetString())
    Assert.Equal("pi", r.GetProperty("result").GetString())
    let c = r.GetProperty("certificate")
    Assert.Equal("definite", str c "kind")
    Assert.Equal("true", verified c)
    let d = call [ "expr", el "1/x^2"; "var", el "x"; "from", el "-1"; "to", el "1"; "certificate", flag true ]
    Assert.Equal("unknown", d.GetProperty("status").GetString())
    Assert.Contains("расходится", d.GetProperty("note").GetString())
    Assert.Contains("(divergent ", d.GetProperty("conditions").[0].GetProperty("sexpr").GetString())

[<Fact>]
let ``22.6: флаг выключен или не задан — certificate null`` () =
    let s = McpHost.Server()
    for kvs in [ []; [ "certificate", flag false ] ] do
        let r = s.Call("integrate", args ([ "expr", el "x"; "var", el "x" ] @ kvs))
        Assert.True(r.Certificate.IsNone)
        Assert.Equal(JsonValueKind.Null, JsonDocument.Parse(ToolResponse.toJson r).RootElement.GetProperty("certificate").ValueKind)
    // схема: boolean; ошибочное значение — ошибка аргумента
    let schema = McpHost.inputSchema (McpHost.tools |> List.find (fun t -> t.Name = "solve"))
    Assert.Equal("boolean", schema.GetProperty("properties").GetProperty("certificate").GetProperty("type").GetString())
    let bad = s.Call("integrate", args [ "expr", el "x"; "var", el "x"; "certificate", el "maybe" ])
    Assert.Equal(ToolResponse.Error, bad.Status)
    // --json: строка "true" тоже годится, прочее — ошибка протокола
    let ses = AgentApi.makeSession ()
    let j (json: string) = JsonDocument.Parse(AgentApi.handleJsonRequest ses json).RootElement
    Assert.Equal(JsonValueKind.Object, (j """{"op":"integrate","code":"x","var":"x","certificate":"true"}""").GetProperty("certificate").ValueKind)
    Assert.Equal("error", (j """{"op":"integrate","code":"x","var":"x","certificate":5}""").GetProperty("status").GetString())

// Шаг 21k.4: алгоритм Риша доказал неэлементарность — status nonelementary, условие risch-nonelementary, сертификат kind nonelementary;
// частичный ответ — answer с предупреждением; exp-уровень — unknown
[<Fact>]
let ``21k.4: integrate 1/log x — status nonelementary, note, conditions, сертификат nonelementary; log(log x) — частичный answer`` () =
    let s = McpHost.Server()
    let call (kvs: (string * JsonElement) list) = JsonDocument.Parse(ToolResponse.toJson (s.Call("integrate", args kvs))).RootElement
    let r = call [ "expr", el "1/log(x)"; "var", el "x"; "certificate", flag true ]
    Assert.Equal("nonelementary", r.GetProperty("status").GetString())
    Assert.Equal("(integrate (^ (log x) -1) x)", r.GetProperty("result").GetString())
    Assert.Contains("неэлементарен", r.GetProperty("note").GetString())
    Assert.Equal("(risch-nonelementary (integrate (^ (log x) -1) x))", r.GetProperty("conditions").[0].GetProperty("sexpr").GetString())
    Assert.True(r.GetProperty("ok").GetBoolean())
    let c = r.GetProperty("certificate")
    Assert.Equal("nonelementary", str c "kind")
    Assert.Equal("skipped", verified c)
    Assert.Contains("неэлементарен", (detail c "reason").GetString())
    let p = call [ "expr", el "log(log(x))"; "var", el "x" ]
    Assert.Equal("answer", p.GetProperty("status").GetString())
    Assert.Contains("integrate", p.GetProperty("result").GetString())
    Assert.Equal(JsonValueKind.Array, p.GetProperty("warnings").ValueKind)
    // 21k.5: exp-уровень — RDE Dy + 2xy = 1 без решения: exp(x²) доказанно неэлементарен
    let e = call [ "expr", el "exp(x^2)"; "var", el "x" ]
    Assert.Equal("nonelementary", e.GetProperty("status").GetString())
    Assert.Equal("(risch-nonelementary (integrate (exp (^ x 2)) x))", e.GetProperty("conditions").[0].GetProperty("sexpr").GetString())
    // алгебраика вне R3 — по-прежнему «не знаю»; sqrt(log x) — смешанный случай R3.2 (s² = log x, ∫2s²e^{s²}ds) — неэлементарен
    let u = call [ "expr", el "sqrt(x + log(x))"; "var", el "x" ]
    Assert.Equal("unknown", u.GetProperty("status").GetString())
    let w = call [ "expr", el "sqrt(log(x))"; "var", el "x" ]
    Assert.Equal("nonelementary", w.GetProperty("status").GetString())

[<Fact>]
let ``22.6: solve — подстановка в уравнения: одно уравнение, система, параметр`` () =
    let s = McpHost.Server()
    let c = cert s "solve" [ "equations", el "x^2 - 5x + 6 = 0"; "vars", el "x" ]
    Assert.Equal("substitution", str c "kind")
    Assert.Equal("true", verified c)
    Assert.Equal(2, (detail c "solutions").GetArrayLength())
    Assert.Equal("symbolic", (detail c "solutions").[0].GetProperty("check").GetString())
    let sys = cert s "solve" [ "equations", el "[x + y = 3, x*y = 2]"; "vars", el "[x, y]" ]
    Assert.Equal("true", verified sys)
    Assert.Equal(2, (detail sys "solutions").GetArrayLength())
    Assert.Equal(2, (detail sys "solutions").[0].GetProperty("residuals").GetArrayLength())
    Assert.Equal("true", verified (cert s "solve" [ "equations", el "a*x = 1"; "vars", el "x" ]))
    // иррациональные корни: подстановка символьно
    Assert.Equal("true", verified (cert s "solve" [ "equations", el "x^2 - 2 = 0"; "vars", el "x" ]))
    // нет решений: skipped
    let none = cert s "solve" [ "equations", el "[x + y = 1, x + y = 2]"; "vars", el "[x, y]" ]
    Assert.Equal("skipped", verified none)
    Assert.Equal("substitution", str none "kind")

[<Fact>]
let ``22.6: solve с root-of — часть решений проверена численно, неявный корень skipped`` () =
    let s = McpHost.Server()
    let c = cert s "solve" [ "equations", el "x^5 - x - 1 = 0"; "vars", el "x" ]
    Assert.Equal("substitution", str c "kind")
    Assert.Equal("partial", verified c)
    let sols = detail c "solutions"
    let checks = [ for i in 0 .. sols.GetArrayLength() - 1 -> sols.[i].GetProperty("check").GetString() ]
    Assert.Contains("skipped", checks)
    Assert.Contains("symbolic", checks)

[<Fact>]
let ``22.6: groebner — ideal_membership, остатки образующих равны 0`` () =
    let s = McpHost.Server()
    let c = cert s "groebner" [ "polys", el "[x^2 + y, x*y - 1]"; "vars", el "[x, y]" ]
    Assert.Equal("ideal_membership", str c "kind")
    Assert.Equal("true", verified c)
    let rems = detail c "remainders"
    Assert.Equal(2, rems.GetArrayLength())
    Assert.Equal("0", rems.[0].GetProperty("remainder").GetString())
    Assert.Contains("обратное вложение не проверяется", str c "method")
    let g = cert s "groebner" [ "polys", el "[x^2 + y, x*y - 1]"; "vars", el "[x, y]"; "order", el "grevlex" ]
    Assert.Equal("true", verified g)

[<Fact>]
let ``22.6: simplify, expand, factor, together, apart — equivalence`` () =
    let s = McpHost.Server()
    for tool, expr, extra in
        [ "expand", "(x+1)^3", []
          "factor", "x^3 - x", []
          "simplify", "sin(x)^2 + cos(x)^2", []
          "together", "1/x + 1/y", []
          "apart", "1/(x^2 - 1)", [ "var", el "x" ] ] do
        let c = cert s tool ([ "expr", el expr ] @ extra)
        Assert.Equal("equivalence", str c "kind")
        Assert.True(verified c = "true", tool)
        Assert.Contains("символьно", str c "method")
        Assert.Equal(expr.Replace("x+1", "x + 1"), (detail c "original").GetString())
    // с переменной сессии: исходное с подстановкой переменной — тоже эквивалентно, не «false»
    s.Call("math", args [ "code", el "ca := 2" ]) |> ignore
    Assert.Equal("true", verified (cert s "expand" [ "expr", el "(ca + x)^2" ]))
    // diff, limit, series: none с причиной
    let d = cert s "diff" [ "expr", el "x^2"; "var", el "x" ]
    Assert.Equal("none", str d "kind")
    Assert.Equal("skipped", verified d)
    Assert.Equal("none", str (cert s "limit" [ "expr", el "sin(x)/x"; "var", el "x"; "point", el "0" ]) "kind")
    Assert.Equal("none", str (cert s "series" [ "expr", el "exp(x)"; "var", el "x" ]) "kind")

[<Fact>]
let ``22.6: equivalent — false даёт counterexample, true — equivalence, unknown — none`` () =
    let s = McpHost.Server()
    let f = cert s "equivalent" [ "a", el "x^2"; "b", el "x^2 + 1" ]
    Assert.Equal("counterexample", str f "kind")
    Assert.Equal("true", verified f)             // рациональная точка подставлена точно
    Assert.Contains("точная подстановка", str f "method")
    Assert.True((detail f "point").TryGetProperty("x") |> fst)
    Assert.True((detail f "first").GetString() <> (detail f "second").GetString())
    let t = cert s "equivalent" [ "a", el "(x+1)^2"; "b", el "x^2 + 2x + 1" ]
    Assert.Equal("equivalence", str t "kind")
    Assert.Equal("true", verified t)
    let u = cert s "equivalent" [ "a", el "sin(2x)"; "b", el "2*sin(x)*cos(x)" ]
    Assert.Equal("none", str u "kind")
    Assert.Equal("skipped", verified u)
    // неточный контрпример (иррациональные значения) — численный
    let n = cert s "equivalent" [ "a", el "sin(x)"; "b", el "cos(x)" ]
    Assert.Equal("counterexample", str n "kind")
    Assert.Equal("numeric", verified n)

[<Fact>]
let ``22.6: неверный ответ — verified false и warning, статус answer`` () =
    let s = McpHost.Server()
    let ev (code: string) = s.Call("evaluate", args [ "code", el code ]) |> ignore
    // Подмены обязательно снимаются в finally: методы defmethod (например, integrate тензора в lib\tensor.lisp) —
    // общие для процесса замыкания ПОСЛЕДНЕГО созданного окружения, и подменённый integrate этой сессии иначе
    // протекал бы в другие тесты (TensorTests.integrate тензора — покомпонентно: ответ 1/2 x^3 вместо (* a x))
    ev "(define cert-orig-integrate integrate) (define cert-orig-solve solve) (define cert-orig-groebner groebner)"
    try
        // подмена интегратора в сессии: ответ x^3/2 для x^2
        ev "(define (integrate e x) (quote (* 1/2 (^ x 3))))"
        let r = s.Call("integrate", args [ "expr", el "x^2"; "var", el "x"; "certificate", flag true ])
        Assert.Equal(ToolResponse.Answer, r.Status)
        Assert.Equal("false", r.Certificate.Value.Verified)
        Assert.Equal("derivative", r.Certificate.Value.Kind)
        Assert.Contains(r.Warnings, fun w -> w.Contains "не прошёл проверку")
        // тот же ответ без флага — предупреждения нет
        Assert.True((s.Call("integrate", args [ "expr", el "x^2"; "var", el "x" ])).Warnings.IsEmpty)
        // подмена solve: лишний «корень»
        ev "(define (solve e x) (list->set (list 5 (quote (^ 2 1/2)))))"
        let sr = s.Call("solve", args [ "equations", el "x^2 - 2 = 0"; "vars", el "x"; "certificate", flag true ])
        Assert.Equal(ToolResponse.Answer, sr.Status)
        Assert.Equal("false", sr.Certificate.Value.Verified)
        Assert.Equal("substitution", sr.Certificate.Value.Kind)
        Assert.NotEmpty sr.Warnings
        // подмена groebner (вызов в синтаксисе lisp идёт через сессию): базис не содержит образующих
        ev "(define (groebner fs vars &rest o) (list (quote x)))"
        let gr = s.Call("groebner", args [ "polys", el "((+ (^ x 2) y) (- (* x y) 1))"; "vars", el "(x y)"; "syntax", el "lisp"
                                           "certificate", flag true ])
        Assert.Equal("false", gr.Certificate.Value.Verified)
        Assert.Equal("ideal_membership", gr.Certificate.Value.Kind)
        Assert.Contains(gr.Warnings, fun w -> w.Contains "не прошёл проверку")
    finally
        ev "(define integrate cert-orig-integrate) (define solve cert-orig-solve) (define groebner cert-orig-groebner)"

[<Fact; Trait("Category", "Slow")>]
let ``22.6: проверка не уложилась в timeout_s — verified timeout, ответ сохранён`` () =
    let s = McpHost.Server()
    let ev (code: string) = s.Call("evaluate", args [ "code", el code ]) |> ignore
    // подмена снимается в finally (см. тест «неверный ответ»: подмены сессии не должны протекать в другие тесты)
    ev "(define cert-orig-int-check-how int-check-how)"
    try
        ev "(define (spin n) (spin (+ n 1)))"
        ev "(define (int-check-how F e x) (spin 0))"
        let sw = System.Diagnostics.Stopwatch.StartNew()
        let r = s.Call("integrate", args [ "expr", el "x^2"; "var", el "x"; "certificate", flag true; "timeout_s", JsonSerializer.SerializeToElement 1 ])
        Assert.Equal(ToolResponse.Answer, r.Status)
        Assert.Equal(Some "1/3*x^3", r.Pretty)
        Assert.Equal("timeout", r.Certificate.Value.Verified)
        Assert.False(r.TimedOut)
        Assert.True(sw.ElapsedMilliseconds < 5000L, sprintf "заняло %d мс" sw.ElapsedMilliseconds)
        Assert.False(Cancel.requested)
        // сессия работает дальше
        Assert.Equal(Some "3", (s.Call("evaluate", args [ "code", el "(+ 1 2)" ])).Result)
    finally
        ev "(define int-check-how cert-orig-int-check-how)"

[<Fact>]
let ``22.6: --json — certificate у integrate на языке Lisp и формат объекта`` () =
    let ses = AgentApi.makeSession ()
    let r =
        JsonDocument.Parse(AgentApi.handleJsonRequest ses """{"op":"integrate","code":"(* x (exp x))","var":"x","certificate":true}""").RootElement
    let c = r.GetProperty("certificate")
    Assert.Equal<string list>([ "kind"; "verified"; "method"; "detail" ], c.EnumerateObject() |> Seq.map (fun p -> p.Name) |> List.ofSeq)
    Assert.Equal("derivative", str c "kind")
    Assert.Equal(JsonValueKind.True, c.GetProperty("verified").ValueKind)
    // math-программа и eval: none
    let m = JsonDocument.Parse(AgentApi.handleJsonRequest ses """{"op":"math","code":"1 + 1","certificate":true}""").RootElement
    Assert.Equal("none", str (m.GetProperty("certificate")) "kind")
