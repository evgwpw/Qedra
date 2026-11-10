// Тесты запросов к коду (CodeIndex.fs, Lisp.exe --query и MCP-инструмент code): Q.1
module QueryTests

open System
open System.Text.Json
open Xunit

let private idx (tests: bool) = CodeIndex.getIndex None [] tests

let private qOpts = CodeIndex.defaultOpts

let private ask (kind: string) (arg: string) : string * bool =
    CodeIndex.run (idx true) kind arg qOpts

let private text kind arg = fst (ask kind arg)

[<Fact>]
let ``Q.1: def — расположение, сигнатура, модуль, тело`` () =
    let t = text "def" "alg-factor"
    Assert.Contains("lib/algnum.lisp", t)
    Assert.Contains("(alg-factor F f x)", t)
    Assert.Contains("algnum, exported", t)
    Assert.Contains("(define (alg-factor F f x)", t)

[<Fact>]
let ``Q.1: def --no-body не печатает исходник, но оставляет комментарий`` () =
    let t, ok = CodeIndex.run (idx false) "def" "alg-factor" { qOpts with NoBody = true }
    Assert.True ok
    Assert.DoesNotContain("(define (alg-factor", t)
    Assert.Contains("lib/algnum.lisp", t)

[<Fact>]
let ``Q.1: sig — одна строка, &rest, макрос, builtin`` () =
    let s = text "sig" "fm-nullspace"
    Assert.Contains("(fm-nullspace F m)", s)
    Assert.Contains("field", s)
    Assert.Contains("lib/field.lisp:", s)
    Assert.DoesNotContain("\n", s)
    Assert.Contains("&rest opts", text "sig" "alg-field")
    let m = text "sig" "when"
    Assert.Contains("macro", m)
    Assert.Contains("&rest body", m)
    Assert.Contains("builtin", text "sig" "car")

[<Fact>]
let ``Q.1: квалифицированные имена модуль::имя`` () =
    Assert.Contains("lib/ode/core.lisp", text "sig" "ode::dsolve")
    Assert.Contains("lib/field.lisp", text "def" "field::fm-nullspace")
    let t, ok = ask "sig" "algnum::dsolve"
    Assert.False ok
    Assert.Contains("нет такого имени", t)

[<Fact>]
let ``Q.1: неизвестное имя — подсказка ближайших`` () =
    let t, ok = ask "def" "dsolvee"
    Assert.False ok
    Assert.Contains("нет такого имени", t)
    Assert.Contains("возможно:", t)
    Assert.Contains("dsolve", t)

[<Fact>]
let ``Q.1: callers/callees с глубиной, refs`` () =
    let c1 = text "callers" "alg-factor"
    Assert.Contains("factor-over", c1)
    let d2, _ = CodeIndex.run (idx true) "callers" "alg-factor" { qOpts with Depth = 2 }
    Assert.Contains("(cv-roots K cs)", d2)
    Assert.DoesNotContain("(cv-roots K cs)", c1)
    let ce = text "callees" "ode-dsolve-main"
    Assert.Contains("ode-order", ce)
    let r = text "refs" "fm-nullspace"
    Assert.Contains("tests/Lisp.Tests/lisp/field.lisp", r)

[<Fact>]
let ``Q.1: outline — определения без тел`` () =
    let o = text "outline" "lib/algnum.lisp"
    Assert.Contains("alg-factor", o)
    Assert.Contains("*(alg-factor F f x)", o)
    Assert.DoesNotContain("(define", o)
    Assert.Contains("lib/algnum.lisp", text "outline" "algnum.lisp")
    Assert.Contains("dsolve", text "outline" "ode/core.lisp")
    Assert.Contains("fm-nullspace", text "outline" "lib/field.lisp")

[<Fact>]
let ``Q.1: search — по имени и по комментарию, русские слова`` () =
    let s = text "search" "разложение многочлена над полем"
    Assert.Contains("(factor ", s)
    Assert.True((s.Split('\n').Length <= 10))
    Assert.Contains("fm-nullspace", text "search" "nullspace")
    Assert.Contains("dsolve", text "search" "dsolve")

[<Fact>]
let ``Q.1: module — экспорты и зависимости; deps файла`` () =
    let m = text "module" "ode"
    Assert.Contains("(dsolve eq yx &rest args)", m)
    Assert.Contains("зависит от", m)
    Assert.Contains("solve", m)
    let d = text "deps" "lib/ode/linear.lisp"
    Assert.Contains("prelude:", d)
    let t, ok = ask "module" "ody"
    Assert.False ok
    Assert.Contains("возможно: ode", t)

[<Fact>]
let ``Q.1: unused — приватные и экспорт без ссылок`` () =
    let u = text "unused" ""
    Assert.Contains("приватные без ссылок", u)
    Assert.Contains("экспорт без ссылок", u)
    // используемая функция в списках не встречается
    Assert.DoesNotContain("(alg-factor F f x)", u)

[<Fact>]
let ``Q.1: --json — корректный JSON`` () =
    let j, ok = CodeIndex.run (idx false) "def" "alg-factor" { qOpts with Json = true }
    Assert.True ok
    use doc = JsonDocument.Parse j
    let first = doc.RootElement.[0]
    Assert.Equal("alg-factor", first.GetProperty("name").GetString())
    Assert.True(first.GetProperty("exported").GetBoolean())
    Assert.Contains("(define", first.GetProperty("body").GetString())
    for kind, arg in [ "sig", "dsolve"; "outline", "lib/algnum.lisp"; "module", "ode"; "search", "корни"; "unused", "" ] do
        let j, _ = CodeIndex.run (idx true) kind arg { qOpts with Json = true }
        JsonDocument.Parse(j).Dispose()

[<Fact>]
let ``Q.1: неизвестный вид запроса`` () =
    let t, ok = ask "frobnicate" "x"
    Assert.False ok
    Assert.Contains("def", t)

[<Fact>]
let ``Q.1: каждое экспортированное имя каждого модуля находится запросом def`` () =
    let ix = idx false
    let env = Evaluator.newEnv ()
    let missing =
        [ for kv in ix.Modules do
            for e in kv.Value.Exports do
                let defined = ix.ByName.ContainsKey e && ix.ByName.[e] |> Seq.exists (fun d -> d.Module = kv.Key)
                // экспорт может быть builtin (F#) — тогда определения в lib нет
                if not defined && (env.Lookup e).IsNone then yield kv.Key + "::" + e ]
    Assert.Empty missing
    // и сам запрос def отвечает на каждое такое имя без «нет такого»
    for kv in ix.Modules do
        for e in kv.Value.Exports do
            let t, ok = CodeIndex.run ix "def" (kv.Key + "::" + e) { qOpts with NoBody = true }
            if ix.ByName.ContainsKey e && ix.ByName.[e] |> Seq.exists (fun d -> d.Module = kv.Key) then
                Assert.True(ok, t)

[<Fact>]
let ``Q.2: MCP-инструмент code — те же виды, json, ошибки`` () =
    let el (v: obj) : JsonElement = JsonSerializer.SerializeToElement v
    let args (kvs: (string * JsonElement) list) : Collections.Generic.IDictionary<string, JsonElement> =
        let d = Collections.Generic.Dictionary<string, JsonElement>()
        for k, v in kvs do d[k] <- v
        d :> _
    let s = McpHost.Server()
    let r = s.Call("code", args [ "kind", el "sig"; "arg", el "alg-factor" ])
    Assert.Equal(ToolResponse.Answer, r.Status)
    Assert.Contains("lib/algnum.lisp", r.Result.Value)
    let j = s.Call("code", args [ "kind", el "def"; "arg", el "dsolve"; "json", el true; "no_body", el true ])
    Assert.Equal(ToolResponse.Answer, j.Status)
    use doc = JsonDocument.Parse j.Result.Value
    Assert.Equal("dsolve", doc.RootElement.[0].GetProperty("name").GetString())
    let c = s.Call("code", args [ "kind", el "callers"; "arg", el "alg-factor"; "depth", el 2 ])
    Assert.Contains("(cv-roots K cs)", c.Result.Value)
    let o = s.Call("code", args [ "kind", el "outline"; "arg", el "ode/core.lisp" ])
    Assert.Contains("dsolve", o.Result.Value)
    let bad = s.Call("code", args [ "kind", el "sig"; "arg", el "dsolvee" ])
    Assert.Equal(ToolResponse.Error, bad.Status)
    Assert.Contains("возможно", bad.Error.Value)
    Assert.Equal(ToolResponse.Error, (s.Call("code", args [ "arg", el "x" ])).Status)
    Assert.Equal(ToolResponse.Error, (s.Call("code", args [ "kind", el "sig"; "bogus", el "1" ])).Status)
    Assert.Contains(McpHost.tools, fun t -> t.Name = "code")

// ---------- Q.3: поиск (стемминг, глоссарий, BM25, альтернативы, опечатки) ----------

// имена из первых n строк ответа search
let private topNames (q: string) (n: int) : string list =
    (text "search" q).Split('\n')
    |> Array.truncate n
    |> Array.map (fun l -> Text.RegularExpressions.Regex.Match(l, @"^\(?([^\s()]+)").Groups.[1].Value)
    |> List.ofArray

let private isSqfree (n: string) = n.Contains "sqfree" || n.Contains "squarefree"

[<Fact>]
let ``Q.3: поиск — русская морфология и глоссарий находят функции`` () =
    // (запрос, допустимые имена в первой тройке)
    let cases =
        [ "бесквадратное разложение", [ "sqfree"; "fp-sqfree"; "alg-poly-sqfree"; "gf-sqfree" ]
          "ядро матрицы над полем", [ "fm-nullspace" ]
          "ядро матрицы", [ "nullspace"; "fm-nullspace" ]
          "простота числа с сертификатом", [ "pratt-certificate" ]
          "разложение многочлена над расширением", [ "alg-factor"; "factor-over" ]
          "потенциал векторного поля", [ "vf-potential" ]
          "решить дифференциальное уравнение", [ "dsolve"; "dsolve-check"; "dsolve-conditions-check" ]
          "род кривой", [ "curve-genus" ]
          "особые точки кривой", [ "singular-points"; "curve-singular?" ]
          "интервал для интеграла", [ "certified-integral" ]
          "НОД многочленов над GF(p)", [ "gf-poly-gcd"; "fp-gcd" ]
          "собственные значения матрицы", [ "eigenvalues" ]
          "симплекс-метод линейное программирование", [ "lp-simplex"; "lp-simplex-iter" ]
          "prime certificate", [ "pratt-certificate" ]
          "ряд Пюизё алгебраической кривой", [ "algebraic-series" ] ]
    for q, expect in cases do
        let top = topNames q 3
        Assert.True(top |> List.exists (fun n -> List.contains n expect), sprintf "«%s»: ожидалось %A в первой тройке, получено %A" q expect top)

[<Fact>]
let ``Q.3: поиск — английский запрос, дефисная запись, опечатка`` () =
    Assert.True(topNames "square-free factorization" 3 |> List.exists isSqfree, sprintf "%A" (topNames "square-free factorization" 5))
    Assert.True(topNames "squarefree decomposition" 3 |> List.exists isSqfree, sprintf "%A" (topNames "squarefree decomposition" 5))
    // опечатка в слове (триграммы + глоссарий)
    Assert.True(topNames "бесквадртное" 3 |> List.exists isSqfree, sprintf "%A" (topNames "бесквадртное" 5))
    Assert.True(topNames "бесквадратое разложение" 3 |> List.exists isSqfree, sprintf "%A" (topNames "бесквадратое разложение" 5))

[<Fact>]
let ``Q.3: поиск — альтернативы через | и точное имя`` () =
    let top = topNames "бесквадратное разложение | sqfree" 10
    Assert.Contains("alg-poly-sqfree", top)
    Assert.Contains("fp-sqfree", top)
    // альтернативы — объединение: каждая альтернатива по отдельности даёт свои результаты в объединении
    let u = topNames "nullspace | pratt-certificate" 10
    Assert.Contains("fm-nullspace", u)
    Assert.Contains("pratt-certificate", u)
    // точное имя — первым, даже если есть более длинные совпадения (dsolve-check)
    Assert.Equal("dsolve", (topNames "dsolve" 1).Head)

[<Fact>]
let ``Q.3: поиск — стеммеры и глоссарий`` () =
    Assert.Equal(SearchText.ruStem "бесквадратная", SearchText.ruStem "бесквадратное")
    Assert.Equal(SearchText.ruStem "разложение", SearchText.ruStem "разложения")
    Assert.Equal(SearchText.ruStem "ёлка", SearchText.ruStem "елка")
    Assert.Equal(SearchText.enStem "factoring", SearchText.enStem "factors")
    Assert.Equal(SearchText.enStem "integral", SearchText.enStem "integrals")
    Assert.Equal<string list>([ "fp-sqfree"; "fp"; SearchText.enStem "sqfree" ], SearchText.tokenizeName "fp-sqfree")
    Assert.Equal<string list>([ "gcd" ], SearchText.tokenize "the gcd of")
    let g = SearchText.parseGlossary [ "# комментарий"; "бесквадратный|sqfree|square free" ]
    let extra, demoted = SearchText.expand g (Collections.Generic.HashSet<string>(SearchText.tokenize "square free"))
    Assert.Contains((SearchText.enStem "sqfree", 0.9), extra)
    Assert.Contains(SearchText.enStem "square", demoted)

[<Fact>]
let ``Q.3: поиск — без результатов, пустой запрос, builtin из справочника, json`` () =
    let t, _ = ask "search" "кракозябра"
    Assert.Contains("ничего не найдено", t)
    let e, ok = ask "search" "   |  "
    Assert.False ok
    Assert.Contains("пустой", e)
    // builtin без определения в lib находится по описанию из docs/lisp-library-guide.md
    Assert.Contains("builtin", text "search" "sqfree")
    let j, _ = CodeIndex.run (idx true) "search" "род кривой" { qOpts with Json = true }
    use doc = JsonDocument.Parse j
    Assert.True(doc.RootElement.GetArrayLength() <= 10)

[<Fact>]
let ``Q.3: поиск — холодный поиск по полному индексу укладывается во время`` () =
    let sw = Diagnostics.Stopwatch.StartNew()
    let ix = CodeIndex.getIndex None [] true
    ix.SearchCache <- null
    CodeIndex.run ix "search" "ядро матрицы" qOpts |> ignore
    Assert.True(sw.Elapsed.TotalSeconds < 6.0, sprintf "%.1f с" sw.Elapsed.TotalSeconds)
