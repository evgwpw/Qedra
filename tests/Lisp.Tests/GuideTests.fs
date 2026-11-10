// Шаг GD.1: справка для LLM по запросу — ядро docs\guide\core.md и карточки docs\guide\topics\*.md (встроены в сборку),
// инструмент MCP guide(topic): размеры, подсказки при опечатке, функции карточек существуют, примеры выполняются.
// Соглашение примеров: блоки ```lisp; форма (или несколько строк формы) и необязательная строка «;=> текст» —
// ожидаемая печать результата; примеры разделены строкой «;=>» или пустой строкой; карточка выполняется в одной сессии.
module GuideTests

open System
open System.Collections.Generic
open System.IO
open System.Text
open System.Text.Json
open System.Text.RegularExpressions
open Xunit

let private el (s: string) : JsonElement = JsonSerializer.SerializeToElement s

let private args (kvs: (string * JsonElement) list) : IDictionary<string, JsonElement> =
    let d = Dictionary<string, JsonElement>()
    for k, v in kvs do d[k] <- v
    d :> IDictionary<_, _>

let private cardOf (t: string) : string = (Guide.card t).Value

[<Fact>]
let ``GD.1: guide без темы — ядро и список тем`` () =
    let r = McpHost.Server().Call("guide", args [])
    Assert.Equal(ToolResponse.Answer, r.Status)
    Assert.Contains("CAS guide for LLMs", r.Result.Value)
    Assert.Contains(Guide.core.Trim(), r.Result.Value)
    Assert.Contains("Available topics", r.Result.Value)
    // GD.2: 12 новых карточек плюс три прежние
    for t in [ "algebra"; "solve"; "calculus"; "integration"; "ode"; "sums"; "linear-algebra"; "polynomials"; "number-theory"
               "curves"; "plots"; "numerics"; "optimization"; "forms"; "domains"; "steps"; "units"; "variational" ] do
        Assert.Contains(t, Guide.topics)
    for t in Guide.allTopics do
        Assert.Contains(t, r.Result.Value)
        // каждая тема (и таблица synonyms) названа в ядре отдельной строкой списка
        Assert.Contains("* `" + t + "`", Guide.core)
    // инструменты из таблицы упомянуты в ядре
    for t in McpHost.tools do
        Assert.Contains("`" + t.Name + "`", Guide.core)
    // GD.2: ресурс lisp://guide — то же, что guide без темы (ядро и список тем)
    Assert.Equal(r.Result.Value, McpHost.guideText)
    Assert.Contains("CAS guide for LLMs", McpHost.guideText)

[<Fact>]
let ``GD.1: guide(topic) — карточка; пустая тема — как без темы`` () =
    let s = McpHost.Server()
    let r = s.Call("guide", args [ "topic", el "ode" ])
    Assert.Equal(ToolResponse.Answer, r.Status)
    Assert.Equal(cardOf "ode", r.Result.Value)
    Assert.Equal(cardOf "units", (s.Call("guide", args [ "topic", el " Units " ])).Result.Value)
    Assert.Contains("Available topics", (s.Call("guide", args [ "topic", el "" ])).Result.Value)

[<Fact>]
let ``GD.1: неизвестная тема — ошибка с подсказкой и списком`` () =
    let r = McpHost.Server().Call("guide", args [ "topic", el "intgration" ])
    Assert.Equal(ToolResponse.Error, r.Status)
    Assert.Contains("Did you mean: integration", r.Error.Value)
    Assert.Contains("Available topics: " + String.Join(", ", Guide.allTopics), r.Error.Value)
    let r2 = McpHost.Server().Call("guide", args [ "topic", el "zzzzzzzzzz" ])
    Assert.Equal(ToolResponse.Error, r2.Status)
    Assert.DoesNotContain("Did you mean", r2.Error.Value)
    Assert.Contains("units", r2.Error.Value)
    Assert.Equal(ToolResponse.Error, (McpHost.Server().Call("guide", args [ "topic", JsonSerializer.SerializeToElement 5 ])).Status)

[<Fact>]
let ``GD.1: размеры — ядро не больше 14000 байт, карточка не больше 6000`` () =
    let bytes (s: string) = Encoding.UTF8.GetByteCount s
    Assert.True(bytes Guide.core <= 14000, sprintf "core.md: %d байт" (bytes Guide.core))
    for t in Guide.topics do
        Assert.True(bytes (cardOf t) <= 6000, sprintf "%s.md: %d байт" t (bytes (cardOf t)))
        Assert.True((cardOf t).[0] <> char 0xFEFF, t + ": BOM")

// Имена из сигнатур раздела «## Functions»: все `(имя ...)` в строке маркера до первого «`: »
let private signatureNames (card: string) : string list =
    let lines = card.Replace("\r", "").Split('\n')
    let start = lines |> Array.findIndex (fun l -> l.StartsWith "## Functions")
    [ for l in lines |> Array.skip (start + 1) |> Array.takeWhile (fun l -> not (l.StartsWith "## ")) do
        if l.StartsWith "* `(" then
            let i = l.IndexOf "`: "
            let sigPart = if i < 0 then l else l.Substring(0, i + 1)
            for m in Regex.Matches(sigPart, @"`\(([^\s()`]+)") -> m.Groups.[1].Value ]

[<Fact>]
let ``GD.1: каждая функция из сигнатур карточек существует`` () =
    for t in Guide.topics do
        let names = signatureNames (cardOf t)
        Assert.True(names.Length >= 5, sprintf "%s: функций %d (нужно 5-15)" t names.Length)
        Assert.True(names.Length <= 15, sprintf "%s: функций %d (нужно 5-15)" t names.Length)
        for n in names do
            let text, ok = QueryCli.runCodeDefault "sig" n false false 1
            Assert.True(ok, sprintf "%s: нет функции %s (%s)" t n text)

// Примеры карточки: (форма, ожидаемая печать | None)
let private examples (card: string) : (string * string option) list =
    let lines = card.Replace("\r", "").Split('\n')
    let out = List<string * string option>()
    let mutable inBlock = false
    let cur = List<string>()
    let flush (expected: string option) =
        let text = String.Join("\n", cur).Trim()
        if text <> "" then out.Add((text, expected))
        cur.Clear()
    for l in lines do
        if l.StartsWith "```lisp" then inBlock <- true
        elif l.StartsWith "```" then
            flush None
            inBlock <- false
        elif inBlock then
            if l.StartsWith ";=>" then flush (Some (l.Substring(3).Trim()))
            elif l.Trim() = "" then flush None
            else cur.Add l
    List.ofSeq out

[<Fact>]
let ``GD.1: примеры карточек выполняются и дают ожидаемую печать`` () =
    for t in Guide.topics do
        let card = cardOf t
        let ex = examples card
        Assert.True(ex.Length >= 3, sprintf "%s: примеров %d (нужно 3 и больше)" t ex.Length)
        let s = McpHost.Server()
        for code, expected in ex do
            let r = s.Call("evaluate", args [ "code", el code; "timeout_s", JsonSerializer.SerializeToElement 60 ])
            Assert.True(r.Status = ToolResponse.Answer, sprintf "%s: %s => %A %A" t code r.Status r.Error)
            match expected with
            | Some e -> Assert.True((r.Result = Some e), sprintf "%s: %s => %A, ожидалось %s" t code r.Result e)
            | None -> ()

// --- Шаг GD.2: синонимы, ресурс lisp://guide, покрытие экспортов библиотеки карточками ---

[<Fact>]
let ``GD.2: guide(синоним) возвращает карточку; synonyms — таблица`` () =
    let s = McpHost.Server()
    let get (t: string) = (s.Call("guide", args [ "topic", el t ])).Result.Value
    Assert.Equal(cardOf "ode", get "DSolve")
    Assert.Equal(cardOf "number-theory", get "FactorInteger")
    Assert.Equal(cardOf "linear-algebra", get " eigenvalues ")
    Assert.Equal(cardOf "polynomials", get "GroebnerBasis")
    Assert.Equal(cardOf "integration", get "integrate")
    Assert.Equal(Guide.synonymsText, get "synonyms")
    // имя без синонима — по-прежнему ошибка с подсказками
    let bad = s.Call("guide", args [ "topic", el "NoSuchFunction" ])
    Assert.Equal(ToolResponse.Error, bad.Status)
    Assert.Contains("Available topics:", bad.Error.Value)

// Строки таблицы синонимов: (имена в нижнем регистре, чем вызвать — имена в кавычках, тема)
let private synonymRows : (string list * string list * string) list =
    let ticked (cell: string) = [ for m in Regex.Matches(cell, "`([^`]+)`") -> m.Groups.[1].Value ]
    [ for l in Guide.synonymsText.Replace("\r", "").Split('\n') do
        if l.StartsWith "| `" then
            let c = l.Split('|')
            yield (ticked c.[1] |> List.map (fun n -> n.ToLowerInvariant()), ticked c.[2], (ticked c.[3]).Head) ]

[<Fact>]
let ``GD.2: таблица синонимов согласована — темы есть, имена однозначны, функции существуют`` () =
    Assert.True(synonymRows.Length >= 40, sprintf "строк синонимов: %d" synonymRows.Length)
    for (names, _, topic) in synonymRows do
        Assert.True(Guide.card topic |> Option.isSome, "нет карточки " + topic)
        for n in names do Assert.Equal(Some topic, Guide.resolve n)
    // имя не ведёт на две разные темы
    let byName = synonymRows |> List.collect (fun (ns, _, t) -> ns |> List.map (fun n -> n, t)) |> List.distinct |> List.groupBy fst
    for (n, ts) in byName do Assert.True(ts.Length = 1, sprintf "синоним '%s' ведёт на несколько тем: %A" n ts)
    // имя карточки в таблице ведёт на неё же
    for t in Guide.allTopics do
        match Map.tryFind t Guide.synonyms with
        | Some target -> Assert.Equal(t, target)
        | None -> ()
    // «чем вызвать»: функции существуют (инструменты MCP — тоже имена)
    let tools = McpHost.tools |> List.map (fun t -> t.Name) |> Set.ofList
    for (_, here, topic) in synonymRows do
        for n in here do
            if not (tools.Contains n) then
                let text, ok = QueryCli.runCodeDefault "sig" n false false 1
                Assert.True(ok, sprintf "синонимы (%s): нет функции %s (%s)" topic n text)

let private repoDocsGuide : string =
    let rec find (d: DirectoryInfo) =
        if isNull d then failwith "не найден Lisp.slnx"
        elif File.Exists(Path.Combine(d.FullName, "Lisp.slnx")) then Path.Combine(d.FullName, "docs", "guide")
        else find d.Parent
    find (DirectoryInfo AppContext.BaseDirectory)

// Модули, чьи экспорты покрыты карточками. Вне проверки: mathlang (рантайм входного языка, docs\math-language.md),
// prelude (ядро языка, docs\lisp-library-guide.md), test (каркас тестов), rules (нет экспортов).
let private coveredModules =
    [ "algnum"; "cfinite"; "constzero"; "curves"; "definite"; "denest"; "domain"; "dp"; "elliptic"; "field"; "forms"; "gf"; "groebner"; "gruntz"
      "integrate"; "interval"; "laplace"; "limit"; "linalg"; "logic"; "lp"; "match"; "numtheory"; "ode"; "optimize"; "plot"; "poly"
      "puiseux"; "risch"; "series"; "set"; "solve"; "sos"; "specfun"; "steps"; "summation"; "tensor"; "transforms"; "trigsimp"; "units" ]

let private exportsOf (m: string) : string list =
    let json, ok = QueryCli.runCodeDefault "module" m true true 1
    Assert.True(ok, json)
    use doc = JsonDocument.Parse json
    [ for e in doc.RootElement.GetProperty("exports").EnumerateArray() -> e.GetProperty("name").GetString() ]

[<Fact>]
let ``GD.2: каждый экспорт покрытых модулей назван в карточке или в docs/guide/not-covered.txt`` () =
    // слова карточек: всё, что не пробел/скобка/кавычка/запятая; точка и двоеточие в конце отбрасываются
    let tokens = HashSet<string>()
    for t in Guide.topics do
        for m in Regex.Matches(cardOf t, @"[^\s()`,'""\[\]{}|]+") do
            tokens.Add(m.Value.TrimEnd('.', ';', ':')) |> ignore
    let allow =
        File.ReadAllLines(Path.Combine(repoDocsGuide, "not-covered.txt"))
        |> Array.map (fun l -> l.Trim())
        |> Array.filter (fun l -> l <> "" && not (l.StartsWith "#"))
    let isAllowed (n: string) =
        allow |> Array.exists (fun a -> if a.EndsWith "*" then n.StartsWith(a.TrimEnd '*') else a = n)
    let exports = coveredModules |> List.collect exportsOf |> List.distinct
    let missing = exports |> List.filter (fun n -> not (tokens.Contains n) && not (isAllowed n))
    Assert.True(missing.IsEmpty,
                sprintf "нет ни в одной карточке, ни в docs/guide/not-covered.txt (%d): %s" missing.Length (String.Join(" ", missing)))
    // список исключений не залеживается: каждая запись что-то исключает, а точное имя не названо в карточке
    for a in allow do
        let hits = exports |> List.filter (fun n -> if a.EndsWith "*" then n.StartsWith(a.TrimEnd '*') else a = n)
        Assert.True(not hits.IsEmpty, "not-covered.txt: запись ничего не исключает: " + a)
        if not (a.EndsWith "*") then Assert.True(not (tokens.Contains a), "not-covered.txt: имя уже в карточке: " + a)
