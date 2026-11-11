// Шаг DOCTEST: примеры документации — тесты. Во всех docs\**\*.md (кроме archive, tasks), README.md, README.en.md и
// publish\nuget\README.nuget.md находятся блоки примеров:
//   math> ввод                      — сеанс REPL входного языка; вывод — строки до следующего «math> » или конца блока
//   $ qedra --math -e "ввод"        — вызов CLI (каждый вызов — отдельный процесс, значит новая сессия); прочие «$ …» не проверяются
// Блок кода («```» … «```») — одна сессия, примеры выполняются сверху вниз (присваивания действуют дальше).
// Разметка «не сравнивать» (описана в docs\math-language.md, раздел «Примеры в документации»):
//   * пустой ожидаемый вывод — пример выполняется (без ошибки), печать не сверяется;
//   * строка вывода «…» — любое число строк (в т. ч. ни одной): случайность, время, длинный вывод;
//   * единственная строка вывода «…» — пример выполняется, печать не сверяется.
// Известный дефект кода — список knownDefects (файл, ввод, причина): пример обязан по-прежнему расходиться с документацией;
// когда дефект исправят, тест напомнит убрать запись. Ложный ответ в документации «узаконивать» нельзя.
module DocExamplesTests

open System
open System.Collections.Generic
open System.IO
open Xunit
open Types
open Evaluator

type Example =
    { Id: string            // «файл:строка» (строка ввода)
      File: string
      Input: string
      Expected: string list // строки без краевых пробелов, без пустых
      Block: int }          // номер блока кода в файле (сессия)

let private repoRoot : Lazy<string> =
    lazy (
        let rec find (dir: DirectoryInfo) =
            if isNull dir then failwith "не найден корень репозитория (Lisp.slnx)"
            elif File.Exists(Path.Combine(dir.FullName, "Lisp.slnx")) then dir.FullName
            else find dir.Parent
        find (DirectoryInfo AppContext.BaseDirectory))

let private docFiles () : string list =
    let root = repoRoot.Value
    let skip (rel: string) =
        rel.StartsWith "docs/archive/" || rel.StartsWith "docs/tasks/" || rel.StartsWith "research/"
    let docs =
        Directory.GetFiles(Path.Combine(root, "docs"), "*.md", SearchOption.AllDirectories)
        |> Array.map (fun p -> Path.GetRelativePath(root, p).Replace('\\', '/'))
        |> Array.filter (skip >> not)
        |> Array.sort
        |> List.ofArray
    [ "README.md"; "README.en.md"; "publish/nuget/README.nuget.md" ] @ docs
    |> List.filter (fun r -> File.Exists(Path.Combine(root, r)))

let private clean (lines: string list) : string list =
    lines |> List.map (fun l -> l.Trim()) |> List.filter (fun l -> l <> "")

// «$ qedra --math -e "ввод"» → ввод (для прочих «$ …» — None)
let private cliInput (line: string) : string option =
    let l = line.Substring(2).TrimStart()
    let prefixes = [ "qedra --math -e \""; "Lisp.exe --math -e \"" ]
    prefixes
    |> List.tryPick (fun p ->
        if l.StartsWith p && l.TrimEnd().EndsWith "\"" then
            let t = l.TrimEnd()
            Some(t.Substring(p.Length, t.Length - p.Length - 1))
        else None)

let private parseFile (rel: string) : Example list =
    let lines = File.ReadAllText(Path.Combine(repoRoot.Value, rel)).Replace("\r\n", "\n").Split('\n')
    let result = List<Example>()
    let mutable inFence = false
    let mutable block = 0
    // текущий пример: (строка, ввод, накопленный вывод, признак CLI)
    let mutable cur : (int * string * List<string> * bool) option = None
    let flush () =
        match cur with
        | Some(ln, input, out, _) ->
            result.Add { Id = sprintf "%s:%d" rel ln; File = rel; Input = input; Expected = clean (List.ofSeq out); Block = block }
            cur <- None
        | None -> ()
    for i in 0 .. lines.Length - 1 do
        let l = lines.[i]
        if l.StartsWith "```" then
            flush ()
            inFence <- not inFence
            if inFence then block <- block + 1
        elif inFence then
            if l.StartsWith "math> " then
                flush ()
                cur <- Some(i + 1, l.Substring(6).Trim(), List<string>(), false)
            elif l.StartsWith "$ " then
                flush ()
                match cliInput l with
                | Some input ->
                    block <- block + 1        // каждый вызов CLI — своя сессия
                    cur <- Some(i + 1, input, List<string>(), true)
                | None -> ()
            else
                match cur with
                | Some(_, _, out, _) -> out.Add l
                | None -> ()
    flush ()
    List.ofSeq result

let private allExamples : Lazy<Example list> = lazy (docFiles () |> List.collect parseFile)

// Известные дефекты кода: (файл, ввод) → причина. Пример исключается из сверки «вывод = документация» и вместо этого
// проверяется «вывод всё ещё расходится» (см. шапку).
let private knownDefects : Map<string * string, string> = Map.empty

// --- выполнение ---

let private runInput (env: Env) (input: string) : string =
    let sb = Text.StringBuilder()
    let add (s: string) = if s <> "" then (if sb.Length > 0 then sb.Append '\n' |> ignore); sb.Append s |> ignore
    try
        for ast in MathReader.mathParseProgramFrom "<doc>" input do
            eval (LispList [ LispSym "m-capture-start" ]) env |> ignore
            let v =
                try AgentApi.evalMathTree env ast
                finally
                    match eval (LispList [ LispSym "m-capture-end" ]) env with
                    | LispStr s -> add (s.TrimEnd('\n', '\r'))
                    | _ -> ()
            add (Printer.limitPrint v (MathPrinter.mathPrintLang v))
    with ex ->
        add ("ОШИБКА: " + AgentApi.plainErrorMessage ex)
    sb.ToString()

// результаты блока: Id → фактический вывод; блок выполняется один раз, целиком (сверху вниз)
let private blockResults = Dictionary<string * int, Dictionary<string, string>>()

let private resultsOf (ex: Example) : Dictionary<string, string> =
    lock blockResults (fun () ->
        match blockResults.TryGetValue((ex.File, ex.Block)) with
        | true, r -> r
        | _ ->
            let env = AgentApi.makeSession ()
            eval (LispList [ LispSym "math-reset" ]) env |> ignore
            let r = Dictionary<string, string>()
            for e in allExamples.Value |> List.filter (fun e -> e.File = ex.File && e.Block = ex.Block) do
                r[e.Id] <- runInput env e.Input
            blockResults[(ex.File, ex.Block)] <- r
            r)

let private lines (s: string) : string list = clean (List.ofArray (s.Replace("\r", "").Split('\n')))

let private ellipsis = "…"

// строка «…» — любое число (в т. ч. ноль) строк вывода
let rec private matches (expected: string list) (got: string list) : bool =
    match expected, got with
    | [], [] -> true
    | [], _ -> false
    | e :: rest, _ when e = ellipsis -> List.exists (fun k -> matches rest (List.skip k got)) [ 0 .. got.Length ]
    | e :: rest, g :: grest when e = g -> matches rest grest
    | _ -> false

let cases (): seq<obj[]> = allExamples.Value |> Seq.map (fun e -> [| box e.Id |])

[<Theory; MemberData(nameof cases)>]
let ``DOCTEST: пример документации`` (id: string) =
    let ex = allExamples.Value |> List.find (fun e -> e.Id = id)
    let actual = (resultsOf ex).[id]
    let got = lines actual
    let where = sprintf "%s\n  ввод: %s" id ex.Input
    match Map.tryFind (ex.File, ex.Input) knownDefects with
    | Some why ->
        Assert.True(got <> ex.Expected, sprintf "%s\n  дефект «%s» исправлен — уберите запись из knownDefects" where why)
    | None ->
        if ex.Expected.IsEmpty then
            Assert.True(not (actual.StartsWith "ОШИБКА"), sprintf "%s\n  ожидалось выполнение без ошибки, получено: %s" where actual)
        else
            Assert.True(matches ex.Expected got,
                        sprintf "%s\n  ожидалось: %s\n  получено: %s" where (String.Join("\n", ex.Expected)) actual)

[<Fact>]
let ``DOCTEST: примеры найдены`` () =
    // защита от тихого пропуска: формат поменялся — тест красный
    Assert.True(allExamples.Value.Length >= 300, sprintf "найдено примеров: %d" allExamples.Value.Length)
    Assert.Contains(allExamples.Value, fun e -> e.File = "README.md")
