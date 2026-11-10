// Запросы к коду (Lisp.exe --query и MCP-инструмент code): тонкая обёртка над CodeIndex (Lisp.Core)
module QueryCli

open System
open Types

let private isBuiltinCell (c: Cell) =
    not (isNull (box c)) && (match c.Value with LispBuiltin _ -> true | _ -> false)

// Общее окружение для определения «builtin» (создаётся один раз, если хост не передал своё)
let private defaultEnv : Lazy<Env> = lazy (Evaluator.newEnv ())

/// Выполнить запрос: (текст или JSON, успех). env — окружение с prelude (для имён builtin).
let runCode (env: Env) (kind: string) (arg: string) (json: bool) (noBody: bool) (depth: int)
            (root: string option) (files: string list) : string * bool =
    let extra =
        match kind.ToLowerInvariant() with
        | ("outline" | "deps") when not (String.IsNullOrWhiteSpace arg) && IO.File.Exists arg -> arg :: files
        | _ -> files
    let idx = CodeIndex.getIndex root extra (match kind.ToLowerInvariant() with "refs" | "callers" | "unused" -> true | _ -> false)
    idx.IsBuiltin <- (fun n -> isBuiltinCell (env.TryBound n))
    idx.BuiltinNames <- (fun () -> env.OwnCells |> Seq.filter isBuiltinCell |> Seq.map (fun c -> c.Name) |> Seq.toArray :> seq<string>)
    CodeIndex.run idx kind arg { Json = json; NoBody = noBody; Depth = depth }

/// Для MCP: окружение по умолчанию
let runCodeDefault (kind: string) (arg: string) (json: bool) (noBody: bool) (depth: int) : string * bool =
    runCode (defaultEnv.Force()) kind arg json noBody depth None []

let usage =
    "Lisp --query <вид> <аргумент> [--json] [--no-body] [--depth N] [--root DIR] [--file F]...\n"
    + "виды: def NAME | sig NAME | refs NAME | callers NAME | callees NAME | module NAME | outline FILE | search ТЕКСТ | deps FILE | unused"

/// argv — аргументы командной строки целиком (содержат --query). Код выхода: 0 — найдено, 1 — нет такого, 2 — ошибка запроса.
let runCli (env: Env) (argv: string[]) : int =
    let mutable json = false
    let mutable noBody = false
    let mutable depth = 1
    let mutable root : string option = None
    let files = Collections.Generic.List<string>()
    let pos = Collections.Generic.List<string>()
    let mutable i = 0
    while i < argv.Length do
        match argv.[i] with
        | "--query" -> ()
        | "--json" -> json <- true
        | "--no-body" -> noBody <- true
        | "--depth" when i + 1 < argv.Length ->
            (match Int32.TryParse argv.[i + 1] with
             | true, d -> depth <- max 1 d
             | _ -> ())
            i <- i + 1
        | "--root" when i + 1 < argv.Length ->
            root <- Some argv.[i + 1]
            i <- i + 1
        | "--file" when i + 1 < argv.Length ->
            files.Add argv.[i + 1]
            i <- i + 1
        | a -> pos.Add a
        i <- i + 1
    if pos.Count = 0 then
        Console.WriteLine usage
        2
    else
        let kind = pos.[0]
        let arg = String.Join(" ", pos |> Seq.skip 1)
        let text, ok = runCode env kind arg json noBody depth root (List.ofSeq files)
        Console.WriteLine text
        if ok then 0 else 1
