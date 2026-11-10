// Шаг GD.1–GD.2: справка для LLM по запросу — короткое ядро (docs\guide\core.md), карточки тем (docs\guide\topics\<имя>.md)
// и таблица синонимов (docs\guide\synonyms.md). Файлы встроены в сборку (EmbeddedResource, см. Lisp.Host.fsproj);
// используются инструментом MCP guide(topic), ресурсом lisp://guide и ключом --guide.
module Guide

open System
open System.IO
open System.Text
open System.Text.RegularExpressions

let private readResource (name: string) : string option =
    let asm = Reflection.Assembly.GetExecutingAssembly()
    match asm.GetManifestResourceNames() |> Array.tryFind (fun n -> n.Replace('\\', '/') = name) with
    | None -> None
    | Some n ->
        use s = asm.GetManifestResourceStream n
        use r = new StreamReader(s, Encoding.UTF8)
        Some (r.ReadToEnd())

// Ядро справки (без списка тем, который добавляет text)
let core : string =
    defaultArg (readResource "guide/core.md") "guide/core.md is not embedded"

// Имена тем-карточек (по именам встроенных файлов), по алфавиту
let topics : string list =
    Reflection.Assembly.GetExecutingAssembly().GetManifestResourceNames()
    |> Array.map (fun n -> n.Replace('\\', '/'))
    |> Array.filter (fun n -> n.StartsWith "guide/topics/" && n.EndsWith ".md")
    |> Array.map (fun n -> n.Substring("guide/topics/".Length, n.Length - "guide/topics/".Length - 3))
    |> Array.sort
    |> List.ofArray

// Карточка темы (точное имя)
let card (topic: string) : string option = readResource ("guide/topics/" + topic + ".md")

// Шаг GD.2: таблица синонимов — имена других систем (Mathematica, Maple) и инструментов → тема
let synonymsText : string =
    defaultArg (readResource "guide/synonyms.md") "guide/synonyms.md is not embedded"

// Имя (в нижнем регистре) → тема. Строки таблицы: | `имя`, `имя` | чем вызвать | `тема` |; первое вхождение имени главнее
let synonyms : Map<string, string> =
    let backticked (cell: string) = [ for m in Regex.Matches(cell, "`([^`]+)`") -> m.Groups.[1].Value ]
    synonymsText.Replace("\r", "").Split('\n')
    |> Array.filter (fun l -> l.StartsWith "| `")
    |> Array.collect (fun l ->
        let cells = l.Split('|') // "", имена, чем вызвать, тема, ""
        if cells.Length < 5 then [||]
        else
            match backticked cells.[3] with
            | [ topic ] -> backticked cells.[1] |> List.map (fun n -> n.ToLowerInvariant(), topic) |> Array.ofList
            | _ -> [||])
    |> Array.fold (fun m (n, t) -> if Map.containsKey n m then m else Map.add n t m) Map.empty

// Темы для показа: карточки и таблица синонимов
let allTopics : string list = topics @ [ "synonyms" ]

let private topicList () = String.Join(", ", allTopics)

// Подсказки «возможно, вы имели в виду»: близкие по расстоянию редактирования или вложенные имена
let suggestions (name: string) : string list =
    let q = name.ToLowerInvariant()
    allTopics
    |> List.map (fun t -> t, Checker.editDistance q t)
    |> List.filter (fun (t, d) -> d <= 3 || t.Contains q || q.Contains t)
    |> List.sortBy (fun (t, d) -> d, t)
    |> List.truncate 3
    |> List.map fst

// Тема по имени: имя карточки, «synonyms» или синоним (регистр не важен); None — неизвестно
let resolve (name: string) : string option =
    let t = name.Trim().ToLowerInvariant()
    if List.contains t allTopics then Some t else Map.tryFind t synonyms

// guide(topic): None или пусто — ядро + список тем; тема или синоним — карточка (synonyms — таблица); иначе Error с подсказками
let text (topic: string option) : Result<string, string> =
    match topic |> Option.map (fun t -> t.Trim().ToLowerInvariant()) with
    | None | Some "" -> Ok (core.TrimEnd() + "\n\nAvailable topics (call guide with topic=NAME): " + topicList () + "\n")
    | Some t ->
        match resolve t with
        | Some "synonyms" -> Ok synonymsText
        | Some r when (card r).IsSome -> Ok (card r).Value
        | _ ->
            let sg = suggestions t
            let did = if sg.IsEmpty then "" else " Did you mean: " + String.Join(", ", sg) + "?"
            Error ($"Unknown topic '{t}'.{did} Available topics: {topicList ()}")
