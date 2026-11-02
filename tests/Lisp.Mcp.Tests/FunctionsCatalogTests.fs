// WASM.3a: каталог функций входного языка (web/app/functions.json) — оракул.
// (1) полнота: каждая функция, описанная в docs/math-language.md, есть в каталоге;
// (2) обратное: в каталоге нет имён, которых нет в документации (каталог не «придуман» и не устарел);
// (3) формат: имя/сигнатура/шаблон с местом ввода ▢/описание ≤ 100 символов/тема;
// (4) примеры из каталога выполняются настольным Lisp.dll в режиме --math без ошибок.
module FunctionsCatalogTests

open System
open System.IO
open System.Text
open System.Text.Json
open System.Text.RegularExpressions
open Xunit
open CliProcess

// корень репозитория: вверх от выходного каталога до Lisp.slnx
let private repoRoot () : string =
    let rec up (d: DirectoryInfo) =
        if isNull d then failwith "не найден корень репозитория (Lisp.slnx)"
        elif File.Exists(Path.Combine(d.FullName, "Lisp.slnx")) then d.FullName
        else up d.Parent
    up (DirectoryInfo AppContext.BaseDirectory)

let private catalogPath () = Path.Combine(repoRoot (), "web", "app", "functions.json")
let private docPath () = Path.Combine(repoRoot (), "docs", "math-language.md")

type Fn =
    { Name: string
      Signature: string
      Template: string
      Summary: string
      Topic: string
      Example: string option }

let private catalog () : Fn list =
    use doc = JsonDocument.Parse(File.ReadAllText(catalogPath ()))
    [ for e in doc.RootElement.EnumerateArray () ->
          { Name = e.GetProperty("name").GetString()
            Signature = e.GetProperty("signature").GetString()
            Template = e.GetProperty("template").GetString()
            Summary = e.GetProperty("summary").GetString()
            Topic = e.GetProperty("topic").GetString()
            Example =
              match e.GetProperty("example") with
              | v when v.ValueKind = JsonValueKind.String -> Some(v.GetString ())
              | _ -> None } ]

// --- независимый разбор документации (каталог строится генератором, здесь — проверка) ---
let private calls = Regex(@"`([A-Za-z][A-Za-z0-9_]*)\(([^`]*)`", RegexOptions.Compiled)
let private row = Regex(@"^\|\s*(.+?)\s*\|\s*(.*?)\s*\|\s*$", RegexOptions.Compiled)
let private head = Regex(@"^#{2,3}\s+(.+?)\s*$", RegexOptions.Compiled)

/// имена функций, описанных в документации: ячейки таблиц и вызовы в тексте
/// (строки с «:=» — примеры определения пользовательской функции, их пропускаем)
let private documented () : (string * string * string) list =
    let lines = File.ReadAllLines(docPath ())
    let mutable topic = ""
    let acc = ResizeArray<string * string * string>()
    let add (first: string) (line: string) =
        if not (line.Contains ":=") then
            for c in calls.Matches first do
                acc.Add((c.Groups.[1].Value, topic, line))
    for line in lines do
        let h = head.Match line
        if h.Success then topic <- h.Groups.[1].Value
        else
            let m = row.Match line
            if m.Success then add m.Groups.[1].Value line
            else add line line
    Seq.distinctBy (fun (n, _, _) -> n) acc |> List.ofSeq

let private isLanguageFunction (name: string) =
    name.Length >= 2 && name <> "f" && name <> "foo"

[<Fact>]
let ``каталог: каждая описанная в руководстве функция присутствует`` () =
    let names = catalog () |> List.map (fun f -> f.Name) |> Set.ofList
    let documented =
        documented () |> List.map (fun (n, _, _) -> n) |> List.filter isLanguageFunction |> List.distinct
    let missing = documented |> List.filter (fun n -> not (names.Contains n))
    Assert.True(List.isEmpty missing, sprintf "нет в каталоге: %s" (String.Join(", ", missing)))

[<Fact>]
let ``каталог: в нём нет имён, которых нет в руководстве`` () =
    let documented = documented () |> List.map (fun (n, _, _) -> n) |> Set.ofList
    let extra = catalog () |> List.map (fun f -> f.Name) |> List.filter (fun n -> not (documented.Contains n))
    Assert.True(List.isEmpty extra, sprintf "описаны мимо документации: %s" (String.Join(", ", extra)))

[<Fact>]
let ``каталог: темы — области из задания, по порядку, «Служебное» последняя`` () =
    // WASM.4b: 15 областей (≤ 18), «Служебное» — всегда последняя; список совпадает с генератором
    let order =
        [ "Арифметика и элементарные функции"; "Алгебра и многочлены"; "Уравнения и неравенства"
          "Пределы"; "Производные и ряды"; "Интегралы"; "Суммы и рекуррентности"; "ОДУ"
          "Линейная алгебра"; "Теория чисел"; "Спецфункции"; "Множества, интервалы, логика"
          "Геометрия и кривые"; "Программирование"; "Служебное" ]
    let topics = catalog () |> List.map (fun f -> f.Topic)
    let distinct = List.distinct topics
    Assert.True(distinct.Length <= 18, sprintf "тем слишком много: %d" distinct.Length)
    let unknown = distinct |> List.filter (fun t -> not (List.contains t order))
    Assert.True(List.isEmpty unknown, sprintf "темы вне списка: %s" (String.Join(", ", unknown)))
    let idx = topics |> List.map (fun t -> List.findIndex ((=) t) order)
    let mutable outOfOrder = false
    for i in 1 .. idx.Length - 1 do
        if idx.[i] < idx.[i - 1] then outOfOrder <- true
    Assert.False(outOfOrder, "темы идут не в заданном порядке")
    Assert.Equal("Служебное", List.last distinct)

[<Fact>]
let ``каталог: в темах и описаниях нет номеров шагов`` () =
    // WASM.4b: «шаг 21l.0», «NT.1», «SFn.2a», «A3′.3», «LA.2», «21l.1» — служебные пометки, в справочнике их нет
    let mark = Regex(@"(шаг[а-я]*\s*\d|\b\d+[a-z]\.\d|\bNT\.\d|\bSFn\.\d|A3′\.\d|\bLA\.\d)", RegexOptions.Compiled)
    let bad = ResizeArray<string> ()
    for f in catalog () do
        let text = f.Topic + " " + f.Summary
        if mark.IsMatch text then bad.Add(sprintf "%s: «%s»" f.Name (mark.Match(text).Value))
    Assert.True((bad.Count = 0), String.Join("; ", bad))

[<Fact>]
let ``каталог: описание стоит в строке, где функция определена, вместе с её сигнатурой`` () =
    // WASM.4b: описание не из соседнего абзаца и не от другой формы вызова:
    // нужна строка руководства, где есть и сигнатура из каталога, и текст описания
    let normalize (s: string) =
        Regex.Replace(s.Replace("**", "").Replace("`", "").Replace("…", "").Replace("*", ""), @"\s+", " ").Trim()
    let squeeze (s: string) = Regex.Replace(s, @"\s+", "")
    let lines = File.ReadAllLines(docPath ())
    let bad = ResizeArray<string> ()
    for f in catalog () do
        let sigKey = squeeze f.Signature
        let summary = normalize f.Summary
        let probe = if summary.Length > 40 then summary.Substring(0, 40) else summary
        let ok = lines |> Array.exists (fun line -> (squeeze line).Contains sigKey && (normalize line).Contains probe)
        if not ok then bad.Add(sprintf "%s: «%s»" f.Signature probe)
    Assert.True((bad.Count = 0), String.Join("; ", bad))

[<Fact>]
let ``каталог: поля заполнены и имеют допустимый вид`` () =
    let bad = ResizeArray<string> ()
    for f in catalog () do
        if not (Regex.IsMatch(f.Name, "^[A-Za-z][A-Za-z0-9_]*$")) then bad.Add(sprintf "%s: имя" f.Name)
        if not (f.Signature.StartsWith(f.Name + "(")) then bad.Add(sprintf "%s: сигнатура %s" f.Name f.Signature)
        if not (f.Template.Contains "▢") then bad.Add(sprintf "%s: шаблон без места ввода" f.Name)
        if f.Summary.Trim().Length = 0 then bad.Add(sprintf "%s: пустое описание" f.Name)
        if f.Summary.Length > 100 then bad.Add(sprintf "%s: описание длиннее 100" f.Name)
        if f.Topic.Trim().Length = 0 then bad.Add(sprintf "%s: нет темы" f.Name)
    Assert.True((bad.Count = 0), String.Join("; ", bad))

[<Fact>]
let ``каталог: описания взяты из руководства, а не придуманы`` () =
    // нормализация как в генераторе: без разметки, без многоточия, одиночные пробелы
    let normalize (s: string) =
        Regex.Replace(s.Replace("**", "").Replace("`", "").Replace("…", "").Replace("*", ""), @"\s+", " ").Trim()
    let text = normalize (File.ReadAllText(docPath ()).Replace("\n", " "))
    let bad =
        [ for f in catalog () do
              let summary = normalize f.Summary
              let probe = if summary.Length > 40 then summary.Substring(0, 40) else summary
              if not (text.Contains probe) then yield sprintf "%s: «%s»" f.Name probe ]
    Assert.True(List.isEmpty bad, String.Join("; ", bad))

[<Fact>]
[<Trait("Category", "Slow")>]   // 50 примеров × отдельный процесс ≈ 25 с
let ``каталог: примеры выполняются в режиме --math без ошибок`` () =
    let examples = catalog () |> List.choose (fun f -> f.Example)
    Assert.True(examples.Length > 20, sprintf "примеров слишком мало: %d" examples.Length)
    // каждый пример — отдельный процесс: иначе примеры делят состояние (переменные, функции)
    let bad =
        [ for ex in examples do
              let code, out, err = runLisp [ "--math"; "-e"; ex ]
              if code <> 0 || out.Contains "ОШИБКА" then
                  yield sprintf "%s → код %d: %s" ex code ((out + err).Trim()) ]
    Assert.True(List.isEmpty bad, String.Join("; ", List.truncate 5 bad))
