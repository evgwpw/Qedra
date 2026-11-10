// Шаг 21h'': справочник автора библиотеки docs\lisp-library-guide.md не расходится с кодом —
// каждое имя (builtin, спецформа, экспорт модуля) в нём упомянуто, а каждая строка таблиц-справочников называет существующее имя
module LibraryGuideTests

open System
open System.IO
open System.Text.RegularExpressions
open Xunit
open Evaluator

// docs\lisp-library-guide.md: поднимаемся от каталога сборки тестов до корня репозитория (там Lisp.slnx)
let private guideText : Lazy<string> =
    lazy (
        let rec find (dir: DirectoryInfo) =
            if isNull dir then failwith "не найден корень репозитория (Lisp.slnx)"
            elif File.Exists(Path.Combine(dir.FullName, "Lisp.slnx")) then Path.Combine(dir.FullName, "docs", "lisp-library-guide.md")
            else find dir.Parent
        File.ReadAllText(find (DirectoryInfo AppContext.BaseDirectory)))

// Фрагменты `кода` и ``кода`` в строке
let private codeSpans (line: string) : string list =
    [ for m in Regex.Matches(line, "``(.+?)``|`([^`]+)`") ->
        if m.Groups.[1].Success then m.Groups.[1].Value else m.Groups.[2].Value ]

// Слова кода: имена Lisp без скобок, кавычек и знаков препинания
let private words (code: string) : string list =
    [ for m in Regex.Matches(code, @"[^\s()'`"",\[\]]+") -> m.Value ]

// Все имена, которые обязан упомянуть справочник
let private requiredNames () : Set<string> =
    let env = newEnv ()
    let exports = env.Modules.Values |> Seq.collect (fun m -> m.Exports) |> List.ofSeq
    Set.ofList (builtinNames @ specialFormNames @ exports)

// Строки таблиц внутри <!-- ref:begin --> … <!-- ref:end -->: первая ячейка (до «→» — справа от неё пример значения)
let private refFirstCells (text: string) : string list =
    let mutable inside = false
    [ for line in text.Split('\n') do
        let l = line.TrimEnd('\r')
        if l.StartsWith "<!-- ref:begin" then inside <- true
        elif l.StartsWith "<!-- ref:end" then inside <- false
        elif inside && l.StartsWith "| " then
            let cell = l.Split('|').[1]
            let i = cell.IndexOf '→'
            yield (if i >= 0 then cell.Substring(0, i) else cell) ]

// Имя, которое называет фрагмент первой ячейки: голова формы «(имя ...)» или само слово; цитаты 'x и `x — не имена
let private namedBy (span: string) : string option =
    let s = span.Trim()
    if s.StartsWith "'" || s.StartsWith "`" then None
    else words s |> List.tryHead

[<Fact>]
let ``справочник упоминает каждую builtin-функцию, спецформу и экспорт модулей`` () =
    let mentioned =
        guideText.Force().Split('\n') |> Seq.collect codeSpans |> Seq.collect words |> Set.ofSeq
    let fenced =
        Regex.Matches(guideText.Force(), "```lisp(.*?)```", RegexOptions.Singleline)
        |> Seq.collect (fun m -> words m.Groups.[1].Value) |> Set.ofSeq
    let missing = Set.difference (requiredNames ()) (Set.union mentioned fenced)
    Assert.True(missing.IsEmpty, "нет в docs\\lisp-library-guide.md: " + String.Join(" ", missing))

[<Fact>]
let ``строки справочника называют существующие имена`` () =
    let known = requiredNames ()
    let cells = refFirstCells (guideText.Force())
    Assert.True(cells.Length > 100, sprintf "мало строк справочника: %d" cells.Length)
    let unknown =
        cells
        |> List.collect codeSpans
        |> List.choose namedBy
        |> List.filter (fun n -> not (known.Contains n))
        |> List.distinct
    Assert.True(unknown.IsEmpty, "в справочнике есть несуществующие имена: " + String.Join(" ", unknown))

[<Fact>]
let ``match-bindings возвращает привязки`` () =
    let env = newEnv ()
    let run (src: string) = Reader.readAll src |> List.fold (fun _ e -> eval e env) Types.LispNil |> Printer.prettyPrint
    Assert.Equal("((?a 1) (?b 3))", run "(match-bindings '(+ ?a (* ?b x)) '(+ 1 (* 3 x)))")
    Assert.Equal("#f", run "(match-bindings '(sin ?a) '(cos x))")
    Assert.Equal("#f", run "(match-bindings '(+ ?a ?a) '(+ x y))")
    Assert.Equal("()", run "(match-bindings 'x 'x)")
