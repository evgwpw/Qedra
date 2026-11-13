// Шаг ML.AUDIT: сверка docs/mathlang-not-exposed.txt со справочником docs/lisp-library-guide.md.
// Правило доступности — то же, что в research/mathlang/audit.mjs (скрипт генерирует файл): имя функции справочника
// читается читателем входного языка и разрешается интерпретатором как m-alias, m-kind elem/form, Lisp-функция с тем же
// именем (fbound?, с учётом m-rename) либо совпадает с именем языка из m-aliases/m-renames после приведения `_` ↔ `-`.
// Тест ловит два расхождения: функция справочника не доступна в --math и не перечислена в файле; запись файла
// ничего не исключает (имя стало доступным — запись надо убрать, иначе список «врёт»).
module MathLangAuditTests

open System
open System.IO
open System.Text
open System.Text.RegularExpressions
open Xunit
open Types
open Evaluator

let private repoRoot : Lazy<string> =
    lazy (
        let rec find (dir: DirectoryInfo) =
            if isNull dir then failwith "не найден корень репозитория (Lisp.slnx)"
            elif File.Exists(Path.Combine(dir.FullName, "Lisp.slnx")) then dir.FullName
            else find dir.Parent
        find (DirectoryInfo AppContext.BaseDirectory))

let private readText (rel: string) : string =
    File.ReadAllText(Path.Combine(repoRoot.Value, rel)).Replace("\r\n", "\n")

// ---------- справочник: функции по разделам (те же правила, что в audit.mjs) ----------
let private guideFunctions () : (string * string) list =
    let nameRe = Regex(@"^[A-Za-z][A-Za-z0-9_?!<>+*/-]*$")
    let skip =
        Regex(@"^(Как пользоваться|Обзор|Правила)|^[0-9]+\.\s*(Быстрый старт|Соглашения|Мост|Контракт алгоритмов|Тестирование|Отладка)")
    let acc = ResizeArray<string * string>()
    let mutable title = ""
    let mutable inTable = false
    for line in (readText "docs/lisp-library-guide.md").Split('\n') do
        let h = Regex.Match(line, @"^(#{2,3})\s+(.+)$")
        if h.Success then
            title <- h.Groups.[2].Value.Trim()
            inTable <- false
        elif line.StartsWith "|" then
            if Regex.IsMatch(line, @"^\|\s*-+") then inTable <- true
            elif inTable && not (skip.IsMatch title) then
                let cells = line.Split('|')
                let cell = if cells.Length > 1 then cells.[1] else ""
                for m in Regex.Matches(cell, "`([^`]+)`") do
                    let tok = Regex.Match(m.Groups.[1].Value.Trim(), @"^\(?([^\s()`,'""]+)")
                    if tok.Success && nameRe.IsMatch tok.Groups.[1].Value then
                        acc.Add(tok.Groups.[1].Value, title)
    List.ofSeq acc

// ---------- статус имени во входном языке: спрашиваем интерпретатор ----------
let private mathStatuses (names: string list) : Map<string, string> =
    let quoted = names |> List.map (fun n -> "\"" + n + "\"") |> String.concat " "
    let src =
        String.Join("\n", [|
            "(define (ml-status n)"
            "  (let* ((e (try (math-read n) (lambda (err) #f)))"
            "         (s (and (symbol? e) e))"
            "         (fn (try (fbound? (string->symbol n)) (lambda (err) #f))))"
            "    (cond ((and s (not (null? (get s 'm-alias)))) 'alias)"
            "          ((and s (equal? (get s 'm-kind) 'elem)) 'elem)"
            "          ((and s (not (null? (get s 'm-kind)))) 'form)"
            "          ((and s (try (fbound? (let ((r (get s 'm-rename))) (if (null? r) s r))) (lambda (err) #f))) 'fbound)"
            "          (fn 'lisp-name)"
            "          (else 'value))))"
            $"(map (lambda (n) (list n (ml-status n))) (list {quoted}))"
        |])
    let file = Path.Combine(Path.GetTempPath(), "mathlang-audit-" + Guid.NewGuid().ToString("N") + ".lisp")
    File.WriteAllText(file, src, UTF8Encoding(false))
    try
        let env = newEnv ()
        let res = loadIntoEnv file env
        let pair (v: LispValue) =
            match v with
            | LispList [ LispStr n; LispSym s ] -> Some(n, s)
            | _ -> None
        match res with
        | LispList items -> items |> List.choose pair |> Map.ofList
        | _ -> failwith "проба статусов вернула не список"
    finally File.Delete file

// ---------- таблицы сопоставления m-aliases / m-renames из runtime.lisp ----------
let private runtimePairs (head: string) : (string * string) list =
    let src = Regex.Replace(readText "lib/mathlang/runtime.lisp", @";[^\n]*", "")
    let start = src.IndexOf head
    let mutable depth = 0
    let mutable i = start + head.Length - 1
    let mutable stop = -1
    while i < src.Length && stop < 0 do
        if src.[i] = '(' then depth <- depth + 1
        elif src.[i] = ')' then
            depth <- depth - 1
            if depth = 0 then stop <- i
        i <- i + 1
    let body = src.Substring(start, stop - start + 1)
    [ for m in Regex.Matches(body, @"\(([A-Za-z_][A-Za-z0-9_]*)\s+([A-Za-z_][A-Za-z0-9_*?!<>=-]*)\)") do
        if m.Groups.[1].Value <> "define" then yield m.Groups.[1].Value, m.Groups.[2].Value ]

let private canon (n: string) = n.ToLowerInvariant().Replace('_', '-')

// канонические имена, которые во входном языке называются иначе (fourier-series ↔ fourier_series)
let private aliasedLisp () : Set<string> =
    let pairs = runtimePairs "(define m-aliases '(" @ runtimePairs "(define m-renames '("
    let s = ResizeArray<string>()
    for (mname, lisp) in pairs do
        s.Add(canon mname)
        s.Add(canon lisp)
        for pre in [ "m-"; "math-" ] do
            if lisp.StartsWith pre then s.Add(canon (lisp.Substring pre.Length))
    Set.ofSeq s


// ---------- docs/mathlang-not-exposed.txt ----------
type Entry = { Section: string; Status: string; Pattern: string; Prefix: bool }

let private readNotExposed () : Entry list =
    let head = Regex(@"^\[(.+);\s*(missing|internal|lisp-only)\]\s*(.*)$")
    let acc = ResizeArray<Entry>()
    let mutable section = ""
    let mutable status = ""
    for line in (readText "docs/mathlang-not-exposed.txt").Split('\n') do
        let l = line.Trim()
        let h = head.Match l
        if h.Success then
            section <- h.Groups.[1].Value
            status <- h.Groups.[2].Value
        elif l <> "" && not (l.StartsWith "#") then
            for tok in l.Split([| ' '; '\t' |], StringSplitOptions.RemoveEmptyEntries) do
                let pref = tok.EndsWith "*"
                acc.Add({ Section = section; Status = status
                          Pattern = (if pref then tok.Substring(0, tok.Length - 1) else tok); Prefix = pref })
    List.ofSeq acc

let private matches (e: Entry) (name: string) = if e.Prefix then name.StartsWith e.Pattern else name = e.Pattern

[<Fact>]
let ``каждая функция справочника доступна в --math или перечислена в docs/mathlang-not-exposed.txt`` () =
    let funcs = guideFunctions () |> List.map fst |> List.distinct
    let status = mathStatuses funcs
    let exposedMath = set [ "alias"; "elem"; "form"; "fbound" ]
    let aliased = aliasedLisp ()
    let exposed (n: string) =
        match Map.tryFind n status with
        | Some s -> exposedMath.Contains s || aliased.Contains(canon n)
        | None -> false
    // значения и константы (naturals, #t, имена единиц) — не функции: их статус value
    let isFunction (n: string) = match Map.tryFind n status with Some "value" | None -> false | _ -> true
    let functions = funcs |> List.filter isFunction
    let notExposed = functions |> List.filter (exposed >> not)
    let entries = readNotExposed ()
    let listed n = entries |> List.exists (fun e -> matches e n)
    let missing = notExposed |> List.filter (not << listed)
    Assert.True(missing.IsEmpty,
                "не доступны в --math и не перечислены в docs/mathlang-not-exposed.txt: " + String.Join(" ", missing))
    // обратное направление: каждая запись должна что-то исключать (существовать в справочнике и быть не доступной)
    let all = Set.ofList functions
    let stale =
        entries
        |> List.filter (fun e -> not (all |> Set.exists (matches e)) || not (notExposed |> List.exists (matches e)))
        |> List.map (fun e -> if e.Prefix then e.Pattern + "*" else e.Pattern)
        |> List.distinct
    Assert.True(stale.IsEmpty,
                "записи docs/mathlang-not-exposed.txt ничего не исключают (имя стало доступным или исчезло из справочника): "
                + String.Join(" ", stale))

