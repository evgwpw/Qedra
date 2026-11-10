// Статический проверщик файлов Lisp (Lisp.exe --check): код НЕ выполняется.
// CHK.1 — чтение: скобки (с эвристикой по отступам, где вероятно не хватает «)»), лишняя «)», незакрытая строка,
// неверный синтаксис; после ошибки чтение продолжается (повторная синхронизация на «(» в первом столбце).
module Checker

open System
open System.Collections.Generic
open System.Numerics
open System.Text
open Types

type Severity =
    | SevError
    | SevWarning

// позиция: строка и столбец (с 1)
type P = { L: int; C: int }

type Diag =
    { File: string
      Line: int
      Col: int
      Severity: Severity
      Code: string
      Message: string }

// Дерево чтения с позициями. Кавычка ' ` , ,@ — обычный список (quote x) с позицией знака
type Node =
    | Sym of string * P
    | Num of string * P
    | Str of string * P
    | Bool of bool * P
    | Lst of Node list * P * P      // элементы, позиция «(», позиция «)»
    | Vec of Node list * P          // #( ... )

let posOf (n: Node) : P =
    match n with
    | Sym (_, p) | Num (_, p) | Str (_, p) | Bool (_, p) -> p
    | Lst (_, p, _) -> p
    | Vec (_, p) -> p

let private isNumberToken (t: string) : bool =
    let isInt (s: string) = fst (BigInteger.TryParse s)
    match t.Split('/') with
    | [| a; b |] when isInt a && isInt b && BigInteger.Parse b <> 0I -> true
    | _ ->
        (t.IndexOfAny [| '.'; 'e'; 'E' |] >= 0
         && fst (Double.TryParse(t, Globalization.NumberStyles.Float, Globalization.CultureInfo.InvariantCulture)))
        || isInt t

type private Frame(openPos: P, indent: int, isVec: bool) =
    member _.Open = openPos
    member _.Indent = indent          // столбец первого токена строки, где открыта скобка
    member _.IsVec = isVec
    member val Items = List<Node>()
    member val Pending = Stack<string * P>()   // знаки кавычек, ждущие выражения
    member val Suspect = 0 with get, set       // строка, на которой отступ «не глубже» этой формы (0 — нет)
    member val SuspectPrev = { L = 1; C = 1 } with get, set   // конец последнего токена перед той строкой

type private LexState =
    { mutable I: int
      mutable Line: int
      mutable Ls: int            // индекс начала строки
      mutable TokLine: int       // строка последнего начатого токена
      mutable PrevEnd: P }       // позиция сразу за последним токеном

// Чтение текста: формы (только полностью прочитанные) и диагностика чтения
let parseSource (file: string) (text: string) : Node list * Diag list =
    let diags = List<Diag>()
    let err (p: P) (code: string) (msg: string) =
        diags.Add { File = file; Line = p.L; Col = p.C; Severity = SevError; Code = code; Message = msg }
    let root = Frame({ L = 0; C = 0 }, 0, false)
    let stack = List<Frame>()
    stack.Add root
    let n = text.Length
    let st = { I = 0; Line = 1; Ls = 0; TokLine = 0; PrevEnd = { L = 1; C = 1 } }
    let cur () = stack.[stack.Count - 1]
    let rec complete (fr: Frame) (node: Node) =
        if fr.Pending.Count > 0 then
            let (name, p) = fr.Pending.Pop()
            complete fr (Lst([ Sym(name, p); node ], p, p))
        else fr.Items.Add node
    let here () = { L = st.Line; C = st.I - st.Ls + 1 }
    // отметить формы, у которых строка начинается «не глубже» их строки открытия
    let mark (col: int) =
        for k in 1 .. stack.Count - 1 do
            let f = stack.[k]
            if f.Suspect = 0 && f.Indent >= col then
                f.Suspect <- st.Line
                f.SuspectPrev <- st.PrevEnd
    // сообщение о незакрытых формах (кадры 1..); кадры снимаются
    let flush (eof: bool) =
        if stack.Count > 1 then
            let frames = [| for k in 1 .. stack.Count - 1 -> stack.[k] |]
            let inner = frames.[frames.Length - 1]
            let top = frames.[0]
            for f in frames do
                if f.Pending.Count > 0 then
                    err (snd (f.Pending.Peek())) "dangling-quote" "кавычка без выражения"
            let opener (f: Frame) = if f.IsVec then "#(" else "("
            err inner.Open "unclosed-paren"
                (if frames.Length = 1 then sprintf "не закрыта «%s»" (opener inner)
                 else sprintf "не закрыта «%s» (самая внутренняя из %d незакрытых)" (opener inner) frames.Length)
            let marked = frames |> Array.filter (fun f -> f.Suspect > 0)
            if marked.Length > 0 then
                let s = marked |> Array.map (fun f -> f.Suspect) |> Array.min
                let cnt = marked |> Array.filter (fun f -> f.Suspect = s) |> Array.length
                let at = (marked |> Array.find (fun f -> f.Suspect = s)).SuspectPrev
                err at "missing-paren"
                    (sprintf "вероятно, здесь не хватает %d «)»: строка %d начинается не глубже открытой формы; форма верхнего уровня начинается в %d:%d"
                        cnt s top.Open.L top.Open.C)
            else
                err st.PrevEnd "missing-paren"
                    (sprintf "конец файла: не закрыто %d «(»; форма верхнего уровня начинается в %d:%d"
                        frames.Length top.Open.L top.Open.C)
            stack.RemoveRange(1, stack.Count - 1)
    while st.I < n do
        let c = text.[st.I]
        if c = '\n' then
            st.I <- st.I + 1
            st.Line <- st.Line + 1
            st.Ls <- st.I
        elif Char.IsWhiteSpace c then st.I <- st.I + 1
        elif c = ';' then
            while st.I < n && text.[st.I] <> '\n' do st.I <- st.I + 1
        else
            let p = here ()
            let first = st.TokLine <> st.Line
            // отступ строки для форм, открытых далее на той же строке — столбец первого токена строки
            let lineIndent =
                if first then p.C
                else
                    // столбец первого непробельного знака строки
                    let mutable k = st.Ls
                    while k < n && (text.[k] = ' ' || text.[k] = '\t') do k <- k + 1
                    k - st.Ls + 1
            st.TokLine <- st.Line
            if first && c <> ')' then mark p.C
            let isVecOpen = (c = '#' && st.I + 1 < n && text.[st.I + 1] = '(')
            if c = '(' || isVecOpen then
                if first && p.C = 1 && stack.Count > 1 then flush false
                st.I <- st.I + (if isVecOpen then 2 else 1)
                stack.Add(Frame(p, lineIndent, isVecOpen))
                st.PrevEnd <- here ()
            elif c = ')' then
                st.I <- st.I + 1
                st.PrevEnd <- here ()
                if stack.Count = 1 then err p "extra-paren" "лишняя «)»"
                else
                    let fr = stack.[stack.Count - 1]
                    stack.RemoveAt(stack.Count - 1)
                    if fr.Pending.Count > 0 then
                        err (snd (fr.Pending.Peek())) "dangling-quote" "кавычка без выражения (перед «)»)"
                    let items = List.ofSeq fr.Items
                    let dots = items |> List.indexed |> List.filter (fun (_, x) -> match x with Sym (".", _) -> true | _ -> false)
                    match dots with
                    | [] -> ()
                    | [ (k, _) ] when k >= 1 && k = items.Length - 2 -> ()
                    | (_, d) :: _ -> err (posOf d) "bad-dot" "неверная точечная запись: после «.» ожидается ровно одно выражение"
                    let node = if fr.IsVec then Vec(items, fr.Open) else Lst(items, fr.Open, p)
                    complete (cur ()) node
            elif c = '\'' || c = '`' then
                st.I <- st.I + 1
                (cur ()).Pending.Push((if c = '\'' then "quote" else "quasiquote"), p)
                st.PrevEnd <- here ()
            elif c = ',' then
                let splice = st.I + 1 < n && text.[st.I + 1] = '@'
                st.I <- st.I + (if splice then 2 else 1)
                (cur ()).Pending.Push((if splice then "unquote-splicing" else "unquote"), p)
                st.PrevEnd <- here ()
            elif c = '"' then
                let startI = st.I
                st.I <- st.I + 1
                let sb = StringBuilder()
                let mutable closed = false
                while not closed && st.I < n do
                    let ch = text.[st.I]
                    if ch = '\\' && st.I + 1 < n then
                        if text.[st.I + 1] = '\n' then
                            st.Line <- st.Line + 1
                            st.Ls <- st.I + 2
                        sb.Append(text.[st.I + 1]) |> ignore
                        st.I <- st.I + 2
                    elif ch = '"' then
                        closed <- true
                        st.I <- st.I + 1
                    else
                        if ch = '\n' then
                            st.Line <- st.Line + 1
                            st.Ls <- st.I + 1
                        sb.Append ch |> ignore
                        st.I <- st.I + 1
                st.TokLine <- st.Line
                if closed then
                    st.PrevEnd <- here ()
                    complete (cur ()) (Str(sb.ToString(), p))
                else
                    err p "unterminated-string" "не закрыт строковый литерал"
                    // синхронизация: следующая строка, начинающаяся с «(» в первом столбце
                    stack.RemoveRange(1, stack.Count - 1)
                    let idx = text.IndexOf("\n(", startI, StringComparison.Ordinal)
                    if idx < 0 then st.I <- n
                    else
                        st.I <- idx
                        st.Line <- 1 + (text.Substring(0, idx) |> Seq.filter ((=) '\n') |> Seq.length)
                        st.Ls <- (if idx = 0 then 0 else text.LastIndexOf('\n', idx - 1) + 1)
                        st.TokLine <- 0
            else
                let start = st.I
                while st.I < n
                      && not (Char.IsWhiteSpace text.[st.I])
                      && text.[st.I] <> '(' && text.[st.I] <> ')'
                      && text.[st.I] <> '"' && text.[st.I] <> ';' do
                    st.I <- st.I + 1
                let token = text.Substring(start, st.I - start)
                st.PrevEnd <- here ()
                let node =
                    if token = "#t" then Bool(true, p)
                    elif token = "#f" then Bool(false, p)
                    elif token.StartsWith "#" then
                        err p "bad-syntax" (sprintf "неизвестный синтаксис «%s»: допустимы #t, #f, #( … ) (литералов символов #\\a нет)" token)
                        Sym(token, p)
                    elif isNumberToken token then Num(token, p)
                    else Sym(token, p)
                complete (cur ()) node
    // конец текста
    if stack.Count > 1 then flush true
    if root.Pending.Count > 0 then
        err (snd (root.Pending.Peek())) "dangling-quote" "кавычка без выражения"
    List.ofSeq root.Items, List.ofSeq diags

// ---------- вывод ----------

let severityName (s: Severity) = match s with SevError -> "ошибка" | SevWarning -> "предупреждение"

let formatDiag (d: Diag) : string =
    sprintf "%s:%d:%d: %s: %s" d.File d.Line d.Col (severityName d.Severity) d.Message

let private jsonStr (s: string) : string =
    let sb = StringBuilder("\"")
    for ch in s do
        match ch with
        | '"' -> sb.Append "\\\"" |> ignore
        | '\\' -> sb.Append "\\\\" |> ignore
        | '\n' -> sb.Append "\\n" |> ignore
        | '\r' -> sb.Append "\\r" |> ignore
        | '\t' -> sb.Append "\\t" |> ignore
        | c when c < ' ' -> sb.AppendFormat("\\u{0:x4}", int c) |> ignore
        | c -> sb.Append c |> ignore
    sb.Append('"').ToString()

let formatJson (ds: Diag list) : string =
    let item (d: Diag) =
        sprintf "{\"file\":%s,\"line\":%d,\"col\":%d,\"severity\":%s,\"code\":%s,\"message\":%s}"
            (jsonStr d.File) d.Line d.Col
            (jsonStr (match d.Severity with SevError -> "error" | SevWarning -> "warning"))
            (jsonStr d.Code) (jsonStr d.Message)
    "[" + String.Join(",", ds |> List.map item) + "]"

let fileNotFound (file: string) : Diag =
    { File = file; Line = 1; Col = 1; Severity = SevError; Code = "file-not-found"; Message = "файл не найден" }

// ---------- CHK.2: статические проверки ----------
// Код пользователя не выполняется. Знание о глобальных именах — из окружения с загруженным prelude (builtins, функции и
// макросы библиотеки), плюс экспорты ВСЕХ модулей lib\ (не только загруженных prelude) и имена, определённые в файле.
// Арность: для функций файла и функций библиотеки (по списку параметров) точная; для builtin — только небольшая ручная
// таблица (в таблице builtin арность не записана); остальные builtin не проверяются.

// Прочитанный lib\: экспорты, макросы, определения по модулям (для файлов из нескольких частей одного модуля)
type private LibInfo =
    { Exports: HashSet<string>
      Macros: HashSet<string>
      Modules: HashSet<string>
      DefsByModule: Dictionary<string, HashSet<string>> }

let private isSymNamed (s: string) (n: Node) = match n with Sym (x, _) -> x = s | _ -> false

// Имена, определяемые формами (define, defmacro, defmemo; внутри begin — тоже)
let rec private definedIn (forms: Node list) : string list =
    forms |> List.collect (fun f ->
        match f with
        | Lst (Sym ("define", _) :: Sym (n, _) :: _, _, _)
        | Lst (Sym ("define", _) :: Lst (Sym (n, _) :: _, _, _) :: _, _, _)
        | Lst (Sym ("defmacro", _) :: Lst (Sym (n, _) :: _, _, _) :: _, _, _)
        | Lst (Sym ("defmemo", _) :: Lst (Sym (n, _) :: _, _, _) :: _, _, _) -> [ n ]
        | Lst (Sym ("begin", _) :: inner, _, _) -> definedIn inner
        | _ -> [])

let private moduleHeader (forms: Node list) : (string * (string * P) list) option =
    match forms with
    | Lst (Sym ("module", _) :: Sym (name, _) :: opts, _, _) :: _ ->
        let exports =
            opts |> List.collect (fun o ->
                match o with
                | Lst (Sym ("export", _) :: names, _, _) ->
                    names |> List.choose (function Sym (s, p) -> Some (s, p) | _ -> None)
                | _ -> [])
        Some (name, exports)
    | _ -> None

let private macroNamesIn (forms: Node list) : string list =
    let rec go (forms: Node list) =
        forms |> List.collect (fun f ->
            match f with
            | Lst (Sym ("defmacro", _) :: Lst (Sym (n, _) :: _, _, _) :: _, _, _) -> [ n ]
            | Lst (Sym ("begin", _) :: inner, _, _) -> go inner
            | _ -> [])
    go forms

let private libInfo : Lazy<LibInfo> =
    lazy (
        let info =
            { Exports = HashSet<string>(); Macros = HashSet<string>(); Modules = HashSet<string>()
              DefsByModule = Dictionary<string, HashSet<string>>() }
        let dir = IO.Path.Combine(AppContext.BaseDirectory, "lib")
        if IO.Directory.Exists dir then
            for f in IO.Directory.GetFiles(dir, "*.lisp", IO.SearchOption.AllDirectories) do
                let forms, _ = parseSource f (IO.File.ReadAllText f)
                for m in macroNamesIn forms do info.Macros.Add m |> ignore
                match moduleHeader forms with
                | Some (name, exports) ->
                    info.Modules.Add name |> ignore
                    for (e, _) in exports do info.Exports.Add e |> ignore
                    if not (info.DefsByModule.ContainsKey name) then info.DefsByModule.[name] <- HashSet<string>()
                    for d in definedIn forms do info.DefsByModule.[name].Add d |> ignore
                | None -> ()
        info)

// Подсказки для частых «чужих» имён (показываются, только если имя действительно неизвестно)
let private hints : IDictionary<string, string> =
    dict [
        "print", "нет такой функции; вывод — display и newline"
        "println", "нет такой функции; вывод — display и newline"
        "write", "нет такой функции; вывод — display и newline"
        "expt", "нет expt; степень — ^"
        "fold", "нет fold; есть foldl (f получает (acc x))"
        "foldr", "нет foldr; есть foldl (f получает (acc x))"
        "reduce", "нет reduce; есть foldl (f получает (acc x))"
        "member", "нет member; есть member? (x список)"
        "memq", "нет memq; есть member?"
        "assq", "нет assq; есть assoc"
        "first", "нет first; есть car"
        "second", "нет second; есть cadr"
        "rest", "нет rest; есть cdr"
        "list-ref", "нет list-ref; есть (nth список индекс)"
        "list-tail", "нет list-tail; есть (drop список n)"
        "iota", "нет iota; есть (range n)"
        "remove", "нет remove; используйте filter с отрицанием"
        "delete", "нет delete; используйте filter с отрицанием"
        "flatten", "нет flatten"
        "zip", "нет zip; для двух списков — map2"
        "count-if", "нет count-if; (length (filter p l))"
        "void", "нет void; значение «ничего» — (begin)"
        "float", "нет float; численное значение — eval-num"
        "to-float", "нет to-float; численное значение — eval-num"
        "exact", "нет exact; точные числа получаются без float"
        "inexact", "нет inexact; численное значение — eval-num"
        "nil", "символа nil нет; пустой список — '()"
        "eq?", "нет eq?; используйте equal?"
        "eqv?", "нет eqv?; используйте equal?"
        "call/cc", "продолжений нет; нелокальный выход — raise и try"
        "call-with-current-continuation", "продолжений нет; нелокальный выход — raise и try"
        "1+", "нет 1+; пишите (+ x 1)"
        "1-", "нет 1-; пишите (- x 1)"
        "numerator", "нет numerator; есть numer"
        "denominator", "нет denominator; есть denom"
        "pi", "pi — символ: в коде пишите 'pi (с кавычкой)"
        "%i", "%i — символ: в коде пишите '%i (с кавычкой)"
        "else", "else допустим только как последняя ветка cond/case"
        "=>", "=> в cond не поддерживается" ]

// Ручная таблица арности builtin (мин, макс; макс = -1 — любое число). Только то, в чём уверены
let private builtinArity : IDictionary<string, int * int> =
    dict [
        for n in [ "car"; "cdr"; "cadr"; "cddr"; "caddr"; "null?"; "pair?"; "not"; "length"; "reverse"; "list?"
                   "symbol?"; "number?"; "integer?"; "string-length"; "vlength"; "vector->list"; "list->vector" ] do
            yield n, (1, 1)
        for n in [ "cons"; "nth"; "map"; "filter"; "assoc"; "equal?"; "sort"; "vref"; "any?"; "every?" ] do
            yield n, (2, 2)
        yield "foldl", (3, 3)
        yield "vset!", (3, 3)
        yield "hash-set!", (3, 3)
        yield "hash-ref", (2, 3)
        yield "newline", (0, 0)
        yield "display", (1, 1) ]

// Редакционное расстояние (для подсказки ближайшего имени)
let editDistance (a: string) (b: string) : int =
    let d = Array2D.zeroCreate (a.Length + 1) (b.Length + 1)
    for i in 0 .. a.Length do d.[i, 0] <- i
    for j in 0 .. b.Length do d.[0, j] <- j
    for i in 1 .. a.Length do
        for j in 1 .. b.Length do
            let cost = if a.[i - 1] = b.[j - 1] then 0 else 1
            d.[i, j] <- min (min (d.[i - 1, j] + 1) (d.[i, j - 1] + 1)) (d.[i - 1, j - 1] + cost)
    d.[a.Length, b.Length]

let private arityOfNames (names: string list) : int * int =
    match List.tryFindIndex ((=) "&rest") names with
    | Some k -> (k, -1)
    | None -> (names.Length, names.Length)

let private arityText (mn: int, mx: int) : string =
    if mx < 0 then sprintf "не менее %d" mn
    elif mn = mx then string mn
    else sprintf "от %d до %d" mn mx

// Макросы prelude/lib с известной формой: аргументы — обычные выражения (кроме отмеченных ниже)
let private exprMacros =
    set [ "when"; "unless"; "while"; "delay"; "cons-stream"; "steps"; "explain"; "assert-error"; "for-each" ]

let private specialNames : Set<string> = set Evaluator.specialFormNames

// Файл → диагностика статических проверок (чтение — отдельно, parseSource)
let private staticChecks (env: Env) (file: string) (forms: Node list) (diags: List<Diag>) : unit =
    let lib = libInfo.Force()
    // внутри (assert-error ...) выражение должно упасть: диагностика там подавляется (ожидаемая ошибка)
    let quiet = ref 0
    let add sev (p: P) code msg =
        if quiet.Value = 0 then
            diags.Add { File = file; Line = p.L; Col = p.C; Severity = sev; Code = code; Message = msg }
    let err p code msg = add SevError p code msg
    let warn p code msg = add SevWarning p code msg
    let header = moduleHeader forms
    let body = if header.IsSome then List.tail forms else forms
    // определения файла: имя -> арности (для define-функций); (-2,-2) — не функция/неизвестно
    let fileDefs = HashSet<string>()
    let fileArity = Dictionary<string, List<int * int>>()
    let fileMacros = HashSet<string>()
    let noteArity (n: string) (a: int * int) =
        fileDefs.Add n |> ignore
        if not (fileArity.ContainsKey n) then fileArity.[n] <- List<int * int>()
        fileArity.[n].Add a
    let rec collect (fs: Node list) =
        for f in fs do
            match f with
            | Lst (Sym ("define", _) :: Sym (n, _) :: _, _, _) -> noteArity n (-2, -2)
            | Lst (Sym ("define", _) :: Lst (Sym (n, _) :: ps, _, _) :: _, _, _) ->
                let names = ps |> List.map (function Sym (s, _) -> s | _ -> "?")
                noteArity n (arityOfNames names)
            | Lst (Sym ("defmacro", _) :: Lst (Sym (n, _) :: _, _, _) :: _, _, _) ->
                noteArity n (-2, -2)
                fileMacros.Add n |> ignore
            | Lst (Sym ("defmemo", _) :: Lst (Sym (n, _) :: _, _, _) :: _, _, _) -> noteArity n (-2, -2)
            | Lst (Sym ("begin", _) :: inner, _, _) -> collect inner
            | _ -> ()
    collect body
    // (load "файл"): имена из загружаемого файла (экспорт модуля или все верхнеуровневые определения)
    let dir = (try IO.Path.GetDirectoryName(IO.Path.GetFullPath file) with _ -> ".")
    for f in body do
        match f with
        | Lst ([ Sym ("load", _); Str (path, _) ], _, _) ->
            let cands = [ IO.Path.Combine(dir, path); path; IO.Path.Combine(AppContext.BaseDirectory, "lib", path) ]
            match cands |> List.tryFind IO.File.Exists with
            | Some full ->
                let sub, _ = parseSource full (IO.File.ReadAllText full)
                match moduleHeader sub with
                | Some (_, exports) -> for (e, _) in exports do fileDefs.Add e |> ignore
                | None -> for d in definedIn sub do fileDefs.Add d |> ignore
                for m in macroNamesIn sub do fileMacros.Add m |> ignore
            | None -> ()
        | _ -> ()
    // имена других файлов того же модуля (модуль из нескольких частей: приватные имена общие)
    match header with
    | Some (m, _) ->
        match lib.DefsByModule.TryGetValue m with
        | true, defs -> for d in defs do fileDefs.Add d |> ignore
        | _ -> ()
    | None -> ()
    let isKeyword (s: string) = s.Length > 1 && s.[0] = ':'
    let isKnownGlobal (name: string) : bool =
        fileDefs.Contains name || specialNames.Contains name || lib.Exports.Contains name || isKeyword name
        || (env.Lookup name).IsSome
        || (let k = name.IndexOf "::" in k > 0 && (lib.Modules.Contains(name.Substring(0, k)) || (match header with Some (m, _) -> m = name.Substring(0, k) | None -> false) || env.Modules.ContainsKey(name.Substring(0, k))))
    let isMacroName (name: string) =
        exprMacros.Contains name || fileMacros.Contains name || lib.Macros.Contains name
        || name = "deftest" || name = "with-step" || name = "do" || name = "assuming" || name = "defmemo"
        || (match env.Lookup name with Some (LispMacro _) -> true | _ -> false)
    let allNames = lazy (
        let s = HashSet<string>()
        for c in env.OwnCells do
            if not (obj.ReferenceEquals(c.Value, null)) then s.Add c.Name |> ignore
        for d in fileDefs do s.Add d |> ignore
        for e in lib.Exports do s.Add e |> ignore
        s)
    let suggest (name: string) (sc: Set<string>) : string =
        match hints.TryGetValue name with
        | true, h -> "; " + h
        | _ when name.Length <= 2 -> ""
        | _ ->
            let limit = if name.Length <= 4 then 1 else 2
            let cand =
                Seq.append (allNames.Force()) sc
                |> Seq.filter (fun c -> abs (c.Length - name.Length) <= limit && not (c.Contains "::"))
                |> Seq.map (fun c -> c, editDistance name c)
                |> Seq.filter (fun (_, d) -> d <= limit)
                |> Seq.sortBy snd
                |> Seq.tryHead
            match cand with
            | Some (c, _) -> sprintf "; возможно, имелось в виду %s" c
            | None -> ""
    let checkRef (sc: Set<string>) (name: string) (p: P) =
        if not (Set.contains name sc) && not (isKnownGlobal name) then
            warn p "unknown-name" (sprintf "неизвестное имя «%s»%s" name (suggest name sc))
    let arityFor (name: string) : (int * int) option =
        if fileDefs.Contains name then
            match fileArity.TryGetValue name with
            | true, l when l.Count > 0 && (l |> Seq.distinct |> Seq.length) = 1 && fst l.[0] >= 0 -> Some l.[0]
            | _ -> None
        else
            match env.Lookup name with
            | Some (LispFunc f) -> Some (arityOfNames f.Params)
            | Some (LispBuiltin _) ->
                (match builtinArity.TryGetValue name with
                 | true, a -> Some a
                 | _ -> None)
            | _ -> None
    let checkArity (name: string) (p: P) (n: int) =
        match arityFor name with
        | Some (mn, mx) when n < mn || (mx >= 0 && n > mx) ->
            err p "arity" (sprintf "вызов %s: ожидается аргументов %s, получено %d" name (arityText (mn, mx)) n)
        | _ -> ()
    let checkParams (ps: Node list) (what: string) =
        for p in ps do
            match p with
            | Sym _ -> ()
            | other -> err (posOf other) "bad-params" (sprintf "%s: параметр должен быть символом" what)
        match ps |> List.tryFindIndex (isSymNamed "&rest") with
        | Some k when k <> ps.Length - 2 ->
            err (posOf ps.[k]) "bad-params" (sprintf "%s: после &rest ровно одно имя параметра" what)
        | _ -> ()
    let paramNames (ps: Node list) =
        ps |> List.choose (function Sym (s, _) when s <> "&rest" -> Some s | _ -> None)
    let patternVars (nodes: Node list) : string list =
        let acc = List<string>()
        let rec go n =
            match n with
            | Sym (s, _) when s.StartsWith "?" -> acc.Add s
            | Lst (items, _, _) -> List.iter go items
            | Vec (items, _) -> List.iter go items
            | _ -> ()
        List.iter go nodes
        List.ofSeq acc
    let isBuiltinName (name: string) =
        match env.TryBound name with
        | null -> false
        | c -> (match c.Value with LispBuiltin _ -> true | _ -> false)
    let shape p what = err p "bad-form" what
    let rec walk (sc: Set<string>) (top: bool) (n: Node) : unit =
        match n with
        | Sym (name, p) -> checkRef sc name p
        | Num _ | Str _ | Bool _ | Vec _ -> ()
        | Lst ([], _, _) -> ()
        | Lst (head :: args, p, _) ->
            match head with
            | Sym (name, hp) when not (Set.contains name sc) -> walkForm sc top name hp p args
            | Sym (_, _) -> List.iter (walk sc false) args
            | other ->
                walk sc false other
                List.iter (walk sc false) args
    and walkBody (sc: Set<string>) (forms: Node list) : unit =
        let sc2 = Set.union sc (Set.ofList (definedIn forms))
        for f in forms do walk sc2 false f
    and walkLambda (sc: Set<string>) (what: string) (ps: Node list) (bodyForms: Node list) : unit =
        checkParams ps what
        walkBody (Set.union sc (Set.ofList (paramNames ps))) bodyForms
    and walkBindings (sc: Set<string>) (what: string) (bs: Node list) : (string * Node) list =
        bs |> List.choose (fun b ->
            match b with
            | Lst ([ Sym (s, _); e ], _, _) -> Some (s, e)
            | other ->
                shape (posOf other) (sprintf "%s: неверный формат привязки, ожидается (имя значение)" what)
                None)
    and walkQQ (sc: Set<string>) (depth: int) (n: Node) : unit =
        match n with
        | Lst ([ Sym (("unquote" | "unquote-splicing"), _); x ], _, _) ->
            if depth = 1 then walk sc false x else walkQQ sc (depth - 1) x
        | Lst ([ Sym ("quasiquote", _); x ], _, _) -> walkQQ sc (depth + 1) x
        | Lst (items, _, _) -> List.iter (walkQQ sc depth) items
        | _ -> ()
    and walkForm (sc: Set<string>) (top: bool) (name: string) (hp: P) (p: P) (args: Node list) : unit =
        match name with
        | "quote" ->
            if args.Length <> 1 then shape p "quote: требуется один аргумент"
        | "quasiquote" ->
            (match args with
             | [ t ] -> walkQQ sc 1 t
             | _ -> shape p "quasiquote: требуется один аргумент")
        | "unquote" | "unquote-splicing" -> List.iter (walk sc false) args
        | "if" ->
            if args.Length < 2 || args.Length > 3 then
                shape p (sprintf "if: требуется 2 или 3 аргумента, получено %d" args.Length)
            List.iter (walk sc false) args
        | "define" ->
            (match args with
             | Sym (n, np) :: rest ->
                if isKeyword n then shape np (sprintf "define: %s — ключевое слово, имя переменной быть не может" n)
                if top && isBuiltinName n then
                    err np "define-builtin" (sprintf "define: имя %s занято встроенной функцией (builtin): переименуйте" n)
                (match rest with
                 | [ v ] -> walk sc false v
                 | [] -> shape p "define: нет значения"
                 | _ -> shape p "define: лишние аргументы, ожидается (define имя значение)")
             | Lst (Sym (n, np) :: ps, _, _) :: (_ :: _ as bodyForms) ->
                if isKeyword n then shape np (sprintf "define: %s — ключевое слово, имя функции быть не может" n)
                if top && isBuiltinName n then
                    err np "define-builtin" (sprintf "define: имя %s занято встроенной функцией (builtin): переименуйте" n)
                walkLambda sc ("define " + n) ps bodyForms
             | Lst (Sym _ :: _, _, _) :: [] -> shape p "define: пустое тело функции"
             | _ -> shape p "define: неверный синтаксис, ожидается (define имя значение) или (define (имя параметры...) тело...)")
        | "set!" ->
            (match args with
             | [ Sym (n, np); v ] ->
                checkRef sc n np
                walk sc false v
             | _ -> shape p "set!: неверный синтаксис, ожидается (set! имя значение)")
        | "lambda" ->
            (match args with
             | Lst (ps, _, _) :: (_ :: _ as bodyForms) -> walkLambda sc "lambda" ps bodyForms
             | _ -> shape p "lambda: неверный синтаксис, ожидается (lambda (параметры...) тело...)")
        | "let" ->
            (match args with
             | Lst (bs, _, _) :: (_ :: _ as bodyForms) ->
                let pairs = walkBindings sc "let" bs
                for (_, e) in pairs do walk sc false e
                walkBody (Set.union sc (Set.ofList (List.map fst pairs))) bodyForms
             | Sym (loop, _) :: Lst (bs, _, _) :: (_ :: _ as bodyForms) ->
                let pairs = walkBindings sc "let" bs
                let sc1 = Set.add loop sc
                for (_, e) in pairs do walk sc1 false e
                walkBody (Set.union sc1 (Set.ofList (List.map fst pairs))) bodyForms
             | _ -> shape p "let: неверный синтаксис, ожидается (let ((имя значение)...) тело...)")
        | "let*" ->
            (match args with
             | Lst (bs, _, _) :: (_ :: _ as bodyForms) ->
                let mutable cur = sc
                for b in bs do
                    match b with
                    | Lst ([ Sym (s, _); e ], _, _) ->
                        walk cur false e
                        cur <- Set.add s cur
                    | other -> shape (posOf other) "let*: неверный формат привязки, ожидается (имя значение)"
                walkBody cur bodyForms
             | _ -> shape p "let*: неверный синтаксис, ожидается (let* ((имя значение)...) тело...)")
        | "letrec" ->
            (match args with
             | Lst (bs, _, _) :: (_ :: _ as bodyForms) ->
                let pairs = walkBindings sc "letrec" bs
                let sc1 = Set.union sc (Set.ofList (List.map fst pairs))
                for (_, e) in pairs do walk sc1 false e
                walkBody sc1 bodyForms
             | _ -> shape p "letrec: неверный синтаксис, ожидается (letrec ((имя значение)...) тело...)")
        | "begin" -> List.iter (walk sc top) args
        | "and" | "or" | "time" | "profile" -> List.iter (walk sc false) args
        | "try" ->
            if args.Length <> 2 then shape p "try: требуется (try выражение обработчик)"
            List.iter (walk sc false) args
        | "unwind-protect" ->
            if args.IsEmpty then shape p "unwind-protect: требуется (unwind-protect тело очистка...)"
            List.iter (walk sc false) args
        | "case" ->
            (match args with
             | key :: clauses ->
                walk sc false key
                for cl in clauses do
                    match cl with
                    | Lst (Sym ("else", _) :: (_ :: _ as bodyForms), _, _) -> List.iter (walk sc false) bodyForms
                    | Lst (Lst _ :: (_ :: _ as bodyForms), _, _) -> List.iter (walk sc false) bodyForms
                    | other -> shape (posOf other) "case: неверная ветка, ожидается ((данные...) выражение...) или (else выражение...)"
             | [] -> shape p "case: требуется ключ")
        | "cond" ->
            for cl in args do
                match cl with
                | Lst (Sym ("else", _) :: (_ :: _ as bodyForms), _, _) -> List.iter (walk sc false) bodyForms
                | Lst (test :: (_ :: _ as bodyForms), _, _) ->
                    walk sc false test
                    List.iter (walk sc false) bodyForms
                | other -> shape (posOf other) "cond: неверная ветка, ожидается (условие выражение...); тело обязательно"
        | "defmacro" ->
            (match args with
             | Lst (Sym _ :: ps, _, _) :: (_ :: _ as bodyForms) -> walkLambda sc "defmacro" ps bodyForms
             | _ -> shape p "defmacro: неверный синтаксис, ожидается (defmacro (имя параметры...) тело...)")
        | "defrule" ->
            (match args with
             | Sym _ :: pattern :: replacement :: tail ->
                let vars = patternVars [ pattern; replacement ] |> Set.ofList
                let rec condOf (xs: Node list) =
                    match xs with
                    | Sym (":ac", _) :: more -> condOf more
                    | Sym (":title", _) :: Str _ :: more -> condOf more
                    | x :: more -> walk (Set.union sc vars) false x; condOf more
                    | [] -> ()
                condOf tail
             | _ -> shape p "defrule: (defrule имя образец замена [условие] [:ac] [:title \"заголовок\"])")
        | "defmethod" ->
            (match args with
             | Sym _ :: Lst _ :: Lst (ps, _, _) :: (_ :: _ as bodyForms) -> walkLambda sc "defmethod" ps bodyForms
             | _ -> shape p "defmethod: (defmethod op (типы...) (параметры...) тело...)")
        | "module" ->
            err p "bad-form" "module: объявление модуля допустимо только первой формой файла"
        | _ when isMacroName name -> walkMacro sc name p args
        | _ ->
            checkRef sc name hp
            checkArity name hp args.Length
            List.iter (walk sc false) args
    and walkMacro (sc: Set<string>) (name: string) (p: P) (args: Node list) : unit =
        match name with
        | _ when fileMacros.Contains name -> ()          // макрос файла: форма аргументов неизвестна
        | "assert-error" ->
            quiet.Value <- quiet.Value + 1
            List.iter (walk sc false) args
            quiet.Value <- quiet.Value - 1
        | _ when exprMacros.Contains name -> List.iter (walk sc false) args
        | "with-step" ->
            (match args with
             | Lst (items, _, _) :: bodyForms ->
                List.iter (walk sc false) items
                walkBody sc bodyForms
             | _ -> ())
        | "deftest" ->
            (match args with
             | _ :: bodyForms -> walkBody sc bodyForms
             | [] -> ())
        | "do" ->
            (match args with
             | Lst (vars, _, _) :: Lst (exit, _, _) :: bodyForms ->
                let parsed =
                    vars |> List.choose (fun v ->
                        match v with
                        | Lst (Sym (s, _) :: init :: step, _, _) -> Some (s, init, step)
                        | _ -> None)
                for (_, init, _) in parsed do walk sc false init
                let sc2 = Set.union sc (Set.ofList (parsed |> List.map (fun (s, _, _) -> s)))
                for (_, _, step) in parsed do List.iter (walk sc2 false) step
                List.iter (walk sc2 false) exit
                walkBody sc2 bodyForms
             | _ -> ())
        | "assuming" ->
            (match args with
             | Lst (bs, _, _) :: bodyForms ->
                for b in bs do
                    match b with
                    | Lst (_ :: exprs, _, _) -> List.iter (walk sc false) exprs
                    | _ -> ()
                walkBody sc bodyForms
             | _ -> ())
        | "defmemo" ->
            (match args with
             | Lst (Sym _ :: ps, _, _) :: (_ :: _ as bodyForms) -> walkLambda sc "defmemo" ps bodyForms
             | _ -> ())
        | _ -> ()                                         // прочий макрос библиотеки: форма аргументов неизвестна
    // заголовок модуля: экспортированные имена должны быть определены
    (match header with
     | Some (m, exports) ->
        for (e, ep) in exports do
            if not (fileDefs.Contains e) && (env.Lookup e).IsNone then
                err ep "export-undefined" (sprintf "модуль %s экспортирует имя %s, но не определяет его" m e)
     | None -> ())
    let top0 = Set.empty
    for f in body do walk top0 true f

let private defaultEnv : Lazy<Env> = lazy (Evaluator.newEnv ())

// Полная проверка текста файла (чтение + статические проверки) в окружении env (после prelude)
let checkTextEnv (env: Env) (file: string) (text: string) : Diag list =
    let forms, readDiags = parseSource file text
    let diags = List<Diag>()
    // статические проверки — только по полностью прочитанным формам
    (try staticChecks env file forms diags
     with ex -> diags.Add { File = file; Line = 1; Col = 1; Severity = SevWarning; Code = "checker-failure"
                            Message = "внутренняя ошибка проверщика: " + ex.Message })
    (readDiags @ List.ofSeq diags) |> List.sortBy (fun d -> d.Line, d.Col)

// То же в отдельном окружении с prelude (создаётся один раз на процесс)
let checkText (file: string) (text: string) : Diag list = checkTextEnv (defaultEnv.Force()) file text
