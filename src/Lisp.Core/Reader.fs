// Ридер: токенизатор + парсер S-выражений
module Reader

open System
open System.Numerics
open Types

// --- Токенизатор ---

type Token =
    | LPAREN      // (
    | VLPAREN     // #( — начало литерала-вектора
    | RPAREN      // )
    | QUOTE       // '
    | QUASIQUOTE  // `
    | UNQUOTE     // ,
    | UNQUOTE_SPLICING // ,@
    | SYMBOL of string
    | NUMBER of BigInteger
    | RATIONAL of BigInteger * BigInteger  // числитель / знаменатель
    | FLOAT of double
    | STRING of string
    | BOOL of bool

// Пропускаем пробелы и комментарии (;)
let private skipWhitespace (s: string) (i: byref<int>) =
    while i < s.Length && (Char.IsWhiteSpace s.[i] || s.[i] = ';') do
        if s.[i] = ';' then
            while i < s.Length && s.[i] <> '\n' do i <- i + 1
        else
            i <- i + 1

// Проверяем — является ли строка целым числом (включая BigInt)
let private tryParseInteger (s: string) : BigInteger option =
    match BigInteger.TryParse(s) with
    | true, n -> Some n
    | false, _ -> None

// Проверяем — рациональное ли число (формат: N/D, N — целое, D — целое > 0)
let private tryParseRational (s: string) : (BigInteger * BigInteger) option =
    let parts = s.Split('/')
    if parts.Length = 2 then
        match tryParseInteger parts.[0], tryParseInteger parts.[1] with
        | Some n, Some d when d <> 0I -> Some (n, d)
        | _ -> None
    else None

// Проверяем — вещественное ли число (содержит '.' или 'e'/'E')
let private tryParseFloat (s: string) : double option =
    if s.Contains(".") || s.Contains("e") || s.Contains("E") then
        match Double.TryParse(s, Globalization.NumberStyles.Float,
                              Globalization.CultureInfo.InvariantCulture) with
        | true, f -> Some f
        | false, _ -> None
    else None

// Читаем один токен начиная с позиции i, сдвигаем i вперёд
let private nextToken (s: string) (i: byref<int>) : Token option =
    skipWhitespace s &i
    if i >= s.Length then None
    else
        let c = s.[i]
        let start = i
        match c with
        | '(' -> i <- i + 1; Some LPAREN
        | ')' -> i <- i + 1; Some RPAREN
        | '#' when i + 1 < s.Length && s.[i + 1] = '(' -> i <- i + 2; Some VLPAREN
        | '\'' -> i <- i + 1; Some QUOTE
        // Квазицитирование: ` , ,@ — читаются как (quasiquote x) и т.д.
        | '`' -> i <- i + 1; Some QUASIQUOTE
        | ',' ->
            if i + 1 < s.Length && s.[i + 1] = '@' then
                i <- i + 2; Some UNQUOTE_SPLICING
            else
                i <- i + 1; Some UNQUOTE
        | '"' ->
            // Строковый литерал
            i <- i + 1
            let sb = Text.StringBuilder()
            while i < s.Length && s.[i] <> '"' do
                if s.[i] = '\\' && i + 1 < s.Length then
                    match s.[i + 1] with
                    | 'n' -> sb.Append('\n') |> ignore
                    | 't' -> sb.Append('\t') |> ignore
                    | '"' -> sb.Append('"') |> ignore
                    | '\\' -> sb.Append('\\') |> ignore
                    | other -> sb.Append(other) |> ignore
                    i <- i + 2
                else
                    sb.Append(s.[i]) |> ignore
                    i <- i + 1
            if i >= s.Length then
                // Шаг 20: незакрытая строка — ошибка, а не тихая потеря остатка
                let line = 1 + (s.Substring(0, start) |> Seq.filter ((=) '\n') |> Seq.length)
                failwithf "строка %d: не закрыт строковый литерал" line
            i <- i + 1 // закрывающая "
            Some (STRING (sb.ToString()))
        | _ ->
            // Число или символ — читаем до разделителя
            let start = i
            while i < s.Length
                  && not (Char.IsWhiteSpace s.[i])
                  && s.[i] <> '(' && s.[i] <> ')'
                  && s.[i] <> '"' && s.[i] <> ';' do
                i <- i + 1
            let token = s.[start..i - 1]
            // Проверяем по порядку: #t/#f → рациональное → вещественное → целое → символ
            if token = "#t" then Some (BOOL true)
            elif token = "#f" then Some (BOOL false)
            else
                match tryParseRational token with
                | Some (n, d) -> Some (RATIONAL (n, d))
                | None ->
                    match tryParseFloat token with
                    | Some f -> Some (FLOAT f)
                    | None ->
                        match tryParseInteger token with
                        | Some n -> Some (NUMBER n)
                        | None -> Some (SYMBOL token)

// --- Парсер ---

// Токенизируем всю строку; для каждого токена — позиция начала (индекс символа)
let tokenizePos (s: string) : (Token * int) list =
    let tokens = Collections.Generic.List<Token * int>()
    let i = ref 0
    let mutable finished = false
    while not finished do
        skipWhitespace s &i.contents
        let pos = i.Value
        match nextToken s &i.contents with
        | Some t -> tokens.Add((t, pos))
        | None -> finished <- true
    List.ofSeq tokens

let tokenize (s: string) : Token list = tokenizePos s |> List.map fst

// Номер строки (с 1) для индекса символа
let private lineOf (s: string) (idx: int) : int =
    1 + (s.Substring(0, min idx s.Length) |> Seq.filter ((=) '\n') |> Seq.length)

// Шаг 20: проверка баланса скобок. Лишняя «)» и незакрытая «(» — ошибка с номером строки
// начала формы (раньше парсер молча отбрасывал форму и весь остаток файла)
let private checkBalance (s: string) (tokens: (Token * int) list) : unit =
    let stack = Collections.Generic.Stack<int>()
    for (t, pos) in tokens do
        match t with
        | LPAREN | VLPAREN -> stack.Push pos
        | RPAREN ->
            if stack.Count = 0 then
                failwithf "строка %d: лишняя закрывающая скобка" (lineOf s pos)
            else stack.Pop() |> ignore
        | _ -> ()
    if stack.Count > 0 then
        // Самая внешняя незакрытая скобка — начало формы, которая не закрыта
        let outer = stack.ToArray() |> Array.last
        failwithf "строка %d: не закрыта скобка (форма начинается здесь)" (lineOf s outer)

// Шаг 21d: контекст чтения. Starts — индексы символов, с которых начинаются списочные формы, в порядке открытия
// (номер формы = порядковый номер); File = null — позиции не запоминаются (Starts не растёт)
// Dotted — в текущей верхнеуровневой форме встретилась точечная пара (a . b): нумерация форм не совпадёт с обходом
// готового значения, поэтому такая форма не регистрируется для вычисления позиций вложенных форм
type private Ctx = { File: SrcFile; Starts: Collections.Generic.List<int>; mutable Dotted: bool }

let private makeCtx (file: string) (s: string) : Ctx =
    if isNull file then { File = null; Starts = null; Dotted = false }
    else
        let lines = Collections.Generic.List<int>()
        lines.Add 0
        for i in 0 .. s.Length - 1 do
            if s.[i] = '\n' then lines.Add (i + 1)
        { File = SrcFile(file, lines.ToArray()); Starts = Collections.Generic.List<int>(); Dotted = false }

// Открытие формы (скобка, # ( или знак ' ` , ,@): запоминаем индекс символа — это и есть номер формы
let inline private openForm (ctx: Ctx) (idx: int) : unit =
    if not (isNull ctx.File) then ctx.Starts.Add idx

// Парсим одно выражение из списка токенов (токен, индекс его начала)
let rec private parseExpr (ctx: Ctx) (tokens: (Token * int) list) : (LispValue * (Token * int) list) option =
    // Обёртка (quote x) и т. п.: позиция — у знака ' ` , ,@
    let wrap (name: string) (pos: int) (rest: (Token * int) list) =
        openForm ctx pos
        match parseExpr ctx rest with
        | Some (expr, rest2) -> Some (LispList [LispSym name; expr], rest2)
        | None -> None
    match tokens with
    | [] -> None
    | (LPAREN, pos) :: rest -> parseList ctx pos rest
    // #(a b c) — вектор; элементы НЕ вычисляются (как у quote)
    | (VLPAREN, pos) :: rest ->
        match parseList ctx pos rest with
        | Some (LispList items, rest2) -> Some (LispVector (Array.ofList items), rest2)
        | _ -> None
    | (RPAREN, _) :: _ -> None
    | (QUOTE, pos) :: rest -> wrap "quote" pos rest
    // `x → (quasiquote x), ,x → (unquote x), ,@x → (unquote-splicing x)
    | (QUASIQUOTE, pos) :: rest -> wrap "quasiquote" pos rest
    | (UNQUOTE, pos) :: rest -> wrap "unquote" pos rest
    | (UNQUOTE_SPLICING, pos) :: rest -> wrap "unquote-splicing" pos rest
    | (SYMBOL s, _) :: rest -> Some (LispSym s, rest)
    | (NUMBER n, _) :: rest -> Some (LispInteger n, rest)
    | (RATIONAL (n, d), _) :: rest ->
        // Создаём рациональное через Numeric (с сокращением)
        Some (Numeric.makeRational n d, rest)
    | (FLOAT f, _) :: rest -> Some (LispFloat f, rest)
    | (STRING s, _) :: rest -> Some (LispStr s, rest)
    | (BOOL b, _) :: rest -> Some (LispBool b, rest)

// Парсим содержимое списка — до закрывающей скобки; pos — индекс открывающей скобки
and private parseList (ctx: Ctx) (pos: int) (tokens: (Token * int) list) : (LispValue * (Token * int) list) option =
    openForm ctx pos
    let rec loop (acc: LispValue list) (tokens: (Token * int) list) =
        match tokens with
        | (RPAREN, _) :: rest -> Some (LispList (List.rev acc), rest)
        // Шаг 21d: «(a b . c)» — точечная пара: cons-цепочка; хвост-список даёт обычный список: (a . (b c)) = (a b c)
        | (SYMBOL ".", _) :: rest when not acc.IsEmpty ->
            match parseExpr ctx rest with
            | Some (tail, (RPAREN, _) :: rest2) ->
                ctx.Dotted <- true
                let built =
                    List.fold (fun (t: LispValue) (item: LispValue) ->
                        match t with
                        | LispList l -> LispList (item :: l)
                        | LispNil -> LispList [ item ]
                        | _ -> LispPair (item, t)) tail acc
                Some (built, rest2)
            | _ -> failwith "неверная точечная запись: после «.» ожидается одно выражение и «)»"
        | [] -> None
        | _ ->
            match parseExpr ctx tokens with
            | Some (expr, rest) -> loop (expr :: acc) rest
            | None -> None
    loop [] tokens

// Главная функция: строка → список S-выражений; file — имя файла (или «<repl>», «<json>») для позиций форм,
// null — без позиций
let readAllFrom (file: string) (input: string) : LispValue list =
    let ctx = makeCtx file input
    let rec parseAll (tokens: (Token * int) list) (acc: LispValue list) : LispValue list =
        let baseRank = if isNull ctx.File then 0 else ctx.Starts.Count
        ctx.Dotted <- false
        match parseExpr ctx tokens with
        | Some (expr, rest) ->
            // верхнеуровневая форма запоминает файл и номер первой своей формы; вложенные — вычисляются при компиляции
            if not (isNull ctx.File) && not ctx.Dotted then
                match expr with
                | LispList _ -> registerTop expr (TopPos(ctx.File, baseRank, expr))
                | _ -> ()
            parseAll rest (expr :: acc)
        | None -> List.rev acc
    let tp = tokenizePos input
    checkBalance input tp
    let forms = parseAll tp []
    if not (isNull ctx.File) then ctx.File.Starts <- ctx.Starts.ToArray()
    forms

// Без имени файла (null) позиции не запоминаются: строки, собранные программой (и тесты со старыми ожиданиями
// точного текста стека). REPL, JSON и файлы читают через readAllFrom с именем
let readAll (input: string) : LispValue list = readAllFrom null input
