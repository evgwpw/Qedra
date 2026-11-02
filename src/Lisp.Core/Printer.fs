// Красивый вывод Lisp-значений — используется REPL, AgentApi
module Printer

open Types

// Шаг D1: глобальное ограничение длины печати результата хостом (REPL, -e, show); 0 — без ограничения.
// Не применяется к --json/--mcp (там свои лимиты) и к display внутри программ. Считается от уже
// напечатанной строки (после prettyPrint/mathPrint), обрезка — с хвостом «… [обрезано: N символов, M узлов]».
let mutable PrintLimit: int = 0

// число узлов значения (атом или голова списка + подсчёт по аргументам) — для пояснения «что обрезано»
let rec countNodes (v: LispValue) : int =
    match v with
    | LispList items -> 1 + List.sum (List.map countNodes items)
    | LispVector items -> 1 + Array.sum (Array.map countNodes items)
    | LispPair (a, b) -> 1 + countNodes a + countNodes b
    | _ -> 1

// Ограничение напечатанной строки: длиннее PrintLimit — обрезать, добавив хвост с числом отброшенных
// символов и узлов исходного значения. PrintLimit <= 0 — вернуть как есть. Хвост не длиннее лимита.
let limitPrint (v: LispValue) (s: string) : string =
    if PrintLimit <= 0 || s.Length <= PrintLimit then s
    else
        let tail = sprintf "… [обрезано: %d символов, %d узлов]" (s.Length - PrintLimit) (countNodes v)
        let keep = max 0 (PrintLimit - tail.Length)
        s.Substring(0, keep) + tail

// Рекурсивный вывод Lisp-значения в стандартной нотации
let rec prettyPrint (v: LispValue) : string =
    match v with
    | LispInteger n -> string n
    | LispRational (p, q) -> string p + "/" + string q
    | LispFloat f ->
        // LANG.1: float с целым значением печатается с .0 (2.0), чтобы отличать от целого;
        // прежний «string f» давал «2» — неотличимо от LispInteger 2
        let s = string f
        if System.Double.IsNaN f then "nan"
        elif System.Double.IsInfinity f then (if f > 0.0 then "+inf" else "-inf")
        elif s.IndexOfAny([| '.'; 'e'; 'E' |]) < 0 then s + ".0"
        else s
    | LispComplex (re, im) ->
        prettyPrint re + " + " + prettyPrint im + "i"
    | LispAlgebraic (poly, (loN, loD), (hiN, hiD)) ->
        let polyStr = poly |> List.map string |> String.concat " "
        "root(" + polyStr + ", " + string loN + "/" + string loD + ", " + string hiN + "/" + string hiD + ")"
    | LispBool true -> "#t"
    | LispBool false -> "#f"
    | LispStr s -> "\"" + s + "\""
    | LispSym s -> s
    | LispNil -> "nil"
    // ODE.0: производная неизвестной функции в точке — f′(u), f″(u), …
    | LispList [LispSym "deriv"; fs; LispInteger k; u] when k >= 1I && k <= 4I ->
        prettyPrint fs + String.replicate (int k) "'" + "(" + prettyPrint u + ")"
    | LispList items ->
        "(" + String.concat " " (List.map prettyPrint items) + ")"
    | LispFunc f -> "#<функция " + f.Name + ">"
    | LispBuiltin _ -> "#<встроенная>"
    | LispMacro m -> "#<макрос " + m.Name + ">"
    | LispVector items ->
        "#(" + String.concat " " (Array.map prettyPrint items) + ")"
    // Шаг 21d: точечная пара (a . b); цепочка пар печатается как (a b . c)
    | LispPair (a, b) ->
        let rec tail (x: LispValue) (acc: string list) : string =
            match x with
            | LispPair (h, t) -> tail t (prettyPrint h :: acc)
            | last -> String.concat " " (List.rev acc) + " . " + prettyPrint last
        "(" + tail b [ prettyPrint a ] + ")"
    // Шаг 15b: объект ошибки (try): #<error сообщение>
    | LispObject { Type = "error"; Fields = fields } when fields.Length = 3 ->
        "#<error " + (match fields.[0] with LispStr m -> m | other -> prettyPrint other) + ">"
    | LispObject o ->
        // метод (print type) возвращает строку; иначе #<type f1 f2 ...>
        match Objects.findMethod "print" [o.Type] with
        | Some fn ->
            match Objects.applyHook fn [v] with
            | LispStr s -> s
            | other -> prettyPrint other
        | None ->
            "#<" + String.concat " " (o.Type :: (o.Fields |> Array.map prettyPrint |> List.ofArray)) + ">"

// Шаг D3a: контекст в ошибках builtins — имя функции, номер аргумента (1-based, 0 — не про аргумент),
// что ожидалось (expected — уже с глаголом, напр. «ожидался объект») и укороченная печать полученного
// значения (≤ 200 символов, без хвоста-счётчика: ошибки короткие, лимит печати результата здесь
// неуместен). Формат:  f: аргумент 2 — ожидался многочлен, получено: (a b c)
// Возвращает 'a (всегда бросает) — можно ставить веткой match, как failwith
let expectError<'a> (who: string) (argIndex: int) (expected: string) (value: LispValue) : 'a =
    let shown =
        let s = prettyPrint value
        if s.Length > 200 then s.Substring(0, 200) + "… [обрезано]" else s
    let place = if argIndex > 0 then sprintf "аргумент %d — " argIndex else ""
    raise (System.Exception(sprintf "%s: %s%s, получено: %s" who place expected shown))
