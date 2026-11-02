// Полный порядок на выражениях (orderCompare / orderp) — Шаг 13, вынесено из Simplify.fs (Шаг 15a)
// Не зависит от simplify: числа < символы < составные < прочее; степени сравниваются по основанию
module Order

open System
open Types
open Numeric

// Ранг вида: числа < символы < составные < прочее
let rankOf (v: LispValue) : int =
    match v with
    | LispInteger _ | LispRational _ | LispFloat _ | LispComplex _ | LispAlgebraic _ -> 0
    | LispSym _ -> 1
    | LispList _ -> 2
    | LispBool _ -> 3
    | LispStr _ -> 4
    | LispNil -> 5
    | LispObject _ -> 6
    | LispVector _ -> 7
    | LispPair _ -> 8
    | _ -> 9

let toFloat (v: LispValue) : float =
    match promoteTo KindFloat v with LispFloat f -> f | _ -> 0.0

// Сравнение чисел: вещественные по значению; комплексные — после вещественных (по re, затем im)
let rec numCompare (a: LispValue) (b: LispValue) : int =
    match a, b with
    | LispComplex (r1, i1), LispComplex (r2, i2) ->
        let c = numCompare r1 r2
        if c <> 0 then c else numCompare i1 i2
    | LispComplex _, _ -> 1
    | _, LispComplex _ -> -1
    | LispAlgebraic _, _ | _, LispAlgebraic _ -> compare (toFloat a) (toFloat b)
    | _ -> compareNum a b

// Степенной «вид» выражения: (^ b e) → (b, Some e); иначе (e, None)
let powView (v: LispValue) : LispValue * LispValue option =
    match v with
    | LispList [LispSym "^"; b; e] -> (b, Some e)
    | _ -> (v, None)

// Оператор и аргументы составного объекта; plain-list — оператор "" и все элементы как аргументы
let opArgs (v: LispValue) : string * LispValue list =
    match v with
    | LispList (LispSym s :: rest) -> (s, rest)
    | LispList items -> ("", items)
    | _ -> ("", [])

// Полный порядок: <0, 0, >0. Сравнение идёт по ОСНОВАНИЮ (степень (^ b e) — по b, затем по e),
// основания: ранг (число < символ < составной); числа — по значению; символы — по алфавиту
// (ordinal); составные — по оператору, затем по аргументам лексикографически (короткий — раньше)
let rec orderCompare (a: LispValue) (b: LispValue) : int =
    let ba, ea = powView a
    let bb, eb = powView b
    let c = structCompare ba bb
    if c <> 0 then c
    else
        match ea, eb with
        | None, None -> 0
        | Some x, Some y -> orderCompare x y
        | None, Some y -> orderCompare (LispInteger 1I) y
        | Some x, None -> orderCompare x (LispInteger 1I)

and structCompare (a: LispValue) (b: LispValue) : int =
    let ra, rb = rankOf a, rankOf b
    if ra <> rb then compare ra rb
    else
        match a, b with
        | LispSym x, LispSym y -> sign (String.CompareOrdinal(x, y))
        | LispList _, LispList _ ->
            let opA, argsA = opArgs a
            let opB, argsB = opArgs b
            let c = sign (String.CompareOrdinal(opA, opB))
            if c <> 0 then c
            else
                let rec lex (xs: LispValue list) (ys: LispValue list) =
                    match xs, ys with
                    | [], [] -> 0
                    | [], _ -> -1
                    | _, [] -> 1
                    | x :: xt, y :: yt ->
                        let c = orderCompare x y
                        if c <> 0 then c else lex xt yt
                lex argsA argsB
        | LispObject x, LispObject y ->
            let c = sign (String.CompareOrdinal(x.Type, y.Type))
            if c <> 0 then c else lexArr x.Fields y.Fields
        | LispVector x, LispVector y -> lexArr x y
        | LispPair (a1, b1), LispPair (a2, b2) ->
            let c = orderCompare a1 a2
            if c <> 0 then c else orderCompare b1 b2
        | LispBool x, LispBool y -> compare x y
        | LispStr x, LispStr y -> sign (String.CompareOrdinal(x, y))
        | _ when ra = 0 -> numCompare a b
        | _ -> 0

// Лексикографическое сравнение массивов (короткий — раньше)
and lexArr (xs: LispValue[]) (ys: LispValue[]) : int =
    if xs.Length <> ys.Length then compare xs.Length ys.Length
    else
        let mutable c = 0
        let mutable i = 0
        while c = 0 && i < xs.Length do
            c <- orderCompare xs.[i] ys.[i]
            i <- i + 1
        c

// orderp: a предшествует b или равно ему (a <= b в каноническом порядке)
let orderp (a: LispValue) (b: LispValue) : bool = orderCompare a b <= 0
