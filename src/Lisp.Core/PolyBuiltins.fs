// Регистрация builtins многочленов и рациональных функций (Шаг 17, коммит 3).
// Алгоритмы — в MPoly.fs / PolyFactor.fs / RatFun.fs; здесь только разбор аргументов.
// Старые poly-add/poly-sub/... на списках коэффициентов (Polynomial.fs, CasBuiltins.fs) сохранены.
module PolyBuiltins

open Types
open Builtins

let private one1 (name: string) (f: LispValue -> LispValue) : string * LispValue =
    builtin name (fun args ->
        match args with
        | [a] -> f a
        | _ -> failwithf "%s: один аргумент" name)

let private two (name: string) (f: LispValue -> LispValue -> LispValue) : string * LispValue =
    builtin name (fun args ->
        match args with
        | [a; b] -> f a b
        | _ -> failwithf "%s: два аргумента" name)

// --- шаг 21i: мост к Groebner.fs (внутреннее представление lib\groebner.lisp: многочлен — список термов (c d e1 … en)) ---
let private gbCoef (v: LispValue) : Groebner.Q =
    match v with
    | LispInteger n -> (n, 1I)
    | LispRational (n, d) -> (n, d)
    | other -> failwithf "groebner-basis-raw: коэффициент — рациональное число, получено %s" (Printer.prettyPrint other)

let private gbInt (v: LispValue) : int =
    match v with
    | LispInteger n -> int n
    | other -> failwithf "groebner-basis-raw: показатель — целое, получено %s" (Printer.prettyPrint other)

let private gbPoly (v: LispValue) : Groebner.Poly =
    match v with
    | LispNil -> [||]
    | LispList terms ->
        terms |> List.map (fun t ->
            match t with
            | LispList (c :: m) -> { Groebner.C = gbCoef c; Groebner.M = m |> List.map gbInt |> Array.ofList }
            | other -> failwithf "groebner-basis-raw: терм (c d e1 … en), получено %s" (Printer.prettyPrint other))
        |> Array.ofList
    | other -> failwithf "groebner-basis-raw: многочлен — список термов, получено %s" (Printer.prettyPrint other)

let private gbToLisp (p: Groebner.Poly) : LispValue =
    if p.Length = 0 then LispNil else
    LispList [ for t in p ->
                 LispList (Numeric.makeRational (fst t.C) (snd t.C) :: [ for e in t.M -> LispInteger (bigint e) ]) ]

let private gbOrder (v: LispValue) : Groebner.Order =
    match v with
    | LispSym s -> Groebner.orderOfName s
    | LispList [ LispSym "block"; LispInteger k ] -> Groebner.Block (int k)
    | other -> failwithf "groebner-basis-raw: порядок — lex, grlex, grevlex или (block k), получено %s" (Printer.prettyPrint other)

let all : (string * LispValue) list = [
    // (groebner-basis-raw многочлены порядок стратегия предел) — приведённый базис Грёбнера во внутреннем представлении
    // lib\groebner.lisp (F#-версия Бухбергера, Groebner.fs); стратегия — normal | sugar; предел — число редукций S-пар
    builtin "groebner-basis-raw" (fun args ->
        match args with
        | [LispList ps; ord; LispSym strategy; LispInteger lim] ->
            let polys = ps |> List.map gbPoly
            match Groebner.basis (gbOrder ord) (strategy = "sugar") (int lim) polys with
            | [] -> LispNil
            | g -> LispList (g |> List.map gbToLisp)
        | [LispNil; _; _; _] -> LispNil
        | _ -> failwith "groebner-basis-raw: (groebner-basis-raw многочлены порядок стратегия предел)")

    // Шаг 21i'' (1): диагностика Грёбнера из Lisp. (rational-bits c) — длина числителя + знаменателя в битах (целое — с единицей
    // знаменателя); (clock-us) — монотонные часы, микросекунды
    one1 "rational-bits" (fun v -> LispInteger (bigint (Rational.ratBits (gbCoef v))))
    builtin "clock-us" (fun _ ->
        LispInteger (bigint (System.Diagnostics.Stopwatch.GetTimestamp() / (System.Diagnostics.Stopwatch.Frequency / 1000000L))))

    // (together e) — одна дробь, сокращённая на НОД, числитель и знаменатель раскрыты
    one1 "together" RatFun.together
    // (cancel e) — сокращение дробей без приведения к общему знаменателю
    one1 "cancel" RatFun.cancel
    one1 "numer" RatFun.numer
    one1 "denom" RatFun.denom
    // (apart e x) — простейшие дроби по x над ℚ
    two "apart" RatFun.apart
    two "poly-gcd" RatFun.polyGcd
    two "poly-lcm" RatFun.polyLcm
    builtin "poly-quotient" (fun args ->
        match args with
        | [a; b; x] -> RatFun.polyQuotient a b x
        | _ -> failwith "poly-quotient: три аргумента (a b x)")
    builtin "poly-remainder" (fun args ->
        match args with
        | [a; b; x] -> RatFun.polyRemainder a b x
        | _ -> failwith "poly-remainder: три аргумента (a b x)")
    // (coeff e x n) — коэффициент при x^n
    builtin "coeff" (fun args ->
        match args with
        | [e; x; LispInteger n] when n >= 0I -> RatFun.coeff e x (int n)
        | _ -> failwith "coeff: (coeff e x n), n — неотрицательное целое")
    two "degree" RatFun.degree
    one1 "variables" RatFun.variables
    one1 "sqfree" Factor.sqfreeExpr
    one1 "poly?" (fun e -> LispBool (RatFun.isPoly e))
    two "polynomial?" (fun e x -> LispBool (RatFun.isPolynomialIn e x))
    // Шаг 18: примитивы для solve
    two "subst" SolveNum.subst
    builtin "resultant" (fun args ->
        match args with
        | [p; q; x] -> SolveNum.resultant p q x
        | _ -> failwith "resultant: три аргумента (p q x)")
    two "nroots" SolveNum.nroots
    two "real-roots" SolveNum.realRoots
    one1 "factor-list" SolveNum.factorList
    one1 "eval-num" SolveNum.evalNum
    one1 "num-abs" SolveNum.numAbs
    // Шаг 21h: (rat-integrate e x t) — сырой результат Эрмит + ЛРТ: (∫полином, рациональная часть, ((Q S i) ...))
    builtin "rat-integrate" (fun args ->
        match args with
        | [e; x; t] -> RatIntExpr.ratIntegrateRaw e x t
        | _ -> failwith "rat-integrate: три аргумента (e x t)")
    // Шаг 21h: (rat-integrate-log e x t real) — первообразная рациональной функции (Эрмит + ЛРТ + вещественная форма +
    // сумма по корням): выражение (+ полином рациональная-часть члены...); real — #t: пары комплексных корней → атаны
    builtin "rat-integrate-log" (fun args ->
        match args with
        | [e; x; t; real] -> RatIntExpr.ratIntegrateLog e x t (Builtins.isTruthy real)
        | _ -> failwith "rat-integrate-log: четыре аргумента (e x t real)")
    // Шаг 21h: (root-sum 't Q E) — Σ E по корням t многочлена Q (каноническая форма); в языке — rootsum(E, t, Q)
    builtin "root-sum" (fun args ->
        match args with
        | [LispSym _ as t; q; e] -> Simplify.simplify (LispList [LispSym "root-sum"; t; q; e])
        | _ -> failwith "root-sum: (root-sum 't Q E) — первый аргумент символ, три аргумента")
    one1 "string->symbol" (fun s ->
        match s with
        | LispStr name -> LispSym name
        | v -> Printer.expectError "string->symbol" 1 "ожидалась строка" v)
]
