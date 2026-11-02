// Алгебраические числа (Шаг 12) — корни многочленов с целыми коэффициентами
// Представление: (многочлен, изолирующий интервал с рациональными границами)
// Изоляция корней — Sturm.fs, результатант — Resultant.fs, рациональная арифметика — Numeric.fs
module Algebraic

open System.Numerics
open Types
open Numeric
open Sturm
open Resultant

// --- Арифметика алгебраических чисел ---

// Извлечь тройку (poly, lo, hi) из LispValue
let toAlgebraic (v: LispValue) : bigint list * (bigint * bigint) * (bigint * bigint) =
    match v with
    | LispAlgebraic (poly, lo, hi) -> (poly, lo, hi)
    | LispInteger n -> ([1I; -n], (n, 1I), (n, 1I))
    | LispRational (p, q) -> ([q; -p], ratNorm (p, q), ratNorm (p, q))
    | _ -> failwith "toAlgebraic: не алгебраическое число"

// Продвижение рационального к алгебраическому: x = p/q → [q; -p], интервал — точка p/q
let promoteAlg (v: LispValue) : bigint list * (bigint * bigint) * (bigint * bigint) =
    match v with
    | LispInteger n -> ([1I; -n], (n, 1I), (n, 1I))
    | LispRational (p, q) -> ([q; -p], ratNorm (p, q), ratNorm (p, q))
    | LispAlgebraic (poly, lo, hi) -> (poly, lo, hi)
    | _ -> failwith "promoteAlg: не число подходящего типа"

// Неприводимые над ℤ множители многочлена (коэффициенты от старшей степени); при сбое разложения — сам многочлен.
// Шаг 21i: результант из сложения/умножения имеет степень deg p · deg q (r·r для r степени 4 давал многочлен
// степени 16, r³ — 64, и подстановка корня в многочлен «зависала»); минимальный многочлен результата — один из
// неприводимых множителей результанта
let private irreducibleFactors (poly: bigint list) : bigint list list =
    try
        let cs = poly |> List.rev |> List.map MPoly.ofInt |> Array.ofList
        let (_, fs) = PolyFactor.factorPoly (MPoly.mk 0 cs)
        let toList (f: MPoly.MPoly) =
            match f with
            | MPoly.Poly (_, ks) ->
                ks |> Array.map (function MPoly.Const (n, _) -> n | _ -> failwith "не одномерный") |> List.ofArray |> List.rev
            | MPoly.Const (n, _) -> [ n ]
        let ps = fs |> List.map (fst >> toList) |> List.filter (fun f -> degree f >= 1)
        if ps.IsEmpty then [ poly ] else ps
    with _ -> [ poly ]

// Построить результат из многочлена-результатанта и интервала:
// 1) степень 1 → рациональное; 2) иначе разложить на неприводимые множители и изолировать корень в интервале:
// линейный множитель → рациональное число, иначе → алгебраическое (минимальный многочлен)
let makeResult (poly: bigint list) (lo: bigint * bigint) (hi: bigint * bigint) : LispValue =
    match normalize poly with
    | [a; b] -> makeRational (-b) a
    | p ->
        let overlaps (_, (lN, lD), (hN, hD)) = ratCompare (hN, hD) lo >= 0 && ratCompare (lN, lD) hi <= 0
        // несколько корней задевают [lo, hi] — сужать их интервалы, пока не останется один
        let rec choose hits k =
            match hits with
            | _ :: _ :: _ when k < 64 ->
                choose (hits |> List.map (fun (f, l, h) -> let l', h' = refineN f l h 4 in (f, l', h'))
                             |> List.filter overlaps) (k + 1)
            | _ -> hits
        // рациональные корни — линейные множители (раньше — перебор делителей коэффициентов результанта:
        // на результантах с большими коэффициентами — «вечность», когда сумма оказывалась рациональной)
        let hits =
            irreducibleFactors p
            |> List.collect (fun f ->
                match f with
                | [a; b] -> let r = ratNorm (-b, a) in [ (f, r, r) ]
                | _ -> isolateRoots f)
            |> List.filter overlaps
        match choose hits 0 with
        | ([a; b], _, _) :: _ -> makeRational (-b) a
        | (pp, l, h) :: _ -> LispAlgebraic (pp, l, h)   // Шаг 18: примитивный многочлен
        | [] -> LispAlgebraic (p, lo, hi)

// Упрощение: степень 1 → рациональное (совместимое имя)
let simplifyAlgebraic (poly: bigint list) (lo: bigint * bigint) (hi: bigint * bigint) : LispValue =
    makeResult poly lo hi

// Отрицание: p(-x), интервал (-hi, -lo)
let algNeg (v: LispValue) : LispValue =
    match v with
    | LispAlgebraic (poly, (loN, loD), (hiN, hiD)) ->
        let negPoly = normalize (poly |> List.mapi (fun i c -> if (poly.Length - 1 - i) % 2 = 0 then c else -c))
        let negLo = ratNorm (-hiN, hiD)
        let negHi = ratNorm (-loN, loD)
        makeResult negPoly negLo negHi
    | LispInteger n -> LispInteger (-n)
    | LispRational (p, q) -> LispRational (-p, q)
    | _ -> failwith "alg-neg: не алгебраическое число"

// Сложение: a — корень p, b — корень q; s = a+b — корень Res_y(p(y), q(s-y))
let algAddRaw (a: LispValue) (b: LispValue) : LispValue =
    // смешение с float → обычная плавающая арифметика
    match a, b with
    | LispFloat _, _ | _, LispFloat _ -> Numeric.add a b
    | _ ->
        let ok = function LispInteger _ | LispRational _ -> true | _ -> false
        if ok a && ok b then Numeric.add a b
        else
            // сужаем интервалы операндов, чтобы границы результата изолировали нужный корень
            let (p, alo0, ahi0) = promoteAlg a
            let (q, blo0, bhi0) = promoteAlg b
            let alo, ahi = refineN p alo0 ahi0 32
            let blo, bhi = refineN q blo0 bhi0 32
            let s = bivariateResultant p q substForAdd
            let lo = ratAdd alo blo
            let hi = ratAdd ahi bhi
            makeResult s lo hi

// Умножение: a — корень p, b — корень q; s = a*b — корень Res_y(p(y), y^n q(s/y))
let algMulRaw (a: LispValue) (b: LispValue) : LispValue =
    match a, b with
    | LispFloat _, _ | _, LispFloat _ -> Numeric.mul a b
    | _ ->
        let ok = function LispInteger _ | LispRational _ -> true | _ -> false
        if ok a && ok b then Numeric.mul a b
        else
            // сужаем интервалы операндов, чтобы границы результата изолировали нужный корень
            let (p, alo0, ahi0) = promoteAlg a
            let (q, blo0, bhi0) = promoteAlg b
            let alo, ahi = refineN p alo0 ahi0 32
            let blo, bhi = refineN q blo0 bhi0 32
            let s = bivariateResultant p q substForMul
            // интервал произведения: min/max из четырёх попарных произведений границ
            let prods = [ ratMul alo blo; ratMul alo bhi; ratMul ahi blo; ratMul ahi bhi ]
            let lo = prods |> List.reduce (fun x y -> if ratCompare x y <= 0 then x else y)
            let hi = prods |> List.reduce (fun x y -> if ratCompare x y >= 0 then x else y)
            makeResult s lo hi

// Вычитание: a + (-b)
let algSubRaw (a: LispValue) (b: LispValue) : LispValue =
    let ok = function LispInteger _ | LispRational _ -> true | _ -> false
    if ok a && ok b then Numeric.sub a b
    else algAddRaw a (algNeg b)

// --- Сравнение алгебраических чисел ---

// Сравнение: -1 (a<b), 0 (a=b), 1 (a>b)
let algCompare (a: LispValue) (b: LispValue) : int =
    let ok = function LispInteger _ | LispRational _ -> true | _ -> false
    if ok a && ok b then Numeric.compareNum a b
    else
        let (pa, alo, ahi) = promoteAlg a
        let (pb, blo, bhi) = promoteAlg b
        if ratCompare ahi blo < 0 then -1                  // a < b: интервалы разошлись
        elif ratCompare alo bhi > 0 then 1                 // a > b
        elif pa = pb && ratCompare alo blo = 0 && ratCompare ahi bhi = 0 then 0
        elif pa = pb && ratCompare alo blo >= 0 && ratCompare ahi bhi <= 0 then 0
        elif pa = pb && ratCompare blo alo >= 0 && ratCompare bhi ahi <= 0 then 0
        else
            // интервалы пересекаются — уточняем бисекцией, пока не разойдутся
            let rec refineStep (lo1, hi1) (lo2, hi2) depth =
                if depth > 300 then 0
                else
                    let a1, b1 = refineInterval pa lo1 hi1
                    let a2, b2 = refineInterval pb lo2 hi2
                    if ratCompare b1 a2 < 0 then -1
                    elif ratCompare a1 b2 > 0 then 1
                    else refineStep (a1, b1) (a2, b2) (depth + 1)
            refineStep (alo, ahi) (blo, bhi) 0

// Уточнение: несколько шагов бисекции
let algRefine (v: LispValue) : LispValue =
    match v with
    | LispAlgebraic (poly, lo, hi) ->
        let rec loop l h k =
            if k = 0 then (l, h)
            else
                let l', h' = refineInterval poly l h
                loop l' h' (k - 1)
        let lo', hi' = loop lo hi 5
        LispAlgebraic (poly, lo', hi')
    | _ -> failwith "alg-refine: не алгебраическое число"

// Предикат
let isAlgebraic (v: LispValue) : bool =
    match v with
    | LispAlgebraic _ -> true
    | _ -> false
