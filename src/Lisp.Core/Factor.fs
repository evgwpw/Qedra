// Факторизация (factor) — Шаг 17: полное разложение рациональной функции на неприводимые
// множители над ℤ (см. PolyFactor.fs); до шага 17 здесь было только вынесение общего множителя.
// Шаг 21h': сюда перенесены factorExpr / sqfreeExpr (мост «выражение ↔ многочлен»); чистая алгебра — PolyFactor.fs
module Factor

open System.Numerics
open Types
open Numeric
open MPoly
open PolyGcd
open PolyExpr
open PolyFactor

// Выражение из константы и множителей (числитель с положительными, знаменатель с отрицательными степенями)
let private build (ctx: Ctx) (c: Q) (num: (MPoly * int) list) (den: (MPoly * int) list) : LispValue =
    if ratIsZero c then LispInteger 0I
    else
        let item (f: MPoly, e: int) =
            let fe = toExpr ctx f
            if e = 1 then fe else LispList [LispSym "^"; fe; LispInteger (BigInteger e)]
        let denItem (f: MPoly, e: int) =
            LispList [LispSym "^"; toExpr ctx f; LispInteger (BigInteger (-e))]
        let items =
            (if ratCompare c (1I, 1I) = 0 then [] else [ratToValue c])
            @ (num |> List.map item) @ (den |> List.map denItem)
        match items with
        | [] -> LispInteger 1I
        | [single] -> single
        | _ -> Simplify.simplify (LispList (LispSym "*" :: items))

// Новый factor: рациональная функция от символов и ядер → число × Π неприводимых^степени
let factorExpr (e: LispValue) : LispValue =
    let simp = Simplify.simplify e
    let ctx = makeCtx [simp] []
    if ctx.Vars.Length = 0 then simp
    else
        let (c, num, den) = factorRatFun (toRatFun ctx simp)
        build ctx c num den

// Бесквадратная форма выражения: c · Π a_i^i
let sqfreeExpr (e: LispValue) : LispValue =
    let simp = Simplify.simplify e
    let ctx = makeCtx [simp] []
    if ctx.Vars.Length = 0 then simp
    else
        let (n, d) = normalizeFrac (toRatFun ctx simp)
        let (cn, fn) = sqfreePoly n
        let (cd, fd) = sqfreePoly d
        build ctx (ratDiv cn cd) fn fd

// Рациональная функция от символов и ядер → число × Π неприводимых множителей в степенях
// (знаменатель — в отрицательных степенях). Порядок множителей — канонический (simplify).
// Примеры: (+ (* 2 x) (* 2 y)) → (* 2 (+ x y)); (^ x 4) - 1 → (* (+ -1 x) (+ 1 x) (+ 1 (^ x 2)))
let factor (expr: LispValue) : LispValue = factorExpr expr
