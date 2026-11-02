// Рациональные функции (Шаг 17, коммит 3): together, cancel, numer/denom, apart и прочий пользовательский API
// на выражениях. Все операции — явные команды (как Together/Cancel/Apart в Mathematica);
// simplify автоматически дроби НЕ сокращает.
module RatFun

open System.Numerics
open Types
open Numeric
open MPoly
open PolyGcd
open PolyExpr

// Нормированная пара (знаменатель — целый примитивный) → «красивая» пара: целые коэффициенты
// и в числителе, и в знаменателе; рациональный множитель a/b = u/v распределён: числитель u·np, знаменатель v·dp
let private display ((n, d): MPoly * MPoly) : MPoly * MPoly =
    if isZero n then (zero, one)
    else
        let ((u, v), np) = primitiveInt n
        (mulConst (u, 1I) np, mulConst (v, 1I) d)

let private fracExpr (ctx: Ctx) (p: MPoly * MPoly) : LispValue = ratFunToExpr ctx (display p)

// Выражение → контекст + нормированная рациональная функция
let private analyze (e: LispValue) : LispValue * Ctx * (MPoly * MPoly) =
    let simp = Simplify.simplify e
    let ctx = makeCtx [simp] []
    (simp, ctx, toRatFun ctx simp)

// together: одна дробь с общим знаменателем, сокращённая на НОД; числитель и знаменатель раскрыты
let together (e: LispValue) : LispValue =
    let (simp, ctx, frac) = analyze e
    if ctx.Vars.Length = 0 then simp else fracExpr ctx frac

// cancel: сокращение дробей на НОД БЕЗ приведения слагаемых к общему знаменателю
// (сумма обрабатывается почленно, как Cancel в Mathematica)
let cancel (e: LispValue) : LispValue =
    let one (t: LispValue) : LispValue =
        let ctx = makeCtx [t] []
        if ctx.Vars.Length = 0 then t else fracExpr ctx (toRatFun ctx t)
    match Simplify.simplify e with
    | LispList (LispSym "+" :: terms) -> Simplify.simplify (LispList (LispSym "+" :: List.map one terms))
    | simp -> one simp

// numer / denom — числитель и знаменатель together-формы
let numer (e: LispValue) : LispValue =
    let (simp, ctx, frac) = analyze e
    if ctx.Vars.Length = 0 then (match simp with LispRational (p, _) -> LispInteger p | _ -> simp)
    else toExpr ctx (fst (display frac))

let denom (e: LispValue) : LispValue =
    let (simp, ctx, frac) = analyze e
    if ctx.Vars.Length = 0 then (match simp with LispRational (_, q) -> LispInteger q | _ -> LispInteger 1I)
    else toExpr ctx (snd (display frac))

// --- apart ---

// Деление с остатком по главной переменной (x главная; делитель — с рациональными старшим коэффициентом).
// Возвращает точные (частное, остаток)
let private divModX (a: MPoly) (b: MPoly) : MPoly * MPoly =
    let (q, r, e) = pseudoDivMod a b
    if e = 0 then (zero, a)
    else
        let lcb = lcMain b
        match lcb with
        | Const (n, d) ->
            let inv = ratDiv (1I, 1I) (ratNorm (BigInteger.Pow(n, e), BigInteger.Pow(d, e)))
            (mulConst inv q, mulConst inv r)
        | _ -> failwith "apart: старший коэффициент делителя не число"

// Расширенный Евклид в ℚ[x]: (g, s, t), s·a + t·b = g
let private extGcdX (a: MPoly) (b: MPoly) : MPoly * MPoly * MPoly =
    let mutable r0, r1 = a, b
    let mutable s0, s1 = one, zero
    let mutable t0, t1 = zero, one
    while not (isZero r1) do
        let (q, r2) = divModX r0 r1
        r0 <- r1
        r1 <- r2
        let s2 = sub s0 (mul q s1)
        s0 <- s1
        s1 <- s2
        let t2 = sub t0 (mul q t1)
        t0 <- t1
        t1 <- t2
    (r0, s0, t0)

// Простейшие дроби по x над ℚ. Знаменатель раскладывается над ℤ; множители без x и параметры
// выносятся как общий множитель-знаменатель. Если среди x-зависимых множителей знаменателя есть
// многомерные (с параметрами) — возвращается together-форма (простейшие дроби с параметрами в знаменателе не строим)
let apart (e: LispValue) (x: LispValue) : LispValue =
    let simp = Simplify.simplify e
    let xs = Simplify.simplify x
    let ctx = makeCtx [simp] [xs]
    let xi = varIndex ctx xs
    let (n, d) = toRatFun ctx simp
    if degIn xi d = 0 then simp
    else
        let (_, dfs) = PolyFactor.factorPoly d
        let free, dep = dfs |> List.partition (fun (f, _) -> degIn xi f = 0)
        let univariate = dep |> List.forall (fun (f, _) -> mainVar f = xi && (match f with Poly (_, cs) -> cs |> Array.forall isConst | _ -> false))
        if not univariate then fracExpr ctx (n, d)
        else
            let d0 = free |> List.fold (fun acc (f, e) -> mul acc (pow f e)) one
            let qs = dep |> List.map (fun (p, e) -> (p, e, pow p e))
            let dpoly = qs |> List.fold (fun acc (_, _, q) -> mul acc q) one
            // d содержит и рациональный множитель? d нормирован (примитивен) — константы нет
            let (quot, rem) = divModX n dpoly
            let terms = ResizeArray<LispValue>()
            let scaleBy (t: LispValue) : LispValue =
                if isOne d0 then t
                else Simplify.simplify (LispList [LispSym "*"; t; LispList [LispSym "^"; toExpr ctx d0; LispInteger -1I]])
            if not (isZero quot) then terms.Add (scaleBy (toExpr ctx quot))
            for (p, e, q) in qs do
                let m = qs |> List.filter (fun (_, _, q2) -> q2 <> q) |> List.fold (fun acc (_, _, q2) -> mul acc q2) one
                let a =
                    if isOne m then snd (divModX rem q)
                    else
                        let (g, s, _) = extGcdX m q
                        let sn = mulConst (ratDiv (1I, 1I) (leadConst g)) s
                        snd (divModX (mul rem sn) q)
                // p-адическое разложение: a / p^e = Σ B_j / p^(e-j)
                let mutable cur = a
                for j in 0 .. e - 1 do
                    let (q2, b) = divModX cur p
                    if not (isZero b) then
                        let den = LispList [LispSym "^"; toExpr ctx p; LispInteger (BigInteger (-(e - j)))]
                        terms.Add (scaleBy (Simplify.simplify (LispList [LispSym "*"; toExpr ctx b; den])))
                    cur <- q2
            if terms.Count = 0 then LispInteger 0I
            else Simplify.simplify (LispList (LispSym "+" :: List.ofSeq terms))

// --- прочее ---

let private polyOf (who: string) (ctx: Ctx) (e: LispValue) : MPoly =
    match toPoly ctx e with
    | Some p -> p
    | None -> failwithf "%s: ожидается многочлен" who

// НОД и НОК многочленов (нормированные: целые взаимно простые коэффициенты, положительный старший)
let polyGcd (a: LispValue) (b: LispValue) : LispValue =
    let ctx = makeCtx [a; b] []
    toExpr ctx (gcd (polyOf "poly-gcd" ctx a) (polyOf "poly-gcd" ctx b))

let polyLcm (a: LispValue) (b: LispValue) : LispValue =
    let ctx = makeCtx [a; b] []
    toExpr ctx (lcm (polyOf "poly-lcm" ctx a) (polyOf "poly-lcm" ctx b))

// Частное и остаток от деления a на b по переменной x (над полем рациональных функций от остальных переменных)
let private quotRem (who: string) (a: LispValue) (b: LispValue) (x: LispValue) : Ctx * (MPoly * MPoly) * (MPoly * MPoly) =
    let ctx = makeCtx [a; b] [x]
    let pa, pb = polyOf who ctx a, polyOf who ctx b
    if isZero pb then failwithf "%s: деление на нуль" who
    let (q, r, e) = pseudoDivMod pa pb
    if e = 0 then (ctx, (zero, one), (pa, one))
    else
        let den = pow (lcMain pb) e
        (ctx, normalizeFrac (q, den), normalizeFrac (r, den))

let polyQuotient (a: LispValue) (b: LispValue) (x: LispValue) : LispValue =
    let (ctx, q, _) = quotRem "poly-quotient" a b (Simplify.simplify x)
    fracExpr ctx q

let polyRemainder (a: LispValue) (b: LispValue) (x: LispValue) : LispValue =
    let (ctx, _, r) = quotRem "poly-remainder" a b (Simplify.simplify x)
    fracExpr ctx r

// Коэффициент при x^n
let coeff (e: LispValue) (x: LispValue) (n: int) : LispValue =
    let xs = Simplify.simplify x
    let ctx = makeCtx [e] [xs]
    let p = polyOf "coeff" ctx e
    toExpr ctx (coeffIn (varIndex ctx xs) n p)

// Степень по x: многочлен — степень; рациональная функция — степень числителя минус знаменателя;
// нулевой многочлен — символ -inf
let degree (e: LispValue) (x: LispValue) : LispValue =
    let xs = Simplify.simplify x
    let ctx = makeCtx [e] [xs]
    let xi = varIndex ctx xs
    let (n, d) = toRatFun ctx (Simplify.simplify e)
    if isZero n then LispSym "-inf"
    else LispInteger (BigInteger (degIn xi n - degIn xi d))

// Переменные (символы и ядра) выражения в каноническом порядке
let variables (e: LispValue) : LispValue =
    LispList (kernelsOf e |> List.sortWith Order.orderCompare)

let isPoly (e: LispValue) : bool =
    let ctx = makeCtx [e] []
    (toPoly ctx e).IsSome

// Многочлен ли e по x (остальные переменные — параметры, в том числе в знаменателях)
let isPolynomialIn (e: LispValue) (x: LispValue) : bool =
    let xs = Simplify.simplify x
    let simp = Simplify.simplify e
    let ctx = makeCtx [simp] [xs]
    let xi = varIndex ctx xs
    let rec contains (k: LispValue) : bool =
        structEqual k xs || (match k with LispList items -> List.exists contains items | _ -> false)
    let hidden = ctx.Vars |> Array.exists (fun k -> not (structEqual k xs) && contains k)
    not hidden && (let (_, d) = toRatFun ctx simp in degIn xi d = 0)
