// Вычислительные примитивы для solve (Шаг 18, коммит 1): subst, resultant, nroots, real-roots, factor-list.
// Высокоуровневая логика solve — на Lisp (lib\solve.lisp); здесь только то, что на Lisp было бы слишком медленно.
module SolveNum

open System
open System.Numerics
open Types
open Numeric
open Builtins
open MPoly
open PolyGcd
open PolyExpr
open Subresultant
open NumRoots

// Шаг 21h': вычислительные ядра (результант MPoly — Subresultant, метод Аберта/уточнение корней — NumRoots,
// точная сумма по корням — RatInt.exactRootSumQ) живут в Cas.Algebra; здесь — разбор выражений и builtins

// --- subst: одновременная подстановка значений вместо символов ---

// Правила: (= x v) | (x v) | список таких → [(имя, значение)]
let private parseRules (rules: LispValue) : (string * LispValue) list =
    let one (r: LispValue) : string * LispValue =
        match r with
        | LispList [LispSym "="; LispSym x; v] -> (x, v)
        | LispList [LispSym x; v] -> (x, v)
        | _ -> failwith "subst: правило — (= x значение) или (x значение); подставлять можно только символы"
    match rules with
    | LispNil -> []
    | LispList [] -> []
    | LispList (LispSym _ :: _) -> [one rules]      // одиночное правило
    | LispList rs -> rs |> List.map one
    | _ -> failwith "subst: правила — (= x значение), список правил или пары (x значение)"

// (subst правила выражение): все вхождения символов заменяются одновременно (значения повторно не
// подставляются), затем выражение упрощается. Голова формы (имя функции) не заменяется; ядра ((sin x)
// целиком) подставить нельзя — только символы
let subst (rules: LispValue) (e: LispValue) : LispValue =
    let rs = parseRules rules
    let rec go (v: LispValue) : LispValue =
        match v with
        | LispSym s ->
            match rs |> List.tryFind (fun (n, _) -> n = s) with
            | Some (_, value) -> value
            | None -> v
        // Шаг 21h: связанная переменная суммы по корням не подставляется (без захвата)
        | LispList [LispSym "root-sum"; LispSym _; _; _] -> RootSum.substFree rs v
        | LispList (head :: args) ->
            let h = match head with LispSym _ -> head | _ -> go head
            LispList (h :: List.map go args)
        | LispVector items -> LispVector (Array.map go items)
        | _ -> v
    Simplify.simplify (go e)

// --- вспомогательное: выражение → многочлен ---

let private polyOfExpr (who: string) (ctx: Ctx) (e: LispValue) : MPoly =
    match toPoly ctx e with
    | Some p -> p
    | None -> failwithf "%s: ожидается многочлен" who

// --- resultant ---

// Результант многочленов (матрица Сильвестра, Барейс) — Subresultant.resultantPoly

// (resultant p q x) — результант по x (коэффициенты — многочлены от остальных переменных)
let resultant (p: LispValue) (q: LispValue) (x: LispValue) : LispValue =
    let xs = Simplify.simplify x
    let ctx = makeCtx [p; q] [xs]
    let xi = varIndex ctx xs
    let pa, pb = polyOfExpr "resultant" ctx p, polyOfExpr "resultant" ctx q
    toExpr ctx (resultantPoly xi pa pb)

// --- factor-list: (c (f1 e1) (f2 e2) ...) ---

// Разложение многочлена над ℤ списком: рациональная константа и неприводимые множители с кратностями
let factorList (e: LispValue) : LispValue =
    let simp = Simplify.simplify e
    let ctx = makeCtx [simp] []
    if ctx.Vars.Length = 0 then
        LispList [simp]
    else
        let (n, d) = toRatFun ctx simp
        if not (isOne d) then failwith "factor-list: ожидается многочлен (знаменатель не константа)"
        let (c, fs) = PolyFactor.factorPoly n
        LispList (ratToValue c :: (fs |> List.map (fun (f, k) -> LispList [toExpr ctx f; LispInteger (BigInteger k)])))

// --- real-roots: действительные корни многочлена с рациональными коэффициентами ---

// Корни: рациональные (линейные множители) и алгебраические числа (корни неприводимых множителей степени >= 2),
// по возрастанию. Многочлен должен зависеть только от x
let realRoots (e: LispValue) (x: LispValue) : LispValue =
    let xs = Simplify.simplify x
    let simp = Simplify.simplify e
    let ctx = makeCtx [simp] [xs]
    let xi = varIndex ctx xs
    if ctx.Vars.Length <> 1 then failwith "real-roots: ожидается многочлен только от x с рациональными коэффициентами"
    let p = polyOfExpr "real-roots" ctx simp
    if isZero p then failwith "real-roots: нулевой многочлен"
    let (_, fs) = PolyFactor.factorPoly p
    let roots =
        fs |> List.collect (fun (f, _) ->
            match f with
            | Poly (_, cs) ->
                let zs = cs |> Array.map (fun c -> match c with Const (n, dd) when dd.IsOne -> n | _ -> failwith "real-roots: внутренняя ошибка")
                if zs.Length = 2 then [makeRational (-zs.[0]) zs.[1]]
                else
                    let desc = zs |> Array.rev |> List.ofArray
                    Sturm.isolateRoots desc |> List.map (fun (pl, lo, hi) -> LispAlgebraic (pl, lo, hi))
            | Const _ -> [])
    ignore xi
    LispList (roots |> List.sortWith Algebraic.algCompare)

// --- nroots: все комплексные корни численно (метод Аберта) ---

// Выражение → вещественные коэффициенты по возрастанию степени (рациональные, целые, float)
let private doubleCoeffs (e: LispValue) (x: LispValue) : double[] =
    let rec go (v: LispValue) : double[] =
        match v with
        | _ when structEqual v x -> [| 0.0; 1.0 |]
        | LispInteger _ | LispRational _ | LispFloat _ -> [| toDouble v |]
        | LispList (LispSym "+" :: args) -> args |> List.map go |> List.fold padd [| 0.0 |]
        | LispList (LispSym "*" :: args) -> args |> List.map go |> List.fold pmul [| 1.0 |]
        | LispList [LispSym "^"; b; LispInteger n] when n.Sign >= 0 && n <= 10000I ->
            let pb = go b
            let mutable acc = [| 1.0 |]
            for _ in 1 .. int n do acc <- pmul acc pb
            acc
        | _ -> failwith "nroots: ожидается многочлен от x с числовыми коэффициентами"
    let cs = go (Simplify.simplify e)
    // убрать старшие нули
    let mutable n = cs.Length
    while n > 1 && cs.[n - 1] = 0.0 do n <- n - 1
    Array.sub cs 0 n

// Метод Аберта, корни по коэффициентам и уточнение — NumRoots (Cas.Algebra)
// (nroots p x) — все комплексные корни: вещественные — float, комплексные — (+ re (* im %i)) с float-частями;
// по возрастанию (re, im). Кратные корни находятся с пониженной точностью (~ eps^(1/кратность))

// Целые коэффициенты многочлена (по возрастанию степени), если все числа в выражении рациональны; иначе None
let private exactCoeffs (e: LispValue) (x: LispValue) : BigInteger[] option =
    let zeroQ = (0I, 1I)
    let radd (a: Q[]) (b: Q[]) : Q[] =
        Array.init (max a.Length b.Length) (fun i ->
            ratAdd (if i < a.Length then a.[i] else zeroQ) (if i < b.Length then b.[i] else zeroQ))
    let rmul (a: Q[]) (b: Q[]) : Q[] =
        let r = Array.create (a.Length + b.Length - 1) zeroQ
        for i in 0 .. a.Length - 1 do
            for j in 0 .. b.Length - 1 do
                r.[i + j] <- ratAdd r.[i + j] (ratMul a.[i] b.[j])
        r
    let rec go (v: LispValue) : Q[] =
        match v with
        | _ when structEqual v x -> [| zeroQ; (1I, 1I) |]
        | LispInteger n -> [| (n, 1I) |]
        | LispRational (p, q) -> [| ratNorm (p, q) |]
        | LispList (LispSym "+" :: args) -> args |> List.map go |> List.fold radd [| zeroQ |]
        | LispList (LispSym "*" :: args) -> args |> List.map go |> List.fold rmul [| (1I, 1I) |]
        | LispList [LispSym "^"; b; LispInteger n] when n.Sign >= 0 && n <= 200I ->
            let pb = go b
            let mutable acc = [| (1I, 1I) |]
            for _ in 1 .. int n do acc <- rmul acc pb
            acc
        | _ -> failwith "не рациональный многочлен"
    try
        let cs = go (Simplify.simplify e)
        let mutable n = cs.Length
        while n > 1 && ratIsZero cs.[n - 1] do n <- n - 1
        let cs = Array.sub cs 0 n
        let l = cs |> Array.fold (fun acc (_, d) -> acc / BigInteger.GreatestCommonDivisor(acc, d) * d) 1I
        Some (cs |> Array.map (fun (p, d) -> p * (l / d)))
    with _ -> None

let nroots (e: LispValue) (x: LispValue) : LispValue =
    let cs = doubleCoeffs e (Simplify.simplify x)
    if cs.Length = 1 && cs.[0] = 0.0 then failwith "nroots: нулевой многочлен"
    let all = rootsOfCoeffs cs
    let isReal (z: Complex) = abs z.Imaginary <= 1e-7 * (1.0 + Complex.Abs z)
    let cleaned =
        all |> List.map (fun z -> if isReal z then Complex(z.Real, 0.0) else z)
        |> List.sortWith (fun a b -> if a.Real <> b.Real then compare a.Real b.Real else compare a.Imaginary b.Imaginary)
    LispList (cleaned |> List.map (fun z ->
        if z.Imaginary = 0.0 then LispFloat z.Real
        else
            let im = LispList [LispSym "*"; LispFloat z.Imaginary; LispSym "%i"]
            if z.Real = 0.0 then im else LispList [LispSym "+"; LispFloat z.Real; im]))

// --- eval-num: численное значение выражения без свободных символов (для проверки решений) ---

// Алгебраическое число → double (середина интервала после бисекции)
let private algToComplex (p: bigint list) lo hi : Complex =
    let (l, h) = Sturm.refineN p lo hi 80
    let d ((n: bigint), (dd: bigint)) = double n / double dd
    Complex((d l + d h) / 2.0, 0.0)

// Численное значение (главные ветви функций); None — есть свободные символы или неизвестные функции.
// Деление на нуль даёт бесконечность/NaN (вызывающий отбрасывает нефинитные значения)
// Степень комплексного числа с целым показателем — NumRoots.ipow; double → точное рациональное — NumRoots.ratOfDouble

// ТОЧНОЕ значение Σ_{Q(α)=0} E(α), если Q — многочлен, а E — рациональная функция от t с рациональными (в том числе float —
// как точные двоичные дроби) коэффициентами и без других символов: φ = E mod Q в ℚ[t]/(Q), след — степенные суммы корней Q
// (RatInt.traceMod). Вещественная арифметика для сумм с большими разнородными слагаемыми (вычеты ~10^6 при сумме ~1) теряет
// точность; точное значение — рациональное число, затем одно округление до double
let private exactRootSum (qe: LispValue) (tv: string) (body: LispValue) : Q option =
    let zeroQ, oneQ = (0I, 1I), (1I, 1I)
    let padd (a: Q[]) (b: Q[]) : Q[] =
        Array.init (max a.Length b.Length) (fun i ->
            ratAdd (if i < a.Length then a.[i] else zeroQ) (if i < b.Length then b.[i] else zeroQ))
    let pmul (a: Q[]) (b: Q[]) : Q[] =
        let r = Array.create (a.Length + b.Length - 1) zeroQ
        for i in 0 .. a.Length - 1 do
            for j in 0 .. b.Length - 1 do
                r.[i + j] <- ratAdd r.[i + j] (ratMul a.[i] b.[j])
        r
    let ppow (a: Q[]) (n: int) : Q[] =
        let mutable acc = [| oneQ |]
        for _ in 1 .. n do acc <- pmul acc a
        acc
    let rec rf (v: LispValue) : Q[] * Q[] =
        match v with
        | LispSym s when s = tv -> ([| zeroQ; oneQ |], [| oneQ |])
        | LispInteger n -> ([| (n, 1I) |], [| oneQ |])
        | LispRational (p, q) -> ([| ratNorm (p, q) |], [| oneQ |])
        | LispFloat f when not (Double.IsNaN f || Double.IsInfinity f) -> ([| ratOfDouble f |], [| oneQ |])
        | LispList (LispSym "+" :: args) ->
            args |> List.map rf |> List.fold (fun (n1, d1) (n2, d2) -> (padd (pmul n1 d2) (pmul n2 d1), pmul d1 d2)) ([| zeroQ |], [| oneQ |])
        | LispList (LispSym "*" :: args) ->
            args |> List.map rf |> List.fold (fun (n1, d1) (n2, d2) -> (pmul n1 n2, pmul d1 d2)) ([| oneQ |], [| oneQ |])
        | LispList [LispSym "/"; a; b] ->
            let (na, da), (nb, db) = rf a, rf b
            (pmul na db, pmul da nb)
        | LispList [LispSym "-"; a] ->
            let (na, da) = rf a
            (pmul na [| (-1I, 1I) |], da)
        | LispList (LispSym "-" :: a :: rest) when not rest.IsEmpty ->
            let (n1, d1) = rf a
            rest |> List.map rf |> List.fold (fun (n, d) (n2, d2) -> (padd (pmul n d2) (pmul (pmul n2 [| (-1I, 1I) |]) d), pmul d d2)) (n1, d1)
        | LispList [LispSym "^"; b; LispInteger n] when BigInteger.Abs n <= 200I ->
            let (nb, db) = rf b
            let k = int (BigInteger.Abs n)
            if n.Sign >= 0 then (ppow nb k, ppow db k) else (ppow db k, ppow nb k)
        | _ -> failwith "не рациональная функция"
    try
        // без Simplify: свёртка float внесла бы погрешность во входные коэффициенты (при плохой обусловленности суммы — шум)
        let (qn, qd) = rf qe
        if qd.Length <> 1 then None
        else
            let (nn, dd) = rf body
            Outcome.toOption (RatInt.exactRootSumQ qn nn dd)
    with _ -> None

// Подстановка числовых значений в многочлен Q суммы по корням: pi и вещественные связанные переменные внешних сумм
let rec private subNum (env: Map<string, Complex>) (v: LispValue) : LispValue =
    match v with
    | LispSym "pi" -> LispFloat Math.PI
    | LispSym s when env.ContainsKey s && env.[s].Imaginary = 0.0 -> LispFloat env.[s].Real
    | LispList items -> LispList (List.map (subNum env) items)
    | _ -> v

// env — значения связанных переменных (Шаг 21h: связанная переменная суммы по корням принимает значения корней)
// --- A3′.3: эллиптические интегралы Лежандра (Карлсон RF/RD, double) ---
// RF(x,y,z) — дупляция Карлсона; RD(x,y,z) — интеграл второго рода (Numerical Recipes).
let private carlsonRf (x0: float) (y0: float) (z0: float) : float =
    let errtol = 2.5e-3
    let mutable x = x0
    let mutable y = y0
    let mutable z = z0
    let mutable eps = 1.0
    let mutable delx = 0.0
    let mutable dely = 0.0
    let mutable delz = 0.0
    while eps > errtol do
        let mu = (x + y + z) / 3.0
        delx <- 1.0 - x / mu
        dely <- 1.0 - y / mu
        delz <- 1.0 - z / mu
        eps <- max (abs delx) (max (abs dely) (abs delz))
        if eps > errtol then
            let sx = sqrt x
            let sy = sqrt y
            let sz = sqrt z
            let lam = sx * sy + sx * sz + sy * sz
            x <- (x + lam) / 4.0
            y <- (y + lam) / 4.0
            z <- (z + lam) / 4.0
    let e2 = delx * dely - delz * delz
    let e3 = delx * dely * delz
    (1.0 - e2 / 10.0 + e3 / 14.0 + e2 * e2 / 24.0 - 3.0 * e2 * e3 / 44.0) / sqrt ((x + y + z) / 3.0)

let private carlsonRd (x0: float) (y0: float) (z0: float) : float =
    let errtol = 2.5e-3
    let mutable x = x0
    let mutable y = y0
    let mutable z = z0
    let mutable sum = 0.0
    let mutable fac = 1.0
    let mutable eps = 1.0
    let mutable ave = 0.0
    let mutable delx = 0.0
    let mutable dely = 0.0
    let mutable delz = 0.0
    while eps > errtol do
        ave <- (x + y + 3.0 * z) / 5.0
        delx <- 1.0 - x / ave
        dely <- 1.0 - y / ave
        delz <- 1.0 - z / ave
        eps <- max (abs delx) (max (abs dely) (abs delz))
        if eps > errtol then
            let sx = sqrt x
            let sy = sqrt y
            let sz = sqrt z
            let lam = sx * sy + sy * sz + sz * sx
            sum <- sum + fac / (sz * (z + lam))
            fac <- fac / 4.0
            x <- (x + lam) / 4.0
            y <- (y + lam) / 4.0
            z <- (z + lam) / 4.0
    let ea = delx * dely
    let eb = delz * delz
    let ec = ea - eb
    let ed = ea - 6.0 * eb
    let ee = ed + ec + ec
    3.0 * sum + fac * (1.0 + ed * (-3.0 / 14.0 + 9.0 / 88.0 * ed - 9.0 / 52.0 * delz * ee)
                        + delz * (ee / 6.0 + delz * (-9.0 / 22.0 * ec + delz * 3.0 / 26.0 * ea))) / (ave * sqrt ave)

// Π(n; φ, k) — квадратура Симпсона по определению (для одного численного значения)
let private ellipticPiNum (n: float) (phi: float) (k: float) : float =
    let f t = 1.0 / ((1.0 - n * sin t * sin t) * sqrt (1.0 - k * k * sin t * sin t))
    let m = 2000
    let h = phi / float m
    let mutable s = f 0.0 + f phi
    for i in 1 .. m - 1 do
        s <- s + (if i % 2 = 1 then 4.0 else 2.0) * f (float i * h)
    s * h / 3.0

// Комплексные RF/RD (A3′.3: кубика x³+1 требует комплексного модуля Лежандра)
let private cN (x: float) = Complex(x, 0.0)

let private carlsonRfC (x0: Complex) (y0: Complex) (z0: Complex) : Complex =
    let errtol = 2.5e-3
    let mutable x = x0
    let mutable y = y0
    let mutable z = z0
    let mutable eps = 1.0
    let mutable delx = Complex.Zero
    let mutable dely = Complex.Zero
    let mutable delz = Complex.Zero
    while eps > errtol do
        let mu = (x + y + z) / cN 3.0
        delx <- Complex.One - x / mu
        dely <- Complex.One - y / mu
        delz <- Complex.One - z / mu
        eps <- max (Complex.Abs delx) (max (Complex.Abs dely) (Complex.Abs delz))
        if eps > errtol then
            let sx = Complex.Sqrt x
            let sy = Complex.Sqrt y
            let sz = Complex.Sqrt z
            let lam = sx * sy + sx * sz + sy * sz
            x <- (x + lam) / cN 4.0
            y <- (y + lam) / cN 4.0
            z <- (z + lam) / cN 4.0
    let e2 = delx * dely - delz * delz
    let e3 = delx * dely * delz
    (Complex.One - e2 / cN 10.0 + e3 / cN 14.0 + e2 * e2 / cN 24.0 - cN 3.0 * e2 * e3 / cN 44.0)
    / Complex.Sqrt ((x + y + z) / cN 3.0)

let private carlsonRdC (x0: Complex) (y0: Complex) (z0: Complex) : Complex =
    let errtol = 2.5e-3
    let mutable x = x0
    let mutable y = y0
    let mutable z = z0
    let mutable sum = Complex.Zero
    let mutable fac = Complex.One
    let mutable eps = 1.0
    let mutable ave = Complex.Zero
    let mutable delx = Complex.Zero
    let mutable dely = Complex.Zero
    let mutable delz = Complex.Zero
    while eps > errtol do
        ave <- (x + y + cN 3.0 * z) / cN 5.0
        delx <- Complex.One - x / ave
        dely <- Complex.One - y / ave
        delz <- Complex.One - z / ave
        eps <- max (Complex.Abs delx) (max (Complex.Abs dely) (Complex.Abs delz))
        if eps > errtol then
            let sx = Complex.Sqrt x
            let sy = Complex.Sqrt y
            let sz = Complex.Sqrt z
            let lam = sx * sy + sy * sz + sz * sx
            sum <- sum + fac / (sz * (z + lam))
            fac <- fac / cN 4.0
            x <- (x + lam) / cN 4.0
            y <- (y + lam) / cN 4.0
            z <- (z + lam) / cN 4.0
    let ea = delx * dely
    let eb = delz * delz
    let ec = ea - eb
    let ed = ea - cN 6.0 * eb
    let ee = ed + ec + ec
    cN 3.0 * sum + fac * (Complex.One + ed * (cN (-3.0 / 14.0) + cN (9.0 / 88.0) * ed - cN (9.0 / 52.0) * delz * ee)
                          + delz * (ee / cN 6.0 + delz * (cN (-9.0 / 22.0) * ec + delz * cN (3.0 / 26.0) * ea))) / (ave * Complex.Sqrt ave)

// BR.ASIN: asin/acos по Кахану — на разрезах (вещественный |x| > 1) значение согласовано с производной
// 1/(√(1−z)·√(1+z)) из Differentiate.fs: asin z = −i·log(i·z + √(1−z)·√(1+z)), acos z = π/2 − asin z.
// Вне разрезов совпадает с главным значением Complex.Asin (его и используем — точнее у нуля)
let private asinKahan (z: Complex) : Complex =
    if z.Imaginary = 0.0 && abs z.Real > 1.0 then
        let x = z.Real
        let s = Complex.Sqrt (Complex(1.0 - x, 0.0)) * Complex.Sqrt (Complex(1.0 + x, 0.0))
        let l = Complex.Log (Complex(0.0, x) + s)
        Complex(l.Imaginary, -l.Real)
    else Complex.Asin z

let private acosKahan (z: Complex) : Complex =
    if z.Imaginary = 0.0 && abs z.Real > 1.0 then cN (Math.PI / 2.0) - asinKahan z else Complex.Acos z

// результат гиперболической функции: нерегулярный (полюс, ±∞) — не число
let private hypFin (z: Complex) : Complex option =
    if Double.IsFinite z.Real && Double.IsFinite z.Imaginary then Some z else None

// SF.HYP: реестр Lisp-функций численного значения голов — (define-numeric 'голова fn). eval-num вычисляет аргументы,
// вызывает fn (вещественный аргумент — float, комплексный — LispComplex) и принимает число; #f/ошибка — «не вычислено».
// Только для голов, которых нет среди встроенных ветвей ниже (алгоритмы — на Lisp)
let numericHooks = System.Collections.Generic.Dictionary<string, LispValue>()

let private hookNum (fn: LispValue) (a: Complex list) : Complex option =
    let toLisp (z: Complex) =
        if z.Imaginary = 0.0 then LispFloat z.Real else LispComplex (LispFloat z.Real, LispFloat z.Imaginary)
    try
        match Objects.applyHook fn (List.map toLisp a) with
        | LispFloat f -> Some (Complex(f, 0.0))
        | LispInteger n -> Some (Complex(double n, 0.0))
        | LispRational (p, q) -> Some (Complex(double p / double q, 0.0))
        | LispComplex (LispFloat re, LispFloat im) -> Some (Complex(re, im))
        | _ -> None
    with _ -> None

// Шаг PERF.F1: комплексный дилогарифм Li₂(z), главная ветвь, разрез [1, ∞); на самом разрезе — значение «снизу»
// (arg(−x) = +π, как Mathematica: Li₂(2) = π²/4 − iπ·ln 2). Схема (перенос polylog2-cx из lib/polylog.lisp):
// |z| > 1 — инверсия Li₂(z) = −π²/6 − ½ln²(−z) − Li₂(1/z); Re z > ½ — отражение Li₂(z) = π²/6 − ln z·ln(1−z) − Li₂(1−z);
// иначе ряд Бернулли Li₂(z) = Σ Bₙ uⁿ⁺¹/(n+1)!, u = −ln(1−z), |u| < 1,8 (≈ 1e-15 за 40 членов).
let private li2BernCoefs : Lazy<float[]> =
    lazy (
        // Bₙ точно (дроби bigint), B₁ = −½; коэффициент Bₙ/(n+1)!
        let n = 41
        let num : bigint[] = Array.zeroCreate n
        let den : bigint[] = Array.create n 1I
        num.[0] <- 1I
        let binom (m: int) (k: int) =
            let mutable r = 1I
            for i in 1 .. k do r <- r * bigint (m - k + i) / bigint i
            r
        for m in 1 .. n - 1 do
            // Bₘ = −1/(m+1) Σ_{k<m} C(m+1,k) Bₖ
            let mutable sn = 0I
            let mutable sd = 1I
            for k in 0 .. m - 1 do
                let tn = binom (m + 1) k * num.[k]
                let td = den.[k]
                sn <- sn * td + tn * sd
                sd <- sd * td
                let g = BigInteger.GreatestCommonDivisor (sn, sd)
                if not g.IsOne && not g.IsZero then
                    sn <- sn / g
                    sd <- sd / g
            let mutable bn = -sn
            let mutable bd = sd * bigint (m + 1)
            let g = BigInteger.GreatestCommonDivisor (bn, bd)
            if not g.IsOne && not g.IsZero then
                bn <- bn / g
                bd <- bd / g
            num.[m] <- bn
            den.[m] <- bd
        // m = 1 даёт B₁ = −½ (соглашение −)
        Array.init n (fun k ->
            let mutable fact = 1I
            for i in 2 .. k + 1 do fact <- fact * bigint i
            double num.[k] / double (den.[k] * fact)))

let private li2Arg (z: Complex) : float =
    // arg ∈ (−π, π]; на отрицательной вещественной оси +π (−0.0 трактуется как +0.0)
    Math.Atan2 ((if z.Imaginary = 0.0 then 0.0 else z.Imaginary), z.Real)

let private li2Log (z: Complex) : Complex = Complex(Math.Log (Complex.Abs z), li2Arg z)

let rec li2Complex (z: Complex) : Complex =
    let x = z.Real
    let y = z.Imaginary
    let pi2 = Math.PI * Math.PI
    if y = 0.0 && x = 0.0 then Complex.Zero
    elif y = 0.0 && x = 1.0 then Complex(pi2 / 6.0, 0.0)
    elif x * x + y * y > 1.0 then
        let l = li2Log (-z)
        Complex(-pi2 / 6.0, 0.0) - Complex(0.5, 0.0) * l * l - li2Complex (Complex.One / z)
    elif x > 0.5 then
        let om = Complex(1.0 - x, -y)
        Complex(pi2 / 6.0, 0.0) - li2Log z * li2Log om - li2Complex om
    else
        let u = -(li2Log (Complex(1.0 - x, -y)))
        let tb = li2BernCoefs.Value
        let mutable up = u
        let mutable sum = Complex.Zero
        for n in 0 .. 40 do
            sum <- sum + Complex(tb.[n], 0.0) * up
            up <- up * u
        sum

// Шаг INT.SF3: числа Бернулли Bₘ (B₁ = −½), m ≤ 100 — точно (дроби bigint), затем в double
let private bernFloats : Lazy<float[]> =
    lazy (
        let n = 101
        let num : bigint[] = Array.zeroCreate n
        let den : bigint[] = Array.create n 1I
        num.[0] <- 1I
        let binom (m: int) (k: int) =
            let mutable r = 1I
            for i in 1 .. k do r <- r * bigint (m - k + i) / bigint i
            r
        for m in 1 .. n - 1 do
            let mutable sn = 0I
            let mutable sd = 1I
            for k in 0 .. m - 1 do
                let tn = binom (m + 1) k * num.[k]
                let td = den.[k]
                sn <- sn * td + tn * sd
                sd <- sd * td
                let g = BigInteger.GreatestCommonDivisor (sn, sd)
                if not g.IsOne && not g.IsZero then
                    sn <- sn / g
                    sd <- sd / g
            let mutable bn = -sn
            let mutable bd = sd * bigint (m + 1)
            let g = BigInteger.GreatestCommonDivisor (bn, bd)
            if not g.IsOne && not g.IsZero then
                bn <- bn / g
                bd <- bd / g
            num.[m] <- bn
            den.[m] <- bd
        Array.init n (fun k -> double num.[k] / double den.[k]))

// ζ(m), целое m ≥ 2: сумма Эйлера—Маклорена (DLMF 25.2.9) с N = 12 и 10 поправками Бернулли — ≈ 1e-16
let private zetaInt (m: int) : float =
    let nn = 12
    let fm = float m
    let fn = float nn
    let mutable s = 0.0
    for k in 1 .. nn - 1 do s <- s + Math.Pow (float k, -fm)
    s <- s + Math.Pow (fn, 1.0 - fm) / (fm - 1.0) + 0.5 * Math.Pow (fn, -fm)
    let b = bernFloats.Value
    let mutable poch = fm      // m(m+1)…(m+2j−2)
    let mutable fact = 2.0     // (2j)!
    for j in 1 .. 10 do
        let fj = float j
        s <- s + b.[2 * j] / fact * poch * Math.Pow (fn, -fm - 2.0 * fj + 1.0)
        poch <- poch * (fm + 2.0 * fj - 1.0) * (fm + 2.0 * fj)
        fact <- fact * (2.0 * fj + 1.0) * (2.0 * fj + 2.0)
    s

// Шаг INT.SF3: полилогарифм Li_s(z), целое 1 ≤ s ≤ 40, главная ветвь (разрез [1, ∞), на разрезе — значение «снизу»,
// как у Li₂: Li₃(2) = 7ζ(3)/8 + π²ln2/4 − iπ·ln²2/2). Схема:
// |z| ≤ ½ — ряд Σ zᵏ/kˢ (DLMF 25.12.10); ½ < |z| ≤ 1 — разложение по μ = ln z, |μ| < 2π (DLMF 25.12.12):
// Li_s(e^μ) = μ^(s−1)/(s−1)!·[H_(s−1) − ln(−μ)] + Σ_{k≠s−1} ζ(s−k) μᵏ/k!, ζ(−n) = (−1)ⁿ B_(n+1)/(n+1) (DLMF 25.6.3);
// |z| > 1 — инверсия Li_s(z) + (−1)ˢ Li_s(1/z) = −(2πi)ˢ/s!·B_s(½ + ln(−z)/(2πi)) (DLMF 25.12.13 / Crandall).
let private polylogDirect (s: int) (z: Complex) : Complex =
    let mutable zk = z
    let mutable sum = Complex.Zero
    let mutable k = 1
    let mutable go = true
    while go && k <= 200 do
        let add = zk / cN (Math.Pow (float k, float s))
        sum <- sum + add
        if Complex.Abs add < 1e-18 * (Complex.Abs sum + 1e-300) then go <- false
        zk <- zk * z
        k <- k + 1
    sum

let private polylogLogSeries (s: int) (z: Complex) : Complex =
    let mu = li2Log z
    let b = bernFloats.Value
    let mutable h = 0.0
    for j in 1 .. s - 1 do h <- h + 1.0 / float j
    let mutable muPow = Complex.One   // μᵏ/k!
    let mutable sum = Complex.Zero
    for k in 0 .. s + 90 do
        if k > 0 then muPow <- muPow * mu / cN (float k)
        if k = s - 1 then sum <- sum + muPow * (cN h - li2Log (-mu))
        else
            let m = s - k
            let zt =
                if m >= 2 then zetaInt m
                else
                    let nn = -m
                    (if nn % 2 = 0 then 1.0 else -1.0) * b.[nn + 1] / float (nn + 1)
            sum <- sum + cN zt * muPow
    sum

let rec polylogC (s: int) (z: Complex) : Complex option =
    if s < 1 || s > 40 || not (Double.IsFinite z.Real && Double.IsFinite z.Imaginary) then None
    elif z = Complex.Zero then Some Complex.Zero
    elif s = 1 then Some (-(li2Log (Complex.One - z)))
    elif z = Complex.One then Some (cN (zetaInt s))
    else
        let az = Complex.Abs z
        if az <= 0.5 then Some (polylogDirect s z)
        elif az <= 1.0 then Some (polylogLogSeries s z)
        else
            match polylogC s (Complex.One / z) with
            | None -> None
            | Some inv ->
                let b = bernFloats.Value
                let twoPiI = Complex(0.0, 2.0 * Math.PI)
                let x = cN 0.5 + li2Log (-z) / twoPiI
                // B_s(x) = Σ C(s,k) B_k x^(s−k)
                let mutable bp = Complex.Zero
                let mutable binom = 1.0
                for k in 0 .. s do
                    let mutable xp = Complex.One
                    for _ in 1 .. s - k do xp <- xp * x
                    bp <- bp + cN (binom * b.[k]) * xp
                    binom <- binom * float (s - k) / float (k + 1)
                let mutable pre = Complex.One
                for i in 1 .. s do pre <- pre * twoPiI / cN (float i)
                Some ((if s % 2 = 0 then -inv else inv) - pre * bp)

// Шаг INT.SF3: интегралы Френеля C(z) = ∫₀ᶻ cos(πt²/2)dt, S(z) = ∫₀ᶻ sin(πt²/2)dt (нормировка Rubi/Mathematica).
// Ряды (DLMF 7.6.4, 7.6.6): C = Σ (−1)ⁿ(π/2)²ⁿ z⁴ⁿ⁺¹/((2n)!(4n+1)), S = Σ (−1)ⁿ(π/2)²ⁿ⁺¹ z⁴ⁿ⁺³/((2n+1)!(4n+3));
// вещественный |x| ≥ 1,5 — непрерывная дробь для C + iS (DLMF 7.9 / 7.7.?; алгоритм Ленца, Numerical Recipes §6.9)
let private fresnelSeries (z: Complex) : Complex * Complex =
    let h = Math.PI / 2.0
    let w = cN (-(h * h)) * z * z * z * z
    let mutable tc = Complex.One
    let mutable ts = cN h * z * z * z
    let mutable c = z
    let mutable s = ts / cN 3.0
    let mutable n = 0
    let mutable go = true
    while go && n < 300 do
        n <- n + 1
        let fn = float n
        tc <- tc * w / cN ((2.0 * fn - 1.0) * (2.0 * fn))
        ts <- ts * w / cN ((2.0 * fn) * (2.0 * fn + 1.0))
        let ac = tc * z / cN (4.0 * fn + 1.0)
        let asn = ts / cN (4.0 * fn + 3.0)
        c <- c + ac
        s <- s + asn
        if Complex.Abs ac + Complex.Abs asn < 1e-17 * (Complex.Abs c + Complex.Abs s + 1e-300) then go <- false
    (c, s)

let private fresnelCF (ax: float) : float * float =
    let x2 = ax * ax
    let mutable b = Complex(1.0, -Math.PI * x2)
    let mutable c = Complex(1e300, 0.0)
    let mutable d = Complex.One / b
    let mutable h = d
    let mutable n = -1.0
    let mutable k = 2
    let mutable go = true
    while go && k < 2000 do
        n <- n + 2.0
        let a = -n * (n + 1.0)
        b <- b + cN 4.0
        d <- Complex.One / (cN a * d + b)
        c <- b + cN a / c
        let del = c * d
        h <- h * del
        if abs (del.Real - 1.0) + abs del.Imaginary < 1e-16 then go <- false
        k <- k + 1
    h <- Complex(ax, -ax) * h
    let ph = Math.PI * 0.5 * x2
    let cs = Complex(0.5, 0.5) * (Complex.One - Complex(Math.Cos ph, Math.Sin ph) * h)
    (cs.Real, cs.Imaginary)

// (C(z), S(z)) | None (комплексный |z| > 2,5 — ряд теряет точность)
let fresnelCS (z: Complex) : (Complex * Complex) option =
    if z.Imaginary = 0.0 then
        let x = z.Real
        if Double.IsNaN x then None
        elif abs x < 1.5 then
            let (c, s) = fresnelSeries z
            Some (Complex(c.Real, 0.0), Complex(s.Real, 0.0))
        elif Double.IsInfinity x then Some (Complex(0.5 * float (Math.Sign x), 0.0), Complex(0.5 * float (Math.Sign x), 0.0))
        else
            let (c, s) = fresnelCF (abs x)
            let sg = if x < 0.0 then -1.0 else 1.0
            Some (Complex(sg * c, 0.0), Complex(sg * s, 0.0))
    elif Complex.Abs z <= 2.5 then Some (fresnelSeries z)
    else None

let rec numEvalEnv (env: Map<string, Complex>) (v: LispValue) : Complex option =
    let numEval = numEvalEnv env
    match v with
    | LispInteger n -> Some (Complex(double n, 0.0))
    | LispRational (p, q) -> Some (Complex(double p / double q, 0.0))
    | LispFloat f -> Some (Complex(f, 0.0))
    | LispComplex (re, im) ->
        (match numEval re, numEval im with
         | Some a, Some b -> Some (a + Complex.ImaginaryOne * b)
         | _ -> None)
    | LispAlgebraic (p, lo, hi) -> Some (algToComplex p lo hi)
    | LispSym "%i" -> Some Complex.ImaginaryOne
    | LispSym "pi" -> Some (Complex(Math.PI, 0.0))
    // SF.CH2: основание экспоненты E — числовое значение (ответы правил главы 2 содержат Log[F] с F = E;
    // без этого int-check не мог подтвердить ответы с log E — класс «совпало, проверка не подтвердила»)
    | LispSym "E" -> Some (Complex(Math.E, 0.0))
    | LispSym s when env.ContainsKey s -> Some env.[s]
    // Шаг 21h: (root-sum t Q E) — сумма E по корням Q (Аберт), Q с числовыми коэффициентами
    | LispList [LispSym "root-sum"; LispSym tv; q; body] ->
        // тело — рациональная функция от t: точное значение (одно округление)
        let exact = if env.IsEmpty then exactRootSum (subNum Map.empty q) tv body else None
        match exact with
        | Some r -> Some (Complex(toDouble (ratToValue r), 0.0))
        | None ->
        (try
            // коэффициенты Q, не зависящие от t, но не числа ((sin 17/10), корни...): вычисляются в float
            let env0 = env.Remove tv
            let rec foldConst (v: LispValue) : LispValue =
                match v with
                | LispList (LispSym op :: args) when not (RootSum.containsFree tv v) && not (RootSum.freeSyms v |> Seq.exists (fun s -> not (env0.ContainsKey s) && s <> "pi" && s <> "%i")) ->
                    (match numEvalEnv env0 v with
                     | Some z when z.Imaginary = 0.0 -> LispFloat z.Real
                     | _ -> LispList (LispSym op :: List.map foldConst args))
                | LispList (h :: args) -> LispList (h :: List.map foldConst args)
                | _ -> v
            let qs = Simplify.simplify (foldConst (subNum env0 q))
            let cs = doubleCoeffs qs (LispSym tv)
            if cs.Length < 2 then (if cs.[0] = 0.0 then None else Some Complex.Zero)
            else
                let approx = rootsOfCoeffs cs
                // точные целые коэффициенты (нет float, параметров): Ньютон в многоразрядной арифметике
                let roots =
                    match exactCoeffs qs (LispSym tv) with
                    | Some ics when ics.Length >= 3 && ics.[0] <> 0I -> refineRoots ics approx
                    | _ -> approx
                let terms = roots |> List.map (fun z -> numEvalEnv (env.Add(tv, z)) body)
                if terms |> List.exists Option.isNone then None
                else Some (terms |> List.fold (fun acc z -> acc + z.Value) Complex.Zero)
         with _ -> None)
    // θ′ = δ и производные δ: ноль при u ≠ 0 (форма (deriv heaviside n u) от diff), в нуле — не число
    | LispList [LispSym "deriv"; LispSym ("heaviside" | "dirac"); _; u] ->
        (match numEval u with
         | Some z when z.Imaginary = 0.0 && z.Real <> 0.0 -> Some Complex.Zero
         | _ -> None)
    | LispList (LispSym op :: args) ->
        let vals = args |> List.map numEval
        if vals |> List.exists Option.isNone then None
        else
            let a = vals |> List.map Option.get
            match op, a with
            | "+", _ -> Some (List.fold (fun acc z -> acc + z) Complex.Zero a)
            | "*", _ -> Some (List.fold (fun acc z -> acc * z) Complex.One a)
            | "-", [z] -> Some (-z)
            | "-", z :: rest -> Some (List.fold (fun acc w -> acc - w) z rest)
            | "/", [z] -> Some (Complex.One / z)
            | "/", z :: rest -> Some (List.fold (fun acc w -> acc / w) z rest)
            | "^", [b; e] ->
                if e.Imaginary = 0.0 && e.Real = Math.Floor e.Real && abs e.Real <= 1000.0 then Some (ipow b (int e.Real))
                else Some (Complex.Pow(b, e))
            | "sqrt", [z] -> Some (Complex.Sqrt z)
            | "exp", [z] -> Some (Complex.Exp z)
            | ("log" | "ln"), [z] -> Some (Complex.Log z)
            | "sin", [z] -> Some (Complex.Sin z)
            | "cos", [z] -> Some (Complex.Cos z)
            | "tan", [z] -> Some (Complex.Tan z)
            | "asin", [z] -> Some (asinKahan z)
            | "acos", [z] -> Some (acosKahan z)
            | "atan", [z] -> Some (Complex.Atan z)
            // WASM.6a Д3: обратные функции через основные (главные ветви): acot = π/2 − atan, asec = acos(1/z), …
            | "acot", [z] -> Some (cN (Math.PI / 2.0) - Complex.Atan z)
            | "asec", [z] -> Some (acosKahan (Complex.One / z))
            | "acsc", [z] -> Some (asinKahan (Complex.One / z))
            // (Complex не имеет Asinh/Acosh/Atanh — те же формулы, что для asinh/acosh/atanh выше, от 1/z)
            | "acoth", [z] ->
                let w = Complex.One / z
                hypFin (cN 0.5 * Complex.Log ((Complex.One + w) / (Complex.One - w)))
            | "asech", [z] ->
                let w = Complex.One / z
                hypFin (Complex.Log (w + Complex.Sqrt (w + Complex.One) * Complex.Sqrt (w - Complex.One)))
            | "acsch", [z] ->
                let w = Complex.One / z
                hypFin (Complex.Log (w + Complex.Sqrt (w * w + Complex.One)))
            // eval-num: гиперболические функции (sh/ch/th — алиасы входного языка, если дойдут)
            | ("sinh" | "sh"), [z] -> Some (Complex.Sinh z)
            | ("cosh" | "ch"), [z] -> Some (Complex.Cosh z)
            | ("tanh" | "th"), [z] -> Some (Complex.Tanh z)
            | "coth", [z] -> hypFin (Complex.One / Complex.Tanh z)
            | "sech", [z] -> hypFin (Complex.One / Complex.Cosh z)
            | "csch", [z] -> hypFin (Complex.One / Complex.Sinh z)
            | "asinh", [z] -> Some (if z.Imaginary = 0.0 then Complex(Math.Asinh z.Real, 0.0) else Complex.Log (z + Complex.Sqrt (z * z + Complex.One)))
            | "acosh", [z] -> hypFin (if z.Imaginary = 0.0 && z.Real >= 1.0 then Complex(Math.Acosh z.Real, 0.0) else Complex.Log (z + Complex.Sqrt (z + Complex.One) * Complex.Sqrt (z - Complex.One)))
            | "atanh", [z] -> hypFin (if z.Imaginary = 0.0 && abs z.Real < 1.0 then Complex(Math.Atanh z.Real, 0.0) else cN 0.5 * Complex.Log ((Complex.One + z) / (Complex.One - z)))
            // A3′.3: эллиптические интегралы Лежандра (комплексные аргументы — для кубики x³+1)
            | "elliptic-f", [phi; k] ->
                let s = Complex.Sin phi
                let c = Complex.Cos phi
                Some (s * carlsonRfC (c * c) (Complex.One - k * k * s * s) Complex.One)
            | "elliptic-e", [phi; k] ->
                let s = Complex.Sin phi
                let c = Complex.Cos phi
                let m = k * k
                Some (s * carlsonRfC (c * c) (Complex.One - m * s * s) Complex.One
                      - (m / cN 3.0) * s * s * s * carlsonRdC (c * c) (Complex.One - m * s * s) Complex.One)
            | "elliptic-pi", [n; phi; k] ->
                if n.Imaginary = 0.0 && phi.Imaginary = 0.0 && k.Imaginary = 0.0 then
                    Some (Complex(ellipticPiNum n.Real phi.Real k.Real, 0.0))
                else None
            | "elliptic-k", [k] ->
                Some (carlsonRfC Complex.Zero (Complex.One - k * k) Complex.One)
            | "elliptic-ec", [k] ->
                let m = k * k
                Some (carlsonRfC Complex.Zero (Complex.One - m) Complex.One
                      - (m / cN 3.0) * carlsonRdC Complex.Zero (Complex.One - m) Complex.One)
            | "abs", [z] -> Some (Complex(Complex.Abs z, 0.0))
            // Шаг 21l.0: комбинаторные головы — численные значения (рациональные аргументы уже
            // свернулись точно в simplify; сюда попадают float и ψ)
            | "binomial", [n; k] ->
                if n.Imaginary = 0.0 && k.Imaginary = 0.0 && n.Real = floor n.Real && k.Real = floor k.Real then
                    if k.Real < 0.0 || k.Real > n.Real then Some (Complex(0.0, 0.0))
                    else
                        let a = lgamma (n.Real + 1.0) - lgamma (k.Real + 1.0) - lgamma (n.Real - k.Real + 1.0)
                        Some (Complex(exp a, 0.0))
                else None
            | "gamma", [z] ->
                if z.Imaginary = 0.0 then
                    if z.Real <= 0.0 && z.Real = floor z.Real then None    // полюсы Γ в 0, −1, −2, …
                    elif z.Real < 0.5 then
                        // отражение Γ(x) = π / (sin πx · Γ(1−x)): знак для x < 0 сохраняется (lgamma даёт только |Γ|)
                        Some (Complex(Math.PI / (Math.Sin (Math.PI * z.Real) * exp (lgamma (1.0 - z.Real))), 0.0))
                    else Some (Complex(exp (lgamma z.Real), 0.0))
                else None
            // SF.CH2: неполная гамма Γ(a, z) — ответы правил 2.1 (`Gamma[m+1, ...]`, m — целое ≤ 0) и 2.2
            | "gamma", [a; z] ->
                if a.Imaginary = 0.0 then gammaIncNum a.Real z else None
            | "psi", [z] -> psiNum 0 z
            // PERF.F1: Li₂ — комплексный аргумент и вещественный z > 1 (главная ветвь, на разрезе «снизу»)
            // INT.SF3: Li_s, целое s ≥ 3 — polylogC (s = 1, 2 — как раньше); вещественный z ≤ 1 — вещественное значение
            | "polylog", [s; z] ->
                if s.Imaginary <> 0.0 || s.Real <> Math.Floor s.Real then None
                elif s.Real = 2.0 then Some (li2Complex z)
                else
                    polylogC (int s.Real) z
                    |> Option.map (fun r -> if z.Imaginary = 0.0 && z.Real <= 1.0 then Complex(r.Real, 0.0) else r)
            // INT.SF3: интегралы Френеля (нормировка πt²/2) и E_n(z) (целое n ≥ 0)
            | "fresnel_s", [z] -> fresnelCS z |> Option.map snd
            | "fresnel_c", [z] -> fresnelCS z |> Option.map fst
            | ("exp_integral_e" | "expint"), [n; z] ->
                if n.Imaginary = 0.0 && n.Real = Math.Floor n.Real && n.Real >= 0.0 && n.Real <= 60.0 then expIntENum (int n.Real) z else None
            // ODE.0: специальные функции для численного сертификата
            // INT.SF2: erf/erfc/erfi от комплексного аргумента (ответы Rubi с √(−a), мнимыми параметрами) — ряд DLMF 7.6.1
            | "erf", [z] ->
                if z.Imaginary = 0.0 then Some (Complex(erfNum z.Real, 0.0)) else erfComplexSeries z
            | "erfc", [z] ->
                if z.Imaginary = 0.0 then Some (Complex(1.0 - erfNum z.Real, 0.0))
                else erfComplexSeries z |> Option.map (fun v -> Complex.One - v)
            | "erfi", [z] ->
                if z.Imaginary = 0.0 && abs z.Real <= 20.0 then Some (Complex(erfiSeries z.Real, 0.0))
                elif z.Imaginary = 0.0 then None
                else erfComplexSeries (Complex.ImaginaryOne * z) |> Option.map (fun v -> -Complex.ImaginaryOne * v)   // DLMF 7.4.? erfi z = −i·erf(iz)
            | "Ei", [z] ->
                if z.Imaginary = 0.0 && z.Real <> 0.0 then Some (Complex(eiNum z.Real, 0.0)) else None
            // SF.CH2: `ExpIntegralEi` правил Rubi печатается головой exp_integral_ei (utils.lisp:2157) —
            // тот же численный Ei, что и «Ei»
            | "exp_integral_ei", [z] -> eiNumComplex z
            | "li", [z] ->
                if z.Imaginary = 0.0 && z.Real > 0.0 && z.Real <> 1.0 then Some (Complex(eiNum (log z.Real), 0.0)) else None
            // INT.SF2: головы Rubi sin_integral/cos_integral/sinh_integral/cosh_integral (utils.lisp:2277) = Si/Ci/Shi/Chi;
            // комплексный аргумент и Shi/Chi — ряды DLMF 6.6.? (6.2.9, 6.2.11, 6.5.?) в trigIntSeriesC
            | ("Si" | "sin_integral"), [z] ->
                if z.Imaginary = 0.0 then Some (Complex(siNum z.Real, 0.0)) else trigIntSeriesC "Si" z
            | ("Ci" | "cos_integral"), [z] ->
                if z.Imaginary = 0.0 && z.Real <> 0.0 then Some (Complex(ciNum z.Real, 0.0))
                elif z.Imaginary = 0.0 then None
                else trigIntSeriesC "Ci" z
            | ("Shi" | "sinh_integral"), [z] -> trigIntSeriesC "Shi" z
            | ("Chi" | "cosh_integral"), [z] ->
                if z = Complex.Zero then None else trigIntSeriesC "Chi" z
            // θ (1/2 в нуле, как в lib/laplace.lisp) и δ (в нуле — не число: None)
            | "heaviside", [z] ->
                if z.Imaginary = 0.0 then Some (Complex((if z.Real < 0.0 then 0.0 elif z.Real > 0.0 then 1.0 else 0.5), 0.0)) else None
            | "dirac", [z] ->
                if z.Imaginary = 0.0 && z.Real <> 0.0 then Some Complex.Zero else None
            | "psi", [z; m] ->
                if m.Imaginary = 0.0 && m.Real = floor m.Real && m.Real >= 0.0 && m.Real <= 100.0 then psiNum (int m.Real) z
                else None
            | "harmonic", [n] -> harmonicNum n 1.0
            | "harmonic", [n; m] ->
                if m.Imaginary = 0.0 && m.Real >= 1.0 then harmonicNum n m.Real else None
            | "bernoulli", [n] ->
                if n.Imaginary = 0.0 && n.Real = floor n.Real && n.Real >= 0.0 && n.Real <= 60.0 then
                    let exact = Simplify.simplify (LispList [LispSym "bernoulli"; LispFloat n.Real])
                    (match exact with
                     | LispInteger _ | LispRational _ -> numEvalEnv env exact
                     | _ -> None)
                else None
            | "rf", [a; k] -> pochNum a k 1.0
            | "ff", [a; k] -> pochNum a k -1.0
            // SFn.2a: Бессель, Эйри, Лежандр — только вещественные аргументы
            | "bessel-j", [nu; z] ->
                if nu.Imaginary = 0.0 && z.Imaginary = 0.0 then
                    besselJNum nu.Real z.Real |> Option.map (fun v -> Complex(v, 0.0))
                else None
            | "bessel-y", [nu; z] ->
                if nu.Imaginary = 0.0 && z.Imaginary = 0.0 then
                    besselYNum nu.Real z.Real |> Option.map (fun v -> Complex(v, 0.0))
                else None
            | "bessel-i", [nu; z] ->
                if nu.Imaginary = 0.0 && z.Imaginary = 0.0 then
                    besselINum nu.Real z.Real |> Option.map (fun v -> Complex(v, 0.0))
                else None
            | "bessel-k", [nu; z] ->
                if nu.Imaginary = 0.0 && z.Imaginary = 0.0 then
                    besselKNum nu.Real z.Real |> Option.map (fun v -> Complex(v, 0.0))
                else None
            | "airy-ai", [z] ->
                if z.Imaginary = 0.0 then airyNum z.Real 0 |> Option.map (fun v -> Complex(v, 0.0)) else None
            | "airy-bi", [z] ->
                if z.Imaginary = 0.0 then airyNum z.Real 1 |> Option.map (fun v -> Complex(v, 0.0)) else None
            | "airy-ai-prime", [z] ->
                if z.Imaginary = 0.0 then airyNum z.Real 2 |> Option.map (fun v -> Complex(v, 0.0)) else None
            | "airy-bi-prime", [z] ->
                if z.Imaginary = 0.0 then airyNum z.Real 3 |> Option.map (fun v -> Complex(v, 0.0)) else None
            | "legendre-p", [n; z] ->
                if n.Imaginary = 0.0 && z.Imaginary = 0.0 then
                    legendrePNum n.Real z.Real |> Option.map (fun v -> Complex(v, 0.0))
                else None
            | "legendre-q", [n; z] ->
                if n.Imaginary = 0.0 && z.Imaginary = 0.0 then
                    legendreQNum n.Real z.Real |> Option.map (fun v -> Complex(v, 0.0))
                else None
            | _ ->
                match numericHooks.TryGetValue op with
                | true, fn -> hookNum fn a
                | _ -> None
    | _ -> None

// lnΓ(x) — формула Ланцоша (g = 7, 9 коэффициентов); x < 0.5 — через отражение
and private lgamma (x: float) : float =
    let g = 7.0
    let ls = [| 0.99999999999980993; 676.5203681218851; -1259.1392167224028;
                771.32342877765313; -176.61502916214059; 12.507343278686905;
                -0.13857109526572012; 9.9843695780195716e-6; 1.5056327351493116e-7 |]
    if x < 0.5 then log (Math.PI / Math.Sin (Math.PI * x)) - lgamma (1.0 - x)
    else
        let xx = x - 1.0
        let mutable a = ls.[0]
        let t = xx + g + 0.5
        for i in 1 .. 8 do a <- a + ls.[i] / (xx + float i)
        log (sqrt (2.0 * Math.PI) * (t ** (xx + 0.5)) * exp (-t) * a)

// ψ_0(z) (дигамма) численно: рекуррентность к x ≥ 6 + асимптотика Бернулли; None — комплексный/полюс
and private psiDigamma (x: float) : float option =
    if x < 0.5 then
        // отражение: ψ(x) = ψ(1−x) − π/tan(πx)
        (match psiDigamma (1.0 - x) with
         | Some r -> Some (r - Math.PI / Math.Tan (Math.PI * x))
         | None -> None)
    else
        let rec go (xx: float) (acc: float) =
            if xx < 6.0 then go (xx + 1.0) (acc - 1.0 / xx)
            else
                let inv2 = 1.0 / (xx * xx)
                let corr = inv2 * (1.0/12.0 + inv2 * (-1.0/120.0 + inv2 * (1.0/252.0 + inv2 * (-1.0/240.0 + inv2 / 132.0))))
                acc + log xx - 0.5 / xx - corr
        Some (go x 0.0)

// ψ_m(z) численно (m ≥ 0). ψ_0 — дигамма; ψ_m (m ≥ 1) — сдвиг к x ≥ 8 (рекуррентность
// ψ_m(z) = ψ_m(z+1) + (−1)^m·m!/z^{m+1}) + ряд Σ 1/(x+k)^{m+1} с поправкой хвоста Эйлера—Маклорена
and private psiNum (m: int) (z: Complex) : Complex option =
    if z.Imaginary <> 0.0 then None
    elif z.Real <= 0.0 && z.Real = floor z.Real then None    // полюсы
    else
        let m' = float m
        let mf = float (List.fold ( * ) 1 [ 1 .. m ])        // m!
        let sgn = if m % 2 = 1 then 1.0 else -1.0            // (−1)^{m+1}
        if m = 0 then
            (match psiDigamma z.Real with Some v -> Some (Complex(v, 0.0)) | None -> None)
        else
            // сдвиг к x ≥ 8 (рекуррентность ψ_m(z) = ψ_m(z+1) + (−1)^m·m!/z^{m+1}), затем ряд + поправка хвоста
            let rec shift (x: float) (acc: float) =
                if x < 8.0 then shift (x + 1.0) (acc + (if m % 2 = 0 then -1.0 else 1.0) * mf / x ** (m' + 1.0))
                else
                    let mutable s = 0.0
                    let mutable k = 0.0
                    let eps = 1e-15
                    let mutable go = true
                    while go do
                        let t = 1.0 / (x + k) ** (m' + 1.0)
                        s <- s + t
                        k <- k + 1.0
                        if abs t < eps || k > 1e6 then go <- false
                    // хвост Σ_{k=K}^{∞} 1/k^{m+1} ≈ 1/(m·K^m) + 1/(2·K^{m+1}) (Эйлер—Маклорен, старший член)
                    let K = x + k
                    let tail = 1.0 / (m' * K ** m') + 0.5 / K ** (m' + 1.0)
                    Some (Complex(sgn * mf * (s + tail) + acc, 0.0))
            shift z.Real 0.0

// Σ 1/k^m численно (гармонические числа)
and private harmonicNum (n: Complex) (m: float) : Complex option =
    if n.Imaginary = 0.0 && n.Real = floor n.Real && n.Real >= 0.0 && n.Real <= 1e7 then
        let mutable s = 0.0
        for k in 1.0 .. n.Real do s <- s + 1.0 / k ** m
        Some (Complex(s, 0.0))
    else None

// (a)_k / (a)‾k численно
and private pochNum (a: Complex) (k: Complex) (dir: float) : Complex option =
    if a.Imaginary = 0.0 && k.Imaginary = 0.0 && k.Real = floor k.Real && k.Real >= 0.0 && k.Real <= 1e6 then
        let mutable r = Complex(1.0, 0.0)
        for i in 0.0 .. k.Real - 1.0 do
            r <- r * Complex(a.Real + dir * i, 0.0)
        Some r
    else None

// --- SFn.2a: численные значения Бесселя, Эйри, Лежандра (вещественные аргументы) ---

and private besselJNum (nu: float) (x: float) : float option =
    // x ≤ 12 — степенной ряд; больше — асимптотика Ханкеля (двойная точность)
    if x < 0.0 then
        if nu = Math.Round nu then
            besselJNum nu (-x)
            |> Option.map (fun v -> if int (Math.Round nu) % 2 = 0 then v else -v)
        else None
    elif x = 0.0 then
        if nu = 0.0 then Some 1.0 elif nu > 0.0 then Some 0.0 else None
    elif nu < 0.0 && nu = Math.Round nu then
        // J_{−n} = (−1)^n J_n (ряд при ν = −n упирается в полюс Γ)
        besselJNum (-nu) x
        |> Option.map (fun v -> if int (-nu) % 2 = 0 then v else -v)
    elif x <= 12.0 then
        let h = x / 2.0
        // Γ(ν+1) при отрицательном нецелом ν: сдвиг аргумента к (0,1], знак — отдельным множителем
        // (иначе lgamma от отрицательного аргумента даёт nan; нужно для проверки ОДУ с J_{ν−2})
        let mutable z = nu + 1.0
        let mutable sg = 1.0
        while z <= 0.0 do
            sg <- sg * z
            z <- z + 1.0
        let pref = sg * exp (nu * log h - lgamma z)
        let mutable term = 1.0
        let mutable s = 1.0
        let mutable k = 0
        let mutable go = true
        while go && k < 2000 do
            term <- term * (-(x * x) / 4.0) / (float (k + 1) * (nu + float k + 1.0))
            s <- s + term
            k <- k + 1
            if abs term < 1e-18 * (abs s + 1e-300) then go <- false
        Some (pref * s)
    else
        let mu = 4.0 * nu * nu
        let chi = x - nu * Math.PI / 2.0 - Math.PI / 4.0
        let coeff (k: int) =
            let mutable p = 1.0
            for j in 1 .. k do
                let q = float (2 * j - 1)
                p <- p * (mu - q * q) / (float j * 8.0)
            p
        let mutable psum = 1.0
        let mutable qsum = 0.0
        let mutable k = 1
        let mutable go = true
        while go && k <= 40 do
            let ak = coeff k / (x ** float k)
            if k % 2 = 0 then
                psum <- psum + (if (k / 2) % 2 = 0 then ak else -ak)
            else
                qsum <- qsum + (if ((k - 1) / 2) % 2 = 0 then ak else -ak)
            if abs ak < 1e-18 then go <- false
            k <- k + 1
        Some (sqrt (2.0 / (Math.PI * x)) * (cos chi * psum - sin chi * qsum))

and private besselYNum (nu: float) (x: float) : float option =
    // Y при x < 0 комплексна (ветвление) — вещественных значений не даём
    if x <= 0.0 then None
    elif nu <> Math.Round nu then
        // отражение: Y_ν = (J_ν cos νπ − J_{−ν})/sin νπ
        match besselJNum nu x, besselJNum (-nu) x with
        | Some jn, Some jm -> Some ((jn * cos (Math.PI * nu) - jm) / sin (Math.PI * nu))
        | _ -> None
    else
        let n0 = int (Math.Round nu)
        // Y_{−n} = (−1)^n Y_n (для положительных n знака нет)
        let sign = if n0 < 0 && n0 % 2 <> 0 then -1.0 else 1.0
        let n = abs n0
        if x <= 12.0 then
            match besselJNum (float n) x with
            | None -> None
            | Some jn ->
                let dish = x / 2.0
                let mutable s1 = 0.0
                let mutable fact = 1.0
                for k in 0 .. n - 1 do
                    let num = exp (lgamma (float (n - k)))
                    s1 <- s1 + num / fact * dish ** float (2 * k - n)
                    fact <- fact * float (k + 1)
                // бесконечная сумма Σ (−1)^k (ψ(k+1)+ψ(n+k+1))/(k!(n+k)!) (x/2)^{2k+n}
                // ψ целых аргументов точно: ψ(m) = H_{m−1} − γ
                let euler = 0.57721566490153286061
                let mutable hk = 0.0
                let mutable hnk = 0.0
                for i in 1 .. n do hnk <- hnk + 1.0 / float i
                let mutable term = exp (-lgamma (float n + 1.0))
                let mutable s2 = 0.0
                let mutable k = 0
                let mutable go = true
                while go && k < 2000 do
                    let add = (if k % 2 = 0 then 1.0 else -1.0) * (hk + hnk - 2.0 * euler)
                              * term * dish ** float (2 * k + n)
                    s2 <- s2 + add
                    hk <- hk + 1.0 / float (k + 1)
                    hnk <- hnk + 1.0 / float (n + k + 1)
                    term <- term / (float (k + 1) * float (n + k + 1))
                    k <- k + 1
                    if abs add < 1e-18 * (abs s2 + 1e-300) then go <- false
                Some (sign * ((2.0 / Math.PI) * log dish * jn - (s1 + s2) / Math.PI))
        else
            let mu = 4.0 * nu * nu
            let chi = x - nu * Math.PI / 2.0 - Math.PI / 4.0
            let coeff (k: int) =
                let mutable p = 1.0
                for j in 1 .. k do
                    let q = float (2 * j - 1)
                    p <- p * (mu - q * q) / (float j * 8.0)
                p
            let mutable psum = 1.0
            let mutable qsum = 0.0
            let mutable k = 1
            let mutable go = true
            while go && k <= 40 do
                let ak = coeff k / (x ** float k)
                if k % 2 = 0 then
                    psum <- psum + (if (k / 2) % 2 = 0 then ak else -ak)
                else
                    qsum <- qsum + (if ((k - 1) / 2) % 2 = 0 then ak else -ak)
                if abs ak < 1e-18 then go <- false
                k <- k + 1
            Some (sign * sqrt (2.0 / (Math.PI * x)) * (sin chi * psum + cos chi * qsum))

and private besselINum (nu: float) (x: float) : float option =
    if x < 0.0 then
        if nu = Math.Round nu then
            besselINum nu (-x)
            |> Option.map (fun v -> if int (Math.Round nu) % 2 = 0 then v else -v)
        else None
    elif x = 0.0 then
        if nu = 0.0 then Some 1.0 elif nu > 0.0 then Some 0.0 else None
    elif nu < 0.0 && nu = Math.Round nu then
        // I_{−n} = I_n
        besselINum (-nu) x
    else
        let h = x / 2.0
        // как у J: Γ(ν+1) при отрицательном нецелом ν — сдвигом аргумента к (0,1]
        let mutable z = nu + 1.0
        let mutable sg = 1.0
        while z <= 0.0 do
            sg <- sg * z
            z <- z + 1.0
        let pref = sg * exp (nu * log h - lgamma z)
        let mutable term = 1.0
        let mutable s = 1.0
        let mutable k = 0
        let mutable go = true
        while go && k < 4000 do
            term <- term * (x * x / 4.0) / (float (k + 1) * (nu + float k + 1.0))
            s <- s + term
            k <- k + 1
            if abs term < 1e-17 * (abs s + 1e-300) then go <- false
        Some (pref * s)

and private besselKNum (nu: float) (x: float) : float option =
    // интеграл K_ν(x) = ∫₀^∞ e^(−x·ch t)·ch(νt) dt — без вычитания больших членов
    if x <= 0.0 then None
    else
        let tmax = Math.Acosh (1.0 + 45.0 / x)
        let n = 20000
        let h = tmax / float n
        let f (t: float) = exp (-x * cosh t) * cosh (nu * t)
        let mutable s = f 0.0 + f tmax
        for i in 1 .. n - 1 do
            s <- s + (if i % 2 = 0 then 2.0 else 4.0) * f (float i * h)
        Some (s * h / 3.0)

and private airyNum (x: float) (kind: int) : float option =
    // kind: 0 — Ai, 1 — Bi, 2 — Ai′, 3 — Bi′; через K_{1/3}, K_{2/3} (x > 0) и J_{±1/3}, J_{±2/3} (x < 0)
    let c1 = 0.35502805388781723926     // Ai(0)
    let c2 = 0.25881940379280679840     // −Ai′(0)
    if x = 0.0 then
        match kind with
        | 0 -> Some c1
        | 1 -> Some (sqrt 3.0 * c1)
        | 2 -> Some (-c2)
        | _ -> Some (sqrt 3.0 * c2)
    elif x > 0.0 then
        let zeta = (2.0 / 3.0) * x ** 1.5
        match kind with
        | 0 ->
            match besselKNum (1.0 / 3.0) zeta with
            | Some k -> Some (sqrt (x / 3.0) / Math.PI * k)
            | None -> None
        | 1 ->
            match besselINum (-1.0 / 3.0) zeta, besselINum (1.0 / 3.0) zeta with
            | Some i1, Some i2 -> Some (sqrt (x / 3.0) * (i1 + i2))
            | _ -> None
        | 2 ->
            match besselKNum (2.0 / 3.0) zeta with
            | Some k -> Some (-(x / sqrt 3.0) / Math.PI * k)
            | None -> None
        | _ ->
            match besselINum (-2.0 / 3.0) zeta, besselINum (2.0 / 3.0) zeta with
            | Some i1, Some i2 -> Some (x / sqrt 3.0 * (i1 + i2))
            | _ -> None
    else
        let t = -x
        let zeta = (2.0 / 3.0) * t ** 1.5
        let j3 = besselJNum (1.0 / 3.0) zeta |> Option.defaultValue nan
        let jm3 = besselJNum (-1.0 / 3.0) zeta |> Option.defaultValue nan
        let j23 = besselJNum (2.0 / 3.0) zeta |> Option.defaultValue nan
        let jm23 = besselJNum (-2.0 / 3.0) zeta |> Option.defaultValue nan
        let j43 = besselJNum (4.0 / 3.0) zeta |> Option.defaultValue nan
        let jm43 = besselJNum (-4.0 / 3.0) zeta |> Option.defaultValue nan
        if nan = j3 || nan = jm3 || nan = j23 || nan = jm23 || nan = j43 || nan = jm43 then None
        else
            let s = jm3 + j3
            let d = jm3 - j3
            match kind with
            | 0 -> Some (sqrt t / 3.0 * s)
            | 1 -> Some (sqrt (t / 3.0) * d)
            | 2 ->
                let ds = 0.5 * (jm43 - j23) + 0.5 * (jm23 - j43)
                Some (-(s / (6.0 * sqrt t) + t / 3.0 * ds))
            | _ ->
                let dd = 0.5 * (jm43 - j23) - 0.5 * (jm23 - j43)
                Some (-(d / (2.0 * sqrt (3.0 * t)) + t / sqrt 3.0 * dd))

and private legendrePNum (n: float) (x: float) : float option =
    if n = Math.Round n && n >= 0.0 && n <= 200.0 then
        let nn = int (Math.Round n)
        let mutable p0 = 1.0
        let mutable p1 = x
        if nn = 0 then Some 1.0
        else
            for k in 1 .. nn - 1 do
                let p2 = ((2.0 * float k + 1.0) * x * p1 - float k * p0) / float (k + 1)
                p0 <- p1
                p1 <- p2
            Some p1
    else None

and private legendreQNum (n: float) (x: float) : float option =
    if n = Math.Round n && n >= 0.0 && n <= 200.0 && abs x < 1.0 then
        let nn = int (Math.Round n)
        let q0 = 0.5 * log ((1.0 + x) / (1.0 - x))
        let mutable qa = q0
        let mutable qb = x * q0 - 1.0
        if nn = 0 then Some q0
        else
            for k in 1 .. nn - 1 do
                let q2 = ((2.0 * float k + 1.0) * x * qb - float k * qa) / float (k + 1)
                qa <- qb
                qb <- q2
            Some qb
    else None

// --- ODE.0: численные значения специальных функций (erf, erfc, erfi, Ei, li, Si, Ci) ---
// Ряды для умеренных аргументов, асимптотика или непрерывная дробь для больших; аргумент вещественный.

and private erfSeries (x: float) : float =
    // erf x = (2/√π) Σ (−1)^n x^(2n+1)/(n!(2n+1))
    let x2 = x * x
    let mutable term = x
    let mutable sum = x
    let mutable n = 0
    let mutable go = true
    while go && n < 300 do
        n <- n + 1
        term <- term * (-x2) / float n
        let add = term / float (2 * n + 1)
        sum <- sum + add
        if abs add < 1e-17 * (abs sum + 1e-300) then go <- false
    (2.0 / sqrt Math.PI) * sum

and private erfcCF (x: float) : float =
    // erfc(x) = e^(−x²)/(x√π) · 1/(1 + v/(1 + 2v/(1 + 3v/(1 + …)))), v = 1/(2x²), x > 0
    let v = 1.0 / (2.0 * x * x)
    let mutable f = 1.0
    for n in 120 .. -1 .. 1 do
        f <- 1.0 + float n * v / f
    exp (-x * x) / (x * sqrt Math.PI) / f

and private erfNum (x: float) : float =
    if abs x < 3.0 then erfSeries x
    elif x > 0.0 then 1.0 - erfcCF x
    else -1.0 + erfcCF (-x)

and private erfiSeries (x: float) : float =
    // erfi x = (2/√π) Σ x^(2n+1)/(n!(2n+1))
    let x2 = x * x
    let mutable term = x
    let mutable sum = x
    let mutable n = 0
    let mutable go = true
    while go && n < 400 do
        n <- n + 1
        term <- term * x2 / float n
        let add = term / float (2 * n + 1)
        sum <- sum + add
        if abs add < 1e-17 * (abs sum + 1e-300) then go <- false
    (2.0 / sqrt Math.PI) * sum

and private eiNum (x: float) : float =
    if x > 25.0 then
        // асимптотика Ei(x) ~ e^x/x · Σ n!/x^n (оптимальное обрезание)
        let mutable term = 1.0
        let mutable sum = 1.0
        let mutable n = 0
        let mutable go = true
        while go && n < 40 do
            n <- n + 1
            term <- term * float n / x
            if abs term < 1e-17 * abs sum then go <- false
            else sum <- sum + term
        exp x / x * sum
    else
        // ряд Ei(x) = γ + ln|x| + Σ x^n/(n·n!)
        let mutable term = 1.0
        let mutable sum = 0.0
        let mutable n = 1
        let mutable go = true
        while go && n < 500 do
            term <- term * x / float n
            let add = term / float n
            sum <- sum + add
            if abs add < 1e-17 * (abs sum + 1e-300) then go <- false
            n <- n + 1
        0.5772156649015329 + log (abs x) + sum

and private siNum (x: float) : float =
    // Si x = Σ (−1)^n x^(2n+1)/((2n+1)!(2n+1))
    let mutable term = x
    let mutable sum = x
    let mutable n = 0
    let mutable go = true
    while go && n < 500 do
        n <- n + 1
        term <- term * (-x * x) / float (2 * n) / float (2 * n + 1)
        let add = term / float (2 * n + 1)
        sum <- sum + add
        if abs add < 1e-17 * (abs sum + 1e-300) then go <- false
    sum

and private ciNum (x: float) : float =
    // Ci x = γ + ln|x| + Σ (−1)^n x^(2n)/((2n)!(2n))
    let mutable term = 1.0
    let mutable sum = 0.0
    let mutable n = 0
    let mutable go = true
    while go && n < 500 do
        n <- n + 1
        term <- term * (-x * x) / float (2 * n - 1) / float (2 * n)
        let add = term / float (2 * n)
        sum <- sum + add
        if abs add < 1e-17 * (abs sum + 1e-300) then go <- false
    0.5772156649015329 + log (abs x) + sum

// INT.SF2: Si/Ci/Shi/Chi — ряды в комплексной арифметике (целые функции, у Ci/Chi — γ + ln z, главная ветвь):
// Si z = Σ (−1)^n z^(2n+1)/((2n+1)!(2n+1)) (DLMF 6.6.5), Shi z = Σ z^(2n+1)/((2n+1)!(2n+1)) (6.6.6, Shi z = −i·Si(iz)),
// Ci z = γ + ln z + Σ_{n≥1} (−1)^n z^(2n)/((2n)!·2n) (6.6.6), Chi z = γ + ln z + Σ_{n≥1} z^(2n)/((2n)!·2n) (6.6.7).
// У Si/Ci знакопеременный ряд теряет ≈ e^|z| значащих — предел |z| ≤ 12; у Shi/Chi слагаемые одного знака — |z| ≤ 30.
and private trigIntSeriesC (kind: string) (z: Complex) : Complex option =
    let alt = (kind = "Si" || kind = "Ci")
    if Complex.Abs z > (if alt then 12.0 else 30.0) then None
    else
        let z2 = if alt then -(z * z) else z * z
        let odd = (kind = "Si" || kind = "Shi")
        let mutable term = if odd then z else Complex.One
        let mutable sum = if odd then z else Complex.Zero
        let mutable n = 0
        let mutable go = true
        while go && n < 400 do
            n <- n + 1
            let m = float n
            let add =
                if odd then
                    term <- term * z2 / cN (2.0 * m) / cN (2.0 * m + 1.0)
                    term / cN (2.0 * m + 1.0)
                else
                    term <- term * z2 / cN (2.0 * m - 1.0) / cN (2.0 * m)
                    term / cN (2.0 * m)
            sum <- sum + add
            if Complex.Abs add < 1e-17 * (Complex.Abs sum + 1e-300) then go <- false
        Some (if odd then sum else cN 0.5772156649015329 + Complex.Log z + sum)

// INT.SF2: erf z = (2/√π) Σ (−1)^n z^(2n+1)/(n!(2n+1)) (DLMF 7.6.1), комплексный z; |z| ≤ 4 (потеря ≈ e^|z|² значащих)
and private erfComplexSeries (z: Complex) : Complex option =
    if Complex.Abs z > 4.0 then None
    else
        let z2 = -(z * z)
        let mutable term = z
        let mutable sum = z
        let mutable n = 0
        let mutable go = true
        while go && n < 400 do
            n <- n + 1
            term <- term * z2 / cN (float n)
            let add = term / cN (float (2 * n + 1))
            sum <- sum + add
            if Complex.Abs add < 1e-17 * (Complex.Abs sum + 1e-300) then go <- false
        Some (cN (2.0 / sqrt Math.PI) * sum)

// --- SF.CH2: проверка ответов главы 2 Rubi (экспоненты) ---
// Правила 2.1/2.2 отдают ответы через Γ(m+1, z) («2.1 (c+d x)^m (a+b (F^(g (e+f x)))^n)^p.m», правило 4:
// Gamma[m+1, -f*g*Log[F]/d*(c+d*x)]), а 2.1 #3 и 2.3 — через ExpIntegralEi. Без численных значений этих голов
// int-check возвращал 'skip, и ответ отвергался: 261 из 442 разобранных задач главы 2 — класс «совпало, но
// проверка не подтвердила».

and private eiNumComplex (z: Complex) : Complex option =
    if z.Imaginary = 0.0 && z.Real <> 0.0 then Some (Complex(eiNum z.Real, 0.0)) else None

and private gammaRealNum (a: float) : float option =
    // Γ(a) вещественное: полюсы в 0, −1, −2, …; ниже 0,5 — отражение (lgamma даёт только |Γ|)
    if a <= 0.0 && a = floor a then None
    elif a < 0.5 then Some (Math.PI / (Math.Sin (Math.PI * a) * exp (lgamma (1.0 - a))))
    else Some (exp (lgamma a))

and private e1Complex (z: Complex) : Complex =
    // E₁(z) = −γ − ln z − Σ_{n≥1} (−z)^n/(n·n!) (главная ветвь, DLMF 8.6.4); E₁(z) = Γ(0, z)
    let mutable term = Complex.One
    let mutable sum = Complex.Zero
    let mutable n = 1
    let mutable go = true
    while go && n < 500 do
        term <- term * (-z) / cN (float n)
        let add = term / cN (float n)
        sum <- sum + add
        if Complex.Abs add < 1e-17 * (Complex.Abs sum + 1e-300) then go <- false
        n <- n + 1
    -(cN 0.5772156649015329) - Complex.Log z - sum

and private gammaIncSeries (a: float) (z: Complex) : Complex =
    // γ(a,z) = z^a·e^(−z)·Σ z^n/(a(a+1)…(a+n)), Γ(a,z) = Γ(a) − γ(a,z); годится при |z| < |a+1| (DLMF 8.7.3).
    // Первое слагаемое суммы — 1/a (n = 0), а не 1.
    let mutable term = Complex.One / cN a
    let mutable sum = term
    let mutable n = 1
    let mutable go = true
    while go && n < 5000 do
        term <- term * z / cN (a + float n)
        sum <- sum + term
        if Complex.Abs term < 1e-17 * Complex.Abs sum then go <- false
        n <- n + 1
    Complex.Pow(z, a) * Complex.Exp(-z) * sum

and private gammaIncCF (a: float) (z: Complex) : Complex =
    // Γ(a,z) = e^(−z+a·ln z)·h (непрерывная дробь DLMF 8.9.2, модифицированный алгоритм Ленца)
    let eps = 1e-16
    let fpmin = 1e-300
    let mutable b = z + cN (1.0 - a)
    let mutable c = cN 1e300
    let mutable d = Complex.One / b
    let mutable h = d
    let mutable i = 1
    let mutable go = true
    while go && i < 5000 do
        let an = cN (-(float i) * (float i - a))
        b <- b + cN 2.0
        d <- an * d + b
        if Complex.Abs d < fpmin then d <- cN fpmin
        c <- b + an / c
        if Complex.Abs c < fpmin then c <- cN fpmin
        d <- Complex.One / d
        let del = d * c
        h <- h * del
        if Complex.Abs (del - Complex.One) < eps then go <- false
        i <- i + 1
    Complex.Exp(-z + cN a * Complex.Log z) * h

and private gammaIncNum (a: float) (z: Complex) : Complex option =
    if z = Complex.Zero then None
    elif a = floor a && a <= 0.0 then
        // целое a ≤ 0: Γ(0,z) = E₁(z) и вниз по Γ(a,z) = (Γ(a+1,z) − z^a·e^(−z))/a
        let mutable g = e1Complex z
        let mutable k = 0.0
        while k > a do
            let n = k - 1.0
            g <- (g - Complex.Pow(z, n) * Complex.Exp(-z)) / cN n
            k <- n
        Some g
    elif (match gammaRealNum a with Some _ -> true | None -> false) then
        if Complex.Abs z < abs (a + 1.0) then
            (match gammaRealNum a with
             | Some ga -> Some (cN ga - gammaIncSeries a z)
             | None -> None)
        else Some (gammaIncCF a z)
    else None

// INT.SF3: E₁(z) = Γ(0, z): |z| ≤ 2 — ряд DLMF 8.19.? (6.6.1: E₁ = −γ − ln z − Σ(−z)ⁿ/(n·n!)); Re z ≥ 0 — непрерывная дробь
// (DLMF 8.9.2, a = 0); иначе ряд до |z| ≤ 12 (потеря ≈ e^|z| значащих)
and private e1Num (z: Complex) : Complex option =
    if z = Complex.Zero then None
    elif Complex.Abs z <= 2.0 then Some (e1Complex z)
    elif z.Real >= 0.0 then Some (gammaIncCF 0.0 z)
    elif Complex.Abs z <= 12.0 then Some (e1Complex z)
    else None

// E_n(z), целое n ≥ 0: E₀ = e^(−z)/z (DLMF 8.19.1), E₁ = Γ(0, z); рекуррентность n·E_(n+1) = e^(−z) − z·E_n (DLMF 8.19.12)
and private expIntENum (n: int) (z: Complex) : Complex option =
    if n < 0 || n > 60 || z = Complex.Zero then None
    elif n = 0 then Some (Complex.Exp(-z) / z)
    else
        match e1Num z with
        | None -> None
        | Some e1 ->
            let ez = Complex.Exp(-z)
            let mutable e = e1
            for k in 1 .. n - 1 do e <- (ez - z * e) / cN (float k)
            Some e

let numEval (v: LispValue) : Complex option = numEvalEnv Map.empty v

// ВАЖНО: eval-num/num-abs НЕ упрощают выражение — арифметика алгебраических чисел степени >= 4 в simplify
// раздувает степень минимального многочлена (проверка решений идёт только численно)
// (eval-num e) → float, комплексный вид (+ re (* im %i)) или само выражение, если вычислить нельзя
let evalNum (e: LispValue) : LispValue =
    match numEval e with
    | Some z when z.Imaginary = 0.0 -> LispFloat z.Real
    | Some z ->
        let im = LispList [LispSym "*"; LispFloat z.Imaginary; LispSym "%i"]
        if z.Real = 0.0 then im else LispList [LispSym "+"; LispFloat z.Real; im]
    | None -> e

// (num-abs e) → модуль численного значения (float) или #f, если выражение численно не вычисляется
// (NaN и бесконечность — тоже число: +inf для деления на нуль)
let numAbs (e: LispValue) : LispValue =
    match numEval e with
    | Some z ->
        let m = Complex.Abs z
        LispFloat (if Double.IsNaN m then Double.PositiveInfinity else m)
    | None -> LispBool false
