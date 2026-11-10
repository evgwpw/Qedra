// Интегрирование рациональных функций промышленного уровня (Шаг 21h).
//
// Алгоритмы (источник — Bronstein, «Symbolic Integration Tutorial», ISSAC'98, §1.2–1.3; Bronstein, «Symbolic
// Integration I», гл. 2; Mack 1975 — линейная редукция Эрмита; Lazard–Rioboo–Trager 1990):
//   1. деление с остатком: f = P + A/D, ∫P — многочлен;
//   2. редукция Эрмита (Мак, линейная): A/D = g' + h, у h знаменатель бесквадратный;
//   3. ЛРТ: R(t) = res_x(D, A − t·D') считается субрезультантной PRS (Brown–Collins; Bronstein §1.5), R = Π Q_i^i —
//      бесквадратное разложение Юна; для Q_i при i < deg D берётся член PRS степени i по x, pp_x от него; при i = deg D
//      берётся сам D. Ответ: Σ_i Σ_{Q_i(α)=0} α·log S_i(α, x).
// Коэффициенты — ℚ(параметры): мономы по параметрам — «нижние» переменные MPoly, t и x — две старшие (t < x).
// Деления в K[v] (K — поле частных ℚ[нижние переменные]) ведутся над парами «числитель/знаменатель-по-параметрам» (KP);
// субрезультантная PRS работает над целостным кольцом ℚ[параметры, t] напрямую (все деления точные).
// Шаг 21h': файл — чистая алгебра (без типов Lisp); выражения (rat-integrate, rat-integrate-log) — RatIntExpr.fs
module RatInt

open System.Numerics
open Rational
open MPoly
open PolyGcd
open Subresultant

// ======================= K[v]: многочлены над полем частных ℚ[нижние переменные] =======================
// Значение N/D, где D — многочлен только от переменных, лежащих ниже v (скаляр поля K); N — многочлен от v с
// коэффициентами из ℚ[нижние]. Нормализация: D — целый примитивный многочлен, у N и D нет общего множителя.
type KP = { N: MPoly; D: MPoly }

let kzero : KP = { N = zero; D = one }
let kone : KP = { N = one; D = one }
let kIsZero (a: KP) : bool = isZero a.N

let kmk (n: MPoly) (d: MPoly) : KP =
    if isZero n then kzero
    else
        let (c, dp) = primitiveInt d
        let n1 = if ratCompare c (1I, 1I) = 0 then n else mulConst (ratDiv (1I, 1I) c) n
        if isOne dp then { N = n1; D = one }
        else
            let g = gcd (unitNormal n1) dp
            if isOne g then { N = n1; D = dp }
            else { N = divExactExn n1 g; D = divExactExn dp g }

let ofPoly (p: MPoly) : KP = kmk p one

let kneg (a: KP) : KP = { N = neg a.N; D = a.D }

let kadd (a: KP) (b: KP) : KP =
    if kIsZero a then b
    elif kIsZero b then a
    elif a.D = b.D then kmk (add a.N b.N) a.D
    else kmk (add (mul a.N b.D) (mul b.N a.D)) (mul a.D b.D)

let ksub (a: KP) (b: KP) : KP = kadd a (kneg b)

let kmul (a: KP) (b: KP) : KP =
    if kIsZero a || kIsZero b then kzero else kmk (mul a.N b.N) (mul a.D b.D)

// Степень по v (−1 для нуля)
let kdeg (v: int) (a: KP) : int = if kIsZero a then -1 else degIn v a.N

let kderiv (v: int) (a: KP) : KP = kmk (deriv v a.N) a.D

// Обратный к ненулевому скаляру поля (многочлену степени 0 по v)
let kinv (a: KP) : KP = kmk a.D a.N

// Деление с остатком в K[v]: a = q·b + r, deg r < deg b
let kdivmod (v: int) (a: KP) (b: KP) : KP * KP =
    if kIsZero b then failwith "RatInt: деление на нуль"
    let db = degIn v b.N
    if db = 0 then (kmk (mul a.N b.D) (mul a.D b.N), kzero)
    elif kIsZero a || degIn v a.N < db then (kzero, a)
    else
        // lc(b)^e·a = q·b.N + r;  b.N = b.D·b  ⇒  a = (q·b.D/(lc^e·a.D))·b + r/(lc^e·a.D)
        let (q, r, e) = pseudoDivMod a.N b.N
        let den = mul (pow (lcMain b.N) e) a.D
        (kmk (mul q b.D) den, kmk r den)

let kexact (v: int) (a: KP) (b: KP) : KP =
    let (q, r) = kdivmod v a b
    if not (kIsZero r) then failwith "RatInt: деление нацело невозможно"
    q

// Примитивная по v часть (единица поля K отбрасывается)
let private ppV (v: int) (p: MPoly) : MPoly =
    if isZero p then zero
    elif mainVar p <> v then one
    else unitNormal (divExactExn p (contentMain p))

// НОД в K[v] (определён с точностью до скаляра из K): примитивный по v, целые коэффициенты
let kgcd (v: int) (a: KP) (b: KP) : KP =
    if kIsZero a && kIsZero b then kzero
    else { N = ppV v (gcd (unitNormal a.N) (unitNormal b.N)); D = one }

// Расширенный Евклид в K[v]: (g, s, t), s·a + t·b = g
let kext (v: int) (a: KP) (b: KP) : KP * KP * KP =
    let mutable r0, r1 = a, b
    let mutable s0, s1 = kone, kzero
    let mutable t0, t1 = kzero, kone
    while not (kIsZero r1) do
        let (q, r2) = kdivmod v r0 r1
        r0 <- r1
        r1 <- r2
        let s2 = ksub s0 (kmul q s1)
        s0 <- s1
        s1 <- s2
        let t2 = ksub t0 (kmul q t1)
        t0 <- t1
        t1 <- t2
    (r0, s0, t0)

// Диофантова версия (Bronstein §1.3): B·a + C·b = c, deg B < deg b; (a, b) взаимно просты (иначе c должен делиться на НОД)
let kdioph (v: int) (a: KP) (b: KP) (c: KP) : KP * KP =
    let (g, s, t) = kext v a b
    let (q, r) = kdivmod v c g
    if not (kIsZero r) then failwith "RatInt: диофантово уравнение неразрешимо (c не делится на НОД(a, b))"
    let s1 = kmul q s
    let t1 = kmul q t
    if kdeg v s1 >= kdeg v b then
        let (q2, r2) = kdivmod v s1 b
        (r2, kadd t1 (kmul q2 a))
    else (s1, t1)

// ======================= Бесквадратное разложение (Юн) =======================
// p ∈ ℚ[нижние][v]: возвращает [(A_j, j)], p = c · Π A_j^j с точностью до скаляра c ∈ K; A_j бесквадратны, попарно взаимно
// просты, примитивны по v (старший по v хотя бы один коэффициент не константа поля K не требуется). Источник:
// Bronstein, Symbolic Integration I, §1.7 (Yun 1976); в Tutorial §1.2 описан более простой, но менее эффективный вариант.
let yun (v: int) (p: MPoly) : (MPoly * int) list =
    if degIn v p <= 0 then []
    else
        let s = ppV v p
        let s' = deriv v s
        let sm = ppV v (gcd s s')
        let mutable sstar = divExactExn s sm
        let mutable y = divExactExn s' sm
        let mutable z = sub y (deriv v sstar)
        let res = ResizeArray<MPoly * int>()
        let mutable k = 1
        while not (isZero z) do
            let ak = ppV v (gcd sstar z)
            if degIn v ak > 0 then res.Add (ak, k)
            sstar <- divExactExn sstar ak
            y <- divExactExn z ak
            z <- sub y (deriv v sstar)
            k <- k + 1
        if degIn v sstar > 0 then res.Add (sstar, k)
        List.ofSeq res

// ======================= Редукция Эрмита (Мак, линейная версия) =======================
// A/D = g' + h, g = gnum/gden, h = hnum/hden (hden бесквадратный). Для deg A ≥ deg D hnum может иметь степень ≥ deg hden.
// Bronstein, Symbolic Integration I, §2.2 (Mack); Tutorial §1.2 — квадратичная версия (V = D_m, U = D/V^m), здесь —
// линейная: по одному шагу на кратность, без частичных дробей.
let hermiteReduce (v: int) (a: KP) (d: KP) : (KP * KP) * (KP * KP) =
    let dm0 = kgcd v d (kderiv v d)
    let dstar = kexact v d dm0
    let mutable dm = dm0
    let mutable acur = a
    let parts = ResizeArray<KP * KP>()
    while kdeg v dm > 0 do
        let dm2 = kgcd v dm (kderiv v dm)
        let dms = kexact v dm dm2                                         // Dminusstar
        let aa = kneg (kexact v (kmul dstar (kderiv v dm)) dm)           // −D*·Dminus'/Dminus
        let (b, c) = kdioph v aa dms acur                                // B·aa + C·Dminusstar = A, deg B < deg Dminusstar
        acur <- ksub c (kmul (kderiv v b) (kexact v dstar dms))          // A := C − B'·D*/Dminusstar
        parts.Add (b, dm)
        dm <- dm2
    let gnum = parts |> Seq.fold (fun acc (b, dmi) -> kadd acc (kmul b (kexact v dm0 dmi))) kzero
    ((gnum, dm0), (acur, dstar))

// ======================= ЛРТ =======================
// Субрезультантная PRS (Браун–Коллинз) — модуль Subresultant (общий с НОД многочленов)
// Один член логарифмической части: Σ_{Q(α)=0} α·log S(α, x); Q ∈ ℚ[параметры][t] бесквадратный, Mult — кратность
// корней Q в результанте (= степень gcd(D, A − αD') по x), S ∈ ℚ[параметры, t][x]
type LrtTerm = { Q: MPoly; Mult: int; S: MPoly }

// ∫ A/D, D бесквадратный, gcd(A, D) = 1, x — главная переменная A и D; t — свежая переменная (индекс между параметрами и x)
let lrt (x: int) (t: int) (a: MPoly) (d: MPoly) : LrtTerm list =
    let dd = degIn x d
    let b = sub a (mul (var t) (deriv x d))
    let (res, prs) = subResultant x d b
    if isZero res then failwith "RatInt: нулевой результант (A и D не взаимно просты или D не бесквадратный)"
    [ for (q, i) in yun t res do
        let s =
            if i = dd then d
            else
                match prs |> List.tryFind (fun r -> degIn x r = i) with
                | Some r -> divExactExn r (contentMain r)      // pp_x (Tutorial §1.3)
                | None -> failwithf "RatInt: в субрезультантной PRS нет члена степени %d" i
        yield { Q = q; Mult = i; S = s } ]

// ======================= Драйвер =======================

// Многочлен из KP: ∫ (почленно)
let private integratePoly (x: int) (p: KP) : KP =
    if kIsZero p then kzero
    else
        let mutable acc = zero
        for k in 0 .. degIn x p.N do
            let c = coeffIn x k p.N
            if not (isZero c) then
                acc <- add acc (mul (mulConst (1I, BigInteger (k + 1)) c) (pow (var x) (k + 1)))
        kmk acc p.D

type RatResult =
    { PolyInt: KP              // ∫ полиномиальной части (многочлен от x над K)
      RatPart: KP * KP         // g = gnum/gden — рациональная часть (редукция Эрмита)
      LogScale: KP             // λ: логарифмическая часть = λ · Σ_i Σ_{Q_i(α)=0} α·log S_i(α, x)
      Log: LrtTerm list }      // логарифмическая часть (без множителя λ)

// n/d — рациональная функция (d не зависит от t); x — главная, t — следующая
let integrateRational (x: int) (t: int) (n: MPoly) (d: MPoly) : RatResult =
    let a = ofPoly n
    let dk = ofPoly d
    if kdeg x dk <= 0 then
        // знаменатель без x: многочлен от x
        { PolyInt = integratePoly x (kmk n d); RatPart = (kzero, kone); LogScale = kone; Log = [] }
    else
        let (q0, r0) = kdivmod x a dk
        if kIsZero r0 then { PolyInt = integratePoly x q0; RatPart = (kzero, kone); LogScale = kone; Log = [] }
        else
            let (g, (ha0, hd0)) = hermiteReduce x r0 dk
            // сокращение (A' и D* могут иметь общий множитель)
            let gg = kgcd x ha0 hd0
            let (ha, hd) = if kdeg x gg > 0 then (kexact x ha0 gg, kexact x hd0 gg) else (ha0, hd0)
            let (q1, r1) = kdivmod x ha hd
            let polyPart = integratePoly x (kadd q0 q1)
            if kIsZero r1 then { PolyInt = polyPart; RatPart = g; LogScale = kone; Log = [] }
            else
                // A/D = λ·A'/D', A' и D' — примитивные: целые взаимно простые коэффициенты и без содержания по параметрам
                // (содержание выносится в скаляр λ ∈ K: ∫A/D = λ·∫A'/D'; размер входа субрезультантной PRS — главный
                // множитель стоимости при параметрах)
                let contentOf (p: MPoly) = if mainVar p = x then contentMain p else p
                let cA, cD = contentOf r1.N, contentOf hd.N
                let (ia, aI) = primitiveInt (divExactExn r1.N cA)
                let (id, dI) = primitiveInt (divExactExn hd.N cD)
                let lambda = kmk (mulConst ia (mul cA hd.D)) (mulConst id (mul r1.D cD))
                { PolyInt = polyPart; RatPart = g; LogScale = lambda; Log = lrt x t aI dI }

// ======================= Логарифмическая часть в явном виде =======================
// Для каждого Q_i раскладываем Q_i над ℚ(параметры) на неприводимые f (факторизация шага 21f), S_i приводим по модулю f
// (нормировка: старший коэффициент по x равен 1) и строим члены:
//   f степени 1 (корень a ∈ ℚ(параметры)):       a·log S(a, x)
//   f степени 2, a·t² + b·t + c, Δ = b² − 4ac:
//       вещественная форма (real = true, Δ < 0 доказуемо, т.е. Δ = −κ·g², κ > 0): корни u ± i·v, u = −b/2a, v = g·√κ/2a;
//         u·log(A² + B²) + v·(2·atan(c_1) + 2·atan(c_2) + …)   — LogToReal / LogToAtan (Rioboo; Bronstein §2.8),
//         A + iB = S(u + iv, x); c_j — многочлены от x (непрерывные атаны, см. logToAtan);
//       иначе — корни в радикалах: Σ± α± log S(α±, x), α± = (−b ± √Δ)/2a;
//   f степени ≥ 3: (root-sum t f (* t (log S(t, x)))) — сумма по корням (комплексная форма).

// k-й коэффициент по t (элемент поля K)
let kcoef (t: int) (j: int) (a: KP) : KP = kmk (coeffIn t j a.N) a.D

// Нормировка параметра ЛРТ: p'(t) = c^d · p(t/c) — коэффициент при t^k домножается на c^(d−k).
// d задаётся явно, чтобы масштабировать несколько многочленов одинаково (аргумент логарифма тогда
// умножается на константу, что для log — постоянная интегрирования).
let scaleParamWith (c: bigint) (d: int) (t: int) (p: MPoly) : MPoly =
    [ 0 .. d ]
    |> List.fold
        (fun acc k ->
            let ck = coeffIn t k p
            if isZero ck then acc
            else
                let s = BigInteger.Pow(c, d - k)
                add acc (mul (mulConst (s, 1I) ck) (pow (var t) k)))
        zero

// То же с d = deg_t p: корни умножаются на c, коэффициенты резольвенты уменьшаются
// (1 + 243t^3 + 19683t^6 при c = 3 даёт 27 + 9t^3 + t^6).
let scaleParam (c: bigint) (t: int) (p: MPoly) : MPoly = scaleParamWith c (degIn t p) t p

// Коэффициенты S(t, x) = Σ s_k(t)·x^k по модулю f(t), все умноженные на lc_t(f)^E — общий скаляр поля K (E — наибольшее
// число шагов псевдоделения); результат — многочлены по t степени < deg f. Только псевдоостатки: никаких НОД и дробей
// (в многомерном случае сокращения дробей над ℚ(параметры) на порядки дороже)
let reduceScaled (x: int) (t: int) (f: MPoly) (s: MPoly) : MPoly[] =
    let m = degIn t f
    let lcf = coeffIn t m f
    let cs = Array.init (degIn x s + 1) (fun k -> coeffIn x k s)
    let steps (c: MPoly) = max 0 (degIn t c - m + 1)
    let e = cs |> Array.map steps |> Array.max
    let scaled =
        cs |> Array.map (fun c ->
            let r = if steps c = 0 then c else prem c f
            mul (pow lcf (e - steps c)) r)
    // общий множитель коэффициентов (скаляр поля K): содержание по t и числовое — иначе степени параметров раздуваются
    // множителем lc(f)^E и разрастаются дальше (в вещественной форме, в аргументах log)
    let contentOf (c: MPoly) = if isZero c then zero elif mainVar c = t then contentMain c else c
    let g = scaled |> Array.fold (fun acc c -> if isZero c then acc else gcd acc (contentOf c)) zero
    let scaled1 = if isOne g || isZero g then scaled else scaled |> Array.map (fun c -> if isZero c then c else divExactExn c g)
    let whole = scaled1 |> Array.mapi (fun k c -> mul c (pow (var x) k)) |> Array.fold add zero
    let (cInt, _) = primitiveInt whole
    if ratCompare cInt (1I, 1I) = 0 || ratIsZero cInt then scaled1
    else scaled1 |> Array.map (mulConst (ratDiv (1I, 1I) cInt))

// S(t, x) по модулю f(t); monic — нормированный по x (старший коэффициент 1; обратный по модулю f и сокращения дробей над
// ℚ(параметры) дороги — при параметрах не нормируем: общий скаляр поля K в log(c·S) — постоянная интегрирования);
// элементы — KP по t степени < deg f
let reduceKP (x: int) (t: int) (f: MPoly) (s: MPoly) (monic: bool) : KP[] =
    let red = reduceScaled x t f s |> Array.map ofPoly
    if not monic then red
    else
        let kf = ofPoly f
        let lc = red.[red.Length - 1]
        if kIsZero lc then red
        else
            let (g, inv0, _) = kext t lc kf
            if kdeg t g <> 0 then red
            else
                let inv = kmul inv0 (kinv g)
                red |> Array.map (fun c -> snd (kdivmod t (kmul inv c) kf))

let reduceMonic (x: int) (t: int) (f: MPoly) (s: MPoly) : KP[] = reduceKP x t f s true

// Многочлен Σ c_k x^k как KP (x — главная переменная)
let kpolyOf (x: int) (cs: KP[]) : KP =
    let mutable acc = kzero
    for k in 0 .. cs.Length - 1 do
        if not (kIsZero cs.[k]) then acc <- kadd acc (kmul cs.[k] (kmk (pow (var x) k) one))
    acc

// Аргумент логарифма/атана: многочлен без скаляров поля K (константы вне log — постоянная интегрирования)
let cleanPoly (x: int) (p: KP) : MPoly =
    let n = p.N
    unitNormal (if mainVar n = x then divExactExn n (contentMain n) else n)

// ---------- бесквадратная часть целого: n = κ·s² ----------

let private isqrt (n: BigInteger) : BigInteger =
    if n.Sign <= 0 then 0I
    else
        let mutable r = BigInteger (System.Math.Sqrt (double n))
        while r * r > n do r <- r - 1I
        while (r + 1I) * (r + 1I) <= n do r <- r + 1I
        r

// (κ, s): n = κ·s² (n > 0); пробное деление до 10^6, остаток — полный квадрат или бесквадратный
let sqfreeSplit (n: BigInteger) : BigInteger * BigInteger =
    let mutable r = n
    let mutable kappa = 1I
    let mutable s = 1I
    let mutable d = 2I
    while d <= 1000000I && d * d <= r do
        if (r % d).IsZero then
            let mutable e = 0
            while (r % d).IsZero do
                r <- r / d
                e <- e + 1
            s <- s * BigInteger.Pow(d, e / 2)
            if e % 2 = 1 then kappa <- kappa * d
        d <- if d = 2I then 3I else d + 2I
    let q = isqrt r
    if q * q = r then (kappa, s * q) else (kappa * r, s)

// Знак многочлена Δ от параметров: Δ = ±κ·g² (g — элемент поля K) для всех вещественных значений параметров, если все
// простые множители Δ имеют чётные кратности; иначе знак неизвестен
type SignInfo =
    | Pos of BigInteger * KP
    | Neg of BigInteger * KP
    | Unknown

let classifySign (delta: MPoly) : SignInfo =
    if isZero delta then Unknown
    else
        let (c, fs) = PolyFactor.factorPoly delta
        if fs |> List.exists (fun (_, e) -> e % 2 = 1) then Unknown
        else
            let (cn, cd) = c
            let (kappa, s) = sqfreeSplit (BigInteger.Abs cn * cd)
            let g = fs |> List.fold (fun acc (f, e) -> mul acc (pow f (e / 2))) one
            let gk = kmk (mulConst (s, cd) g) one
            if cn.Sign > 0 then Pos (kappa, gk) else Neg (kappa, gk)

// ---------- LogToAtan (Rioboo; Bronstein §2.8) над ℚ(параметры)(ω), ω² = r ----------
// Элемент — P·ω^E, P ∈ K[x], E ∈ {0, 1}; все операции сохраняют эту форму (чётность E определена структурой алгоритма)
type TP = { P: KP; E: int }

let private tZero : TP = { P = kzero; E = 0 }
let private tIsZero (a: TP) = kIsZero a.P
let private tNeg (a: TP) : TP = { a with P = kneg a.P }
let private tMul (r: KP) (a: TP) (b: TP) : TP =
    let p = kmul a.P b.P
    let e = a.E + b.E
    if tIsZero a || tIsZero b then tZero
    elif e = 2 then { P = kmul p r; E = 0 } else { P = p; E = e }
let private tSub (a: TP) (b: TP) : TP =
    if tIsZero b then a
    elif tIsZero a then tNeg b
    elif a.E <> b.E then failwith "RatInt.logToAtan: разная чётность по ω"
    else { P = ksub a.P b.P; E = a.E }
let private tAdd (a: TP) (b: TP) : TP =
    if tIsZero b then a
    elif tIsZero a then b
    elif a.E <> b.E then failwith "RatInt.logToAtan: разная чётность по ω"
    else { P = kadd a.P b.P; E = a.E }

// a = q·b + rem в K(ω)[x]
let private tDivmod (x: int) (r: KP) (a: TP) (b: TP) : TP * TP =
    let (q0, r0) = kdivmod x a.P b.P
    let remT = if kIsZero r0 then tZero else { P = r0; E = a.E }
    if kIsZero q0 then (tZero, remT)
    else
        match a.E - b.E with
        | 0 -> ({ P = q0; E = 0 }, remT)
        | 1 -> ({ P = q0; E = 1 }, remT)
        | _ -> ({ P = kmul q0 (kinv r); E = 1 }, remT)        // ω⁻¹ = ω/r

let private tDeg (x: int) (a: TP) : int = kdeg x a.P

// s·b + t·a = g
let private tExt (x: int) (r: KP) (b: TP) (a: TP) : TP * TP * TP =
    let mutable r0, r1 = b, a
    let mutable s0, s1 = { P = kone; E = 0 }, tZero
    let mutable t0, t1 = tZero, { P = kone; E = 0 }
    while not (tIsZero r1) do
        let (q, r2) = tDivmod x r r0 r1
        r0 <- r1
        r1 <- r2
        let s2 = tSub s0 (tMul r q s1)
        s0 <- s1
        s1 <- s2
        let t2 = tSub t0 (tMul r q t1)
        t0 <- t1
        t1 <- t2
    (r0, s0, t0)

// Аргументы атанов c_j: i·log((A + iB)/(A − iB)) = 2·Σ atan(c_j) + const (B ≠ 0)
let rec logToAtanT (x: int) (r: KP) (a: TP) (b: TP) : TP list =
    let (q, rem) = tDivmod x r a b
    if tIsZero rem then (if tIsZero q then [] else [ q ])
    elif tDeg x a < tDeg x b then logToAtanT x r (tNeg b) a
    else
        let (g, d, c) = tExt x r b (tNeg a)            // d·b + c·(−a) = g
        let num = tAdd (tMul r a d) (tMul r b c)       // A·D + B·C
        let (u, rem2) = tDivmod x r num g
        if not (tIsZero rem2) then failwith "RatInt.logToAtan: деление (A·D + B·C)/G не нацело"
        let rest = logToAtanT x r d c
        if tIsZero u then rest else u :: rest

// То же для обычных многочленов (r = 1, без ω): публичная обёртка для тестов
let logToAtan (x: int) (a: KP) (b: KP) : KP list =
    logToAtanT x kone { P = a; E = 0 } { P = b; E = 0 } |> List.map (fun u -> u.P)

// ---------- Точная проверка: тождество A/D = (∫полином)' + g' + λ·Σ_f Tr_{K[t]/(f)}(t·S_x/S) в рациональной точке ----------
// Подставляются рациональные значения x и всех параметров; след вычисляется ТОЧНО в ℚ[t]/(f) (степенные суммы корней f,
// обращение S(x0, t) по модулю f расширенным Евклидом) — без численных корней, поэтому проверка надёжна и для
// высоких степеней, где вещественная арифметика теряет точность из-за разброса корней.

let private powerSums (t: int) (f: KP) (upto: int) : KP[] =
    let m = kdeg t f
    let am = kcoef t m f
    let c = Array.init (m + 1) (fun i -> if i = 0 then kone else kmul (kcoef t (m - i) f) (kinv am))
    let p = Array.create (upto + 1) kzero
    p.[0] <- ofPoly (ofInt (BigInteger m))
    for k in 1 .. upto do
        let mutable s = if k <= m then kmul (ofPoly (ofInt (BigInteger k))) c.[k] else kzero
        for i in 1 .. min (k - 1) m do
            s <- kadd s (kmul c.[i] p.[k - i])
        p.[k] <- kneg s
    p

// Σ_{f(α)=0} φ(α) для φ ∈ K[t]/(f) (корни — с кратностью; f бесквадратный)
let traceMod (t: int) (f: KP) (phi: KP) : KP =
    let ps = powerSums t f (max (kdeg t phi) 0)
    let mutable acc = kzero
    for j in 0 .. kdeg t phi do
        acc <- kadd acc (kmul (kcoef t j phi) ps.[j])
    acc

let private substPoint (vars: (int * Q) list) (p: MPoly) : MPoly =
    vars |> List.fold (fun acc (v, q) -> subst v (Const (ratNorm q)) acc) p

// factors — (f, S-коэффициенты, множитель): множитель 1/c появляется у членов, где параметр нормирован
// подстановкой t → t/c (см. RatIntExpr.rootSumTerm); он умножает вклад Σ_α α·S_x/S
let verifyExact (x: int) (t: int) (n: MPoly) (d: MPoly) (r: RatResult) (factors: (MPoly * KP[] * Q) list) : bool =
    let qOf (p: MPoly) : Q = match p with Const q -> q | _ -> failwith "RatInt.verifyExact: не число"
    let attempt (x0: Q) (pv: Q list) : bool option =
        let pars = pv |> List.mapi (fun i q -> (i, q)) |> List.filter (fun (i, _) -> i < t)
        let vars = pars @ [ (x, x0) ]
        let sp (p: MPoly) = substPoint vars p
        let dv = qOf (sp d)
        // значение N/D в точке (без сокращений дробей над ℚ(параметры): только подстановки и рациональная арифметика)
        let evND (num: MPoly) (den: MPoly) : Q option =
            let dd = qOf (sp den)
            if ratIsZero dd then None else Some (ratDiv (qOf (sp num)) dd)
        let evK (k: KP) : Q option = evND k.N k.D
        if ratIsZero dv then None
        else
            let rhs = ratDiv (qOf (sp n)) dv
            let (gn, gd) = r.RatPart
            let gPrime =
                if kIsZero gn then Some (0I, 1I)
                else
                    match evK gn, evND (deriv x gn.N) gn.D, evK gd, evND (deriv x gd.N) gd.D with
                    | Some a, Some a', Some b, Some b' when not (ratIsZero b) ->
                        Some (ratDiv (ratSub (ratMul a' b) (ratMul a b')) (ratMul b b))
                    | _ -> None
            let parts = [ (if kIsZero r.PolyInt then Some (0I, 1I) else evND (deriv x r.PolyInt.N) r.PolyInt.D)
                          gPrime
                          evK r.LogScale ]
            if parts |> List.exists Option.isNone then None
            else
                let pPoly, pRat, lam = parts.[0].Value, parts.[1].Value, parts.[2].Value
                let xp (k: int) : Q =
                    let mutable acc = (1I, 1I)
                    for _ in 1 .. k do acc <- ratMul acc x0
                    acc
                let parOnly = pars
                let toQT (k: KP) : KP = kmk (substPoint parOnly k.N) (substPoint parOnly k.D)
                let mutable total : Q = (0I, 1I)
                let mutable ok = true
                for (f, cs, mul) in factors do
                    if ok then
                        let f0 = toQT (ofPoly f)
                        let cs0 = cs |> Array.map toQT
                        let mutable s0 = kzero
                        let mutable sx = kzero
                        for k in 0 .. cs0.Length - 1 do
                            s0 <- kadd s0 (kmul cs0.[k] (kmk (Const (ratNorm (xp k))) one))
                            if k >= 1 then
                                sx <- kadd sx (kmul cs0.[k] (kmk (Const (ratNorm (ratMul (BigInteger k, 1I) (xp (k - 1))))) one))
                        if kIsZero s0 || kdeg t f0 <= 0 then ok <- false
                        else
                            let (g, s, _) = kext t s0 f0
                            if kdeg t g <> 0 then ok <- false
                            else
                                let inv = kmul s (kinv g)
                                let phi = snd (kdivmod t (kmul (kmul (kmk (var t) one) sx) inv) f0)
                                let tr = traceMod t f0 phi
                                match tr.N, tr.D with
                                | Const a, Const b when not (ratIsZero b) -> total <- ratAdd total (ratMul mul (ratDiv a b))
                                | _ -> ok <- false
                if not ok then None
                else
                    let lhs = ratAdd (ratAdd pPoly pRat) (ratMul lam total)
                    Some (ratCompare lhs rhs = 0)
    let points = [ (2I, 7I); (3I, 11I); (5I, 13I); (7I, 17I); (11I, 19I) ]
    let mutable verdict : bool option = None
    let mutable i = 0
    while verdict.IsNone && i < points.Length do
        let pv = [ for j in 0 .. t - 1 -> (BigInteger (j + 2 + i), BigInteger (j + 3 + 2 * i)) ]
        verdict <- attempt points.[i] pv
        i <- i + 1
    match verdict with
    | Some false -> false
    | _ -> true

// ТОЧНОЕ значение Σ_{Q(α)=0} N(α)/D(α) для многочленов Q, N, D ∈ ℚ[t] (коэффициенты по возрастанию степени, Q — степени ≥ 1
// и без кратных корней не требуется): φ = N/D mod Q в ℚ[t]/(Q), след — степенные суммы корней Q (traceMod). None — D не
// обратим по модулю Q или след не рационален. Вынесено из SolveNum (шаг 21h'). Исход в терминах единого контракта
// (Outcome): Answer — значение; Unknown — метод неприменим, с причиной
let exactRootSumQ (qn: Q[]) (nn: Q[]) (dd: Q[]) : Outcome.Outcome<Q> =
    let zeroQ = (0I, 1I)
    let toKP (cs: Q[]) = ofPoly (mk 0 (cs |> Array.map (fun q -> Const (ratNorm q))))
    let kq = toKP qn
    if kdeg 0 kq < 1 then Outcome.Unknown "Q — константа: корней нет"
    else
        let kn, kd = toKP nn, toKP dd
        if kIsZero kd then Outcome.Unknown "знаменатель тела суммы равен нулю"
        else
            let (g, s, _) = kext 0 kd kq
            if kdeg 0 g <> 0 then Outcome.Unknown "знаменатель не обратим по модулю Q (общий множитель с Q)"
            else
                let phi = snd (kdivmod 0 (kmul kn (kmul s (kinv g))) kq)
                let tr = traceMod 0 kq phi
                match tr.N, tr.D with
                | Const a, Const b when not (ratIsZero b) -> Outcome.Answer (ratDiv a b)
                | _ -> if kIsZero tr then Outcome.Answer zeroQ else Outcome.Unknown "след не рационален (коэффициенты содержат параметры)"
