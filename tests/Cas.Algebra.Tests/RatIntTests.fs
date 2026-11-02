// Тесты шага 21h (коммит 1): субрезультантная PRS, бесквадратное разложение Юна, редукция Эрмита (Мак), ЛРТ (RatInt.fs, Subresultant.fs).
// Проверки — тождества: Эрмит A/D = g' + h точно в K(x); ЛРТ — Σ_{Q(α)=0} α·S_x(α,x)/S(α,x) = A/D численно по корням Q.
// Шаг 21h': чистая алгебра (Cas.Algebra.Tests) — многочлены из инфиксной записи (PolyText); корни Q — NumRoots.
// Тесты моста выражений (rat-integrate, root-sum) остались в Lisp.Tests (RatIntExprTests.fs)
module RatIntTests

open System
open System.Numerics
open Xunit
open Rational
open MPoly
open PolyGcd
open Subresultant
open RatInt
open PolyText

let private ctxOf2 (srcs: string list) (mains: string list) : VarCtx = ctxOf srcs mains

// ---------- вычисление MPoly в комплексных точках ----------

let rec private evalC (vals: Complex[]) (p: MPoly) : Complex =
    match p with
    | Const (n, d) -> Complex(double n / double d, 0.0)
    | Poly (v, cs) ->
        let x = vals.[v]
        let mutable acc = Complex.Zero
        for i in cs.Length - 1 .. -1 .. 0 do
            acc <- acc * x + evalC vals cs.[i]
        acc

// корни многочлена Q(t) (коэффициенты — числа) → комплексные числа (как nroots: почти вещественные — вещественные)
let private rootsOf (t: int) (q: MPoly) : Complex list =
    let cs = Array.init (degIn t q + 1) (fun k ->
        match coeffIn t k q with
        | Const (n, d) -> double n / double d
        | _ -> failwith "коэффициент Q — не число")
    let isReal (z: Complex) = abs z.Imaginary <= 1e-7 * (1.0 + Complex.Abs z)
    NumRoots.rootsOfCoeffs cs |> List.map (fun z -> if isReal z then Complex(z.Real, 0.0) else z)

// ---------- Юн ----------

let private sameFactors (ctx: VarCtx) (expected: (string * int) list) (actual: (MPoly * int) list) =
    let key (p: MPoly, k: int) = (k, sprintf "%A" p)
    let got = actual |> List.map (fun (p, k) -> (unitNormal p, k)) |> List.sortBy key
    let exp = expected |> List.map (fun (s, k) -> (unitNormal (polyIn ctx s), k)) |> List.sortBy key
    Assert.Equal<(MPoly * int) list>(exp, got)

[<Fact>]
let ``Юн: (x-1)(x+2)^2(x^2+1)^3`` () =
    let ctx = ctxOf2 [ "x" ] [ "x" ]
    let x = idx ctx "x"
    let p = polyIn ctx "(x-1)*(x+2)^2*(x^2+1)^3"
    sameFactors ctx [ "x-1", 1; "x+2", 2; "x^2+1", 3 ] (yun x p)

[<Fact>]
let ``Юн: пропуск кратностей (x^2-2)^4 (x-5)`` () =
    let ctx = ctxOf2 [ "x" ] [ "x" ]
    let x = idx ctx "x"
    sameFactors ctx [ "x-5", 1; "x^2-2", 4 ] (yun x (polyIn ctx "(x^2-2)^4*(x-5)"))

[<Fact>]
let ``Юн: бесквадратный и константа`` () =
    let ctx = ctxOf2 [ "x" ] [ "x" ]
    let x = idx ctx "x"
    sameFactors ctx [ "x^3+x+1", 1 ] (yun x (polyIn ctx "x^3+x+1"))
    Assert.Empty(yun x (polyIn ctx "7"))

[<Fact>]
let ``Юн: параметры — содержание по параметрам отбрасывается (K[t])`` () =
    let ctx = ctxOf2 [ "t"; "a" ] [ "t" ]
    let t = idx ctx "t"
    // (a·t − 1)·(t + a)^2·(t^2 + a)^3 · a^5: множители примитивны по t
    let p = polyIn ctx "a^5*(a*t-1)*(t+a)^2*(t^2+a)^3"
    sameFactors ctx [ "a*t-1", 1; "t+a", 2; "t^2+a", 3 ] (yun t p)

// ---------- субрезультанты ----------

let private rng = Random(21)

let private randPoly (v: string) (deg: int) (extra: string list) : string =
    let coef () =
        match extra with
        | [] -> string (rng.Next(-5, 6))
        | _ ->
            let e = extra.[rng.Next extra.Length]
            sprintf "(%d + %d*%s)" (rng.Next(-4, 5)) (rng.Next(-3, 4)) e
    String.Join(" + ", [ for k in 0 .. deg -> sprintf "%s*%s^%d" (coef ()) v k ])

[<Fact>]
let ``субрезультант: результант совпадает с матрицей Сильвестра (случайные, параметр t)`` () =
    for trial in 1 .. 40 do
        let da, db = rng.Next(1, 6), rng.Next(1, 6)
        let sa, sb = randPoly "x" da [ "t" ], randPoly "x" db [ "t" ]
        let ctx = ctxOf2 [ sa; sb ] [ "t"; "x" ]
        let x = idx ctx "x"
        let a, b = polyIn ctx sa, polyIn ctx sb
        let expected = Subresultant.resultantPoly x a b
        let (r, _) = subResultant x a b
        Assert.True((r = expected), sprintf "trial %d: (%s), (%s): %s != %s" trial sa sb (show ctx r) (show ctx expected))

[<Fact>]
let ``субрезультант: результант от D и A − tD' (знак и степени)`` () =
    for (d, a) in [ "x^2+x+1", "1"; "x^3-2", "x^2"; "x^4+1", "1"; "x^5+x+1", "x^2+3"; "x^6-x^2+7", "x^3-1" ] do
        let ctx = ctxOf2 [ d; a ] [ "t"; "x" ]
        let x, t = idx ctx "x", idx ctx "t"
        let pd, pa = polyIn ctx d, polyIn ctx a
        let b = sub pa (mul (var t) (deriv x pd))
        let expected = Subresultant.resultantPoly x pd b
        let (r, _) = subResultant x pd b
        Assert.True((r = expected), sprintf "D = %s: %s != %s" d (show ctx r) (show ctx expected))

[<Fact>]
let ``субрезультант: дефектные скачки — степени PRS для x^5+1 и x^4+1`` () =
    let degs (d: string) =
        let ctx = ctxOf2 [ d ] [ "t"; "x" ]
        let x, t = idx ctx "x", idx ctx "t"
        let pd = polyIn ctx d
        let b = sub one (mul (var t) (deriv x pd))
        let (_, prs) = subResultant x pd b
        prs |> List.map (degIn x)
    Assert.Equal<int list>([ 5; 4; 1; 0 ], degs "x^5+1")
    Assert.Equal<int list>([ 4; 3; 1; 0 ], degs "x^4+1")

[<Fact>]
let ``субрезультант: нулевой результант при общем множителе`` () =
    let ctx = ctxOf2 [ "x" ] [ "x" ]
    let x = idx ctx "x"
    let (r, _) = subResultant x (polyIn ctx "(x-1)*(x-2)") (polyIn ctx "(x-1)*(x+3)")
    Assert.True(isZero r)

[<Fact>]
let ``субрезультант: параметры a, b (дефект по главным коэффициентам)`` () =
    let sa, sb = "a*x^3 + b*x + 1", "b*x^2 + a*t*x + 2"
    let ctx = ctxOf2 [ sa; sb ] [ "t"; "x" ]
    let x = idx ctx "x"
    let a, b = polyIn ctx sa, polyIn ctx sb
    Assert.True((fst (subResultant x a b) = Subresultant.resultantPoly x a b))

// ---------- K[v]: деление, Евклид ----------

[<Fact>]
let ``KP: расширенный Евклид и диофантово уравнение над ℚ(a)`` () =
    let ctx = ctxOf2 [ "x"; "a" ] [ "x" ]
    let x = idx ctx "x"
    let mk (s: string) = ofPoly (polyIn ctx s)
    let a, b = mk "x^3 + a*x + 1", mk "a*x^2 - 3"
    let (g, s, t) = kext x a b
    Assert.True(kIsZero (ksub (kadd (kmul s a) (kmul t b)) g))
    Assert.Equal(0, kdeg x g)
    let c = mk "x^2 + a"
    let (bb, cc) = kdioph x a b c
    Assert.True(kIsZero (ksub (kadd (kmul bb a) (kmul cc b)) c))
    Assert.True(kdeg x bb < kdeg x b)

// ---------- Эрмит ----------

// A/D = g' + h точно в K(x)
let private hermiteHolds (n: string) (d: string) (mains: string list) : unit =
    let ctx = ctxOf2 [ n; d ] mains
    let x = idx ctx "x"
    let a, dd = ofPoly (polyIn ctx n), ofPoly (polyIn ctx d)
    let ((gn, gd), (hn, hd)) = hermiteReduce x a dd
    // A·gd²·hd = (gn'·gd − gn·gd')·D·hd + hn·D·gd²
    let lhs = kmul a (kmul (kmul gd gd) hd)
    let rhs =
        kadd (kmul (ksub (kmul (kderiv x gn) gd) (kmul gn (kderiv x gd))) (kmul dd hd))
             (kmul hn (kmul dd (kmul gd gd)))
    Assert.True(kIsZero (ksub lhs rhs), sprintf "Эрмит: %s / %s" n d)
    // знаменатель h бесквадратный
    let g = kgcd x hd (kderiv x hd)
    Assert.Equal(0, kdeg x g)

[<Fact>]
let ``Эрмит: пример 36/(x^5-2x^4-2x^3+4x^2+x-2)`` () =
    hermiteHolds "36" "x^5 - 2*x^4 - 2*x^3 + 4*x^2 + x - 2" [ "x" ]
    // рациональная часть (12x+6)/(x^2-1)
    let ctx = ctxOf2 [ "x" ] [ "x" ]
    let x = idx ctx "x"
    let ((gn, gd), _) = hermiteReduce x (ofPoly (polyIn ctx "36")) (ofPoly (polyIn ctx "x^5 - 2*x^4 - 2*x^3 + 4*x^2 + x - 2"))
    let expN, expD = ofPoly (polyIn ctx "12*x+6"), ofPoly (polyIn ctx "x^2-1")
    // gn/gd = expN/expD  ⇔  gn·expD = expN·gd
    Assert.True(kIsZero (ksub (kmul gn expD) (kmul expN gd)), "рациональная часть ≠ (12x+6)/(x^2-1)")

[<Fact>]
let ``Эрмит: (x^7-24x^4-4x^2+8x-8)/(x^8+6x^6+12x^4+8x^2) (кратности 2 и 3)`` () =
    hermiteHolds "x^7 - 24*x^4 - 4*x^2 + 8*x - 8" "x^8 + 6*x^6 + 12*x^4 + 8*x^2" [ "x" ]

[<Fact>]
let ``Эрмит: кратность 3 и параметры 1/(x(a+bx)^3)`` () =
    hermiteHolds "1" "x*(a+b*x)^3" [ "x" ]
    hermiteHolds "x^2+a" "(x^2+b)^4*(x-a)" [ "x" ]

[<Fact>]
let ``Эрмит: степень числителя ≥ степени знаменателя`` () =
    hermiteHolds "x^9+3*x^4+1" "(x^2+1)^3*(x-1)^2" [ "x" ]

[<Fact>]
let ``Эрмит: бесквадратный знаменатель — g = 0`` () =
    let ctx = ctxOf2 [ "x" ] [ "x" ]
    let x = idx ctx "x"
    let ((gn, _), (hn, hd)) = hermiteReduce x (ofPoly (polyIn ctx "x+1")) (ofPoly (polyIn ctx "x^3+x+1"))
    Assert.True(kIsZero gn)
    Assert.Equal(3, kdeg x hd)
    Assert.Equal(1, kdeg x hn)

[<Fact>]
let ``Эрмит: случайные D = Π f_i^k_i`` () =
    let fs = [ "x+1"; "x^2+x+1"; "x^2-2"; "x-3"; "x^3-x-1" ]
    for trial in 1 .. 15 do
        let picks = fs |> List.filter (fun _ -> rng.Next 2 = 0)
        let picks = if picks.IsEmpty then [ fs.[0] ] else picks
        let d = String.Join("*", picks |> List.map (fun f -> sprintf "(%s)^%d" f (rng.Next(1, 4))))
        hermiteHolds (randPoly "x" (rng.Next(0, 6)) []) d [ "x" ]

// ---------- ЛРТ ----------

// F' = f: производная полиномиальной и рациональной частей + Σ α·S_x/S по корням Q при x = x0 (численно)
let private lrtNumeric (n: string) (d: string) : unit =
    let ctx = ctxOf2 [ n; d ] [ "t"; "x" ]
    let x, t = idx ctx "x", idx ctx "t"
    let (pn, pd) = normalizeFrac (polyIn ctx n, polyIn ctx d)
    let r = integrateRational x t pn pd
    let x0 = 0.37
    let vals = Array.create ctx.Names.Length Complex.Zero
    vals.[x] <- Complex(x0, 0.0)
    let evalK (k: KP) = evalC vals k.N / evalC vals k.D
    // производная полиномиальной части
    let dPoly = evalK (kderiv x r.PolyInt)
    let (gn, gd) = r.RatPart
    let dg = evalK (ksub (kmul (kderiv x gn) gd) (kmul gn (kderiv x gd))) / (evalK (kmul gd gd))
    let logPart =
        r.Log |> List.fold (fun acc tm ->
            let sx = deriv x tm.S
            rootsOf t tm.Q |> List.fold (fun acc2 alpha ->
                vals.[t] <- alpha
                acc2 + alpha * evalC vals sx / evalC vals tm.S) acc) Complex.Zero
    vals.[t] <- Complex.Zero
    let expected = evalC vals pn / evalC vals pd
    let diff = Complex.Abs(dPoly + dg + evalK r.LogScale * logPart - expected)
    Assert.True(diff < 1e-8 * (1.0 + Complex.Abs expected), sprintf "ЛРТ: (%s)/(%s): невязка %g" n d diff)

[<Fact>]
let ``ЛРТ: эталон — 1/(x^2+x+1) и 12/(x^2-x-2)`` () =
    let ctx = ctxOf2 [ "x" ] [ "t"; "x" ]
    let x, t = idx ctx "x", idx ctx "t"
    let r1 = integrateRational x t (polyIn ctx "1") (polyIn ctx "x^2+x+1")
    Assert.Equal(1, r1.Log.Length)
    Assert.Equal(polyIn ctx "1 + 3*t^2", r1.Log.Head.Q)
    Assert.Equal(1, r1.Log.Head.Mult)
    let r2 = integrateRational x t (polyIn ctx "12") (polyIn ctx "x^2-x-2")
    // A = 12 выносится в скаляр λ = 12 (содержание), остаётся 1/(x² − x − 2) с вычетами ±1/3: Q = 9t² − 1
    Assert.Equal(polyIn ctx "9*t^2 - 1", unitNormal r2.Log.Head.Q)
    Assert.Equal(polyIn ctx "12", r2.LogScale.N)
    lrtNumeric "1" "x^2+x+1"
    lrtNumeric "12" "x^2-x-2"

[<Fact>]
let ``ЛРТ: случай i = deg D — x/(x^2-9) и x^2/(x^3-5)`` () =
    let ctx = ctxOf2 [ "x" ] [ "t"; "x" ]
    let x, t = idx ctx "x", idx ctx "t"
    let r = integrateRational x t (polyIn ctx "x") (polyIn ctx "x^2-9")
    Assert.Equal(1, r.Log.Length)
    Assert.Equal(2, r.Log.Head.Mult)
    Assert.Equal(polyIn ctx "x^2 - 9", r.Log.Head.S)
    Assert.Equal(polyIn ctx "2*t - 1", r.Log.Head.Q)
    let r3 = integrateRational x t (polyIn ctx "x^2") (polyIn ctx "x^3-5")
    Assert.Equal(3, r3.Log.Head.Mult)
    Assert.Equal(polyIn ctx "x^3 - 5", r3.Log.Head.S)

[<Fact>]
let ``ЛРТ: дефектные PRS — 1/(x^5+1), 1/(x^4+1), 1/(x^3+2)`` () =
    let ctx = ctxOf2 [ "x" ] [ "t"; "x" ]
    let x, t = idx ctx "x", idx ctx "t"
    let r5 = integrateRational x t (polyIn ctx "1") (polyIn ctx "x^5+1")
    Assert.Equal(polyIn ctx "3125*t^5 - 1", r5.Log.Head.Q)
    Assert.Equal(1, r5.Log.Head.Mult)
    Assert.Equal(1, degIn x r5.Log.Head.S)
    let r4 = integrateRational x t (polyIn ctx "1") (polyIn ctx "x^4+1")
    Assert.Equal(polyIn ctx "256*t^4 + 1", r4.Log.Head.Q)
    for (n, d) in [ "1", "x^5+1"; "1", "x^4+1"; "1", "x^3+2"; "x", "x^5+1"; "x^2+1", "x^4+1"; "1", "x^7+3"; "x^3", "x^8-x+1" ] do
        lrtNumeric n d

[<Fact>]
let ``ЛРТ: Эрмит + логарифмы (числитель степени ≥ знаменателя, кратности)`` () =
    for (n, d) in [ "36", "x^5-2*x^4-2*x^3+4*x^2+x-2"
                    "x^7-24*x^4-4*x^2+8*x-8", "x^8+6*x^6+12*x^4+8*x^2"
                    "x^3*(x^7-24*x^4-4*x^2+8*x-8)", "x*(x^8+6*x^6+12*x^4+8*x^2)"
                    "x^5-x^4+4*x^3+x^2-x+5", "x^4-2*x^3+5*x^2-4*x+4"
                    "x^4-3*x^2+6", "x^6-5*x^4+5*x^2+4"
                    "x^9+3", "(x^3+x+1)^2*(x-2)"
                    "1", "(x^3+x+1)^3"
                    "x+1", "(x^2+1)^2*(x^2+4)^2" ] do
        lrtNumeric n d

[<Fact>]
let ``ЛРТ: одинаковые вычеты разной кратности (Q_i, i > 1, i < deg D)`` () =
    // (x^2+1)(x^2+4): вычеты в ±i, ±2i — пары совпадают по модулю; 1/(x^4+5x^2+4)
    lrtNumeric "1" "x^4+5*x^2+4"
    // вычеты ∓1/6 по два раза: Q_2 = 36t²−1, i = 2 < deg D = 4
    let ctx = ctxOf2 [ "x" ] [ "t"; "x" ]
    let x, t = idx ctx "x", idx ctx "t"
    let r = integrateRational x t (polyIn ctx "x") (polyIn ctx "(x^2-1)*(x^2-4)")
    Assert.Equal(1, r.Log.Length)
    Assert.Equal(2, r.Log.Head.Mult)
    Assert.Equal(2, degIn x r.Log.Head.S)
    lrtNumeric "x" "(x^2-1)*(x^2-4)"
    lrtNumeric "x^3+2*x" "(x^2-1)*(x^2-4)*(x^2-9)"
    lrtNumeric "1" "x^6-1"
    lrtNumeric "x^2" "x^6-1"
    // найден случайным тестом: три кубических/квартичных множителя Q, кратность 2 (Эрмит), большие коэффициенты
    lrtNumeric "-1+3*x-2*x^2-x^3+2*x^4" "(x^3-x-1)*(x^2+1)*(x^4+1)^2"
    lrtNumeric "x^2" "(x^2+1)*(x^2+4)*(x^2+9)"
    // три вычета одной кратности 2 и один иной: x^3/((x-1)(x+1)(x-2)(x+2)) → вычеты 1/6·…
    lrtNumeric "x^4+1" "(x^2-1)*(x^2-4)*(x+7)"

[<Fact>]
let ``ЛРТ: параметры — вычеты в ℚ(a, b)`` () =
    // 1/(x^2+a^2): Q = 4a²t² + 1; x/((x-a)(x+a)): i = deg D
    let ctx = ctxOf2 [ "a"; "b" ] [ "t"; "x" ]
    let x, t = idx ctx "x", idx ctx "t"
    let r = integrateRational x t (polyIn ctx "1") (polyIn ctx "x^2+a^2")
    Assert.Equal(polyIn ctx "1 + 4*a^2*t^2", r.Log.Head.Q)
    let r2 = integrateRational x t (polyIn ctx "x") (polyIn ctx "(x-a)*(x+a)")
    Assert.Equal(2, r2.Log.Head.Mult)
    let r3 = integrateRational x t (polyIn ctx "1") (polyIn ctx "(x-a)*(x-b)")
    Assert.Equal(1, r3.Log.Length)             // Q_1 = (a−b)²t² − 1 — один бесквадратный множитель (корни ±1/(a−b))
    Assert.Equal(1, r3.Log.Head.Mult)

[<Fact>]
let ``ЛРТ: нулевой результант — ошибка предусловий`` () =
    let ctx = ctxOf2 [ "x" ] [ "t"; "x" ]
    let x, t = idx ctx "x", idx ctx "t"
    Assert.ThrowsAny<exn>(fun () -> lrt x t (polyIn ctx "x+1") (polyIn ctx "(x+1)^2*(x+2)") |> ignore) |> ignore

// ---------- LogToAtan (Rioboo): i·log((A+iB)/(A−iB)) = 2·Σ atan(c_j) + const ----------

// значение многочлена в рациональной точке (все переменные, кроме x, — числа в KP)
let private evalAt (x: int) (x0: BigInteger * BigInteger) (k: KP) : BigInteger * BigInteger =
    match subst x (Const (ratNorm x0)) k.N, subst x (Const (ratNorm x0)) k.D with
    | Const a, Const b -> ratDiv a b
    | _ -> failwith "не число"

[<Fact>]
let ``LogToAtan: производная 2Σ atan(c_j) равна производной i·log((A+iB)/(A−iB)) = 2(A'B − AB')/(A²+B²)`` () =
    let ctx = ctxOf2 [ "x" ] [ "x" ]
    let x = idx ctx "x"
    let mk (s: string) = ofPoly (polyIn ctx s)
    for (a, b) in [ "x", "1"; "x^2+1", "x"; "x+1", "x^2+x+1"; "x^3-x", "x^2+2"; "x^2+3*x+1", "2*x+1"
                    "x^3+x+1", "x^2-x+2"; "x^4+1", "x^3+1"; "x^5-3*x", "x^4+x^2+1" ] do
        let ka, kb = mk a, mk b
        let cs = logToAtan x ka kb
        Assert.NotEmpty cs
        for x0 in [ (1I, 3I); (-2I, 7I); (5I, 4I) ] do
            // Σ 2 c'/(1 + c²)
            let lhs =
                cs |> List.fold (fun acc c ->
                    let cv, dc = evalAt x x0 c, evalAt x x0 (kderiv x c)
                    ratAdd acc (ratDiv (ratMul (2I, 1I) dc) (ratAdd (1I, 1I) (ratMul cv cv)))) (0I, 1I)
            let av, bv = evalAt x x0 ka, evalAt x x0 kb
            let da, db = evalAt x x0 (kderiv x ka), evalAt x x0 (kderiv x kb)
            let rhs = ratDiv (ratMul (2I, 1I) (ratSub (ratMul da bv) (ratMul av db))) (ratAdd (ratMul av av) (ratMul bv bv))
            Assert.True(ratCompare lhs rhs = 0, sprintf "A = %s, B = %s, x0 = %A" a b x0)

[<Fact>]
let ``LogToAtan: эталонные примеры — (x, 1) → atan(x); числители из x^6−5x^4+5x^2+4 дают три атана многочленов`` () =
    let ctx = ctxOf2 [ "x" ] [ "x" ]
    let x = idx ctx "x"
    let mk (s: string) = ofPoly (polyIn ctx s)
    Assert.Equal(1, (logToAtan x (mk "x") (mk "1")).Length)
    // атаны — только от многочленов (знаменатель 1): никаких разрывов на вещественной оси
    for c in logToAtan x (mk "x^4-3*x^2+6") (mk "x^3+x") do
        Assert.True(isOne c.D)

// ---------- точная проверка (verifyExact) ----------

[<Fact>]
let ``verifyExact: верный результат проходит, испорченный S — нет`` () =
    let ctx = ctxOf2 [ "x" ] [ "t"; "x" ]
    let x, t = idx ctx "x", idx ctx "t"
    for (n, d) in [ "1", "x^5+1"; "x^2", "x^7+x+1"; "1", "(x^2+1)^2*(x^3-2)"; "x+3", "x^4+5*x^2+4" ] do
        let pn, pd = polyIn ctx n, polyIn ctx d
        let r = integrateRational x t pn pd
        let factors =
            r.Log |> List.collect (fun tm ->
                snd (PolyFactor.factorPoly tm.Q) |> List.map (fun (f, _) -> (f, reduceKP x t f tm.S true, (1I, 1I))))
        Assert.True(verifyExact x t pn pd r factors, sprintf "(%s)/(%s)" n d)
        // портим первый коэффициент S первого множителя
        let (f0, cs0, m0) = factors.Head
        let bad = Array.copy cs0
        bad.[0] <- kadd bad.[0] kone
        Assert.False(verifyExact x t pn pd r ((f0, bad, m0) :: factors.Tail), sprintf "испорченный (%s)/(%s)" n d)

// ---------- нормировка параметра ЛРТ (scaleParam): p(t) → c^d·p(t/c) ----------

[<Fact>]
let ``scaleParam: 1 + 243t^3 + 19683t^6 при c = 3 приводится к 1 + 9t^3 + 27t^6`` () =
    let ctx = ctxOf2 [ "t" ] [ "t" ]
    let t = idx ctx "t"
    let q = polyIn ctx "1 + 243*t^3 + 19683*t^6"
    Assert.Equal(polyIn ctx "729 + 6561*t^3 + 19683*t^6", scaleParam 3I t q)
    Assert.Equal(polyIn ctx "1 + 9*t^3 + 27*t^6", unitNormal (scaleParam 3I t q))
    // общий D для нескольких многочленов: 3^4·(1 + 3(t/3)^2) = 81 + 27t^2
    Assert.Equal(polyIn ctx "81 + 27*t^2", scaleParamWith 3I 4 t (polyIn ctx "1 + 3*t^2"))

[<Fact>]
let ``verifyExact: нормированная пара (f(t/c), c^D·S(t/c)) проходит только со множителем 1/c`` () =
    let ctx = ctxOf2 [ "x" ] [ "t"; "x" ]
    let x, t = idx ctx "x", idx ctx "t"
    let pn, pd = polyIn ctx "1", polyIn ctx "x^7+x+1"
    let r = integrateRational x t pn pd
    let scaled (c: bigint) (mul: Q) =
        r.Log |> List.collect (fun tm ->
            snd (PolyFactor.factorPoly tm.Q)
            |> List.map (fun (f, _) ->
                let cs = reduceScaled x t f tm.S
                let dmax = cs |> Array.mapi (fun k p -> k + max 0 (degIn t p)) |> Array.max
                (unitNormal (scaleParam c t f), cs |> Array.map (scaleParamWith c dmax t) |> Array.map ofPoly, mul)))
    let one = ratDiv (1I, 1I) (1I, 1I)
    Assert.True(verifyExact x t pn pd r (scaled 3I (ratDiv (1I, 1I) (3I, 1I))), "множитель 1/3")
    Assert.False(verifyExact x t pn pd r (scaled 3I one), "множитель 1 вместо 1/3")
    Assert.False(verifyExact x t pn pd r (scaled 3I (ratDiv (1I, 1I) (2I, 1I))), "множитель 1/2")
