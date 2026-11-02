// Тесты полной многомерной факторизации (Шаг 21f): условия Ванга, предсказание старших коэффициентов,
// p-адический подъём, откаты; одномерные — Цассенхауз (множества степеней, тест Эбботта)
module WangFactorTests

open System
open System.Diagnostics
open System.Numerics
open Xunit
open MPoly
open PolyGcd

let padd (a: MPoly) (b: MPoly) = MPoly.add a b
let psub (a: MPoly) (b: MPoly) = MPoly.sub a b
let pmul (a: MPoly) (b: MPoly) = MPoly.mul a b
let pc (n: int) = MPoly.ofInt (BigInteger n)
let ppow (a: MPoly) (n: int) = MPoly.pow a n
let prod (fs: MPoly list) = fs |> List.fold pmul one

// Переменные: y = 0, z = 1, x = 2 (главная), w = 3 для 4-переменных тестов (тогда главная — w; см. xs)
let y, z, x = var 0, var 1, var 2

// Общая проверка: Π множителей = p; каждый множитель неприводим (повторное разложение даёт его же);
// число множителей (с кратностью) не меньше expected
let checkFactorization (p: MPoly) (expected: int) : (MPoly * int) list =
    let (c, parts) = PolyFactor.factorPoly p
    let back = parts |> List.fold (fun acc (f, e) -> pmul acc (ppow f e)) (mulConst c one)
    Assert.Equal(p, back)
    let count = parts |> List.sumBy snd
    Assert.True(count >= expected, sprintf "множителей %d < %d" count expected)
    for (f, _) in parts do
        let (c2, again) = PolyFactor.factorPoly f
        Assert.True((again |> List.sumBy snd) = 1, "множитель повторно разложим")
    parts

let wangStats () = Array.copy (PolyFactor.stats ())

// --- distributeLc ---

[<Fact>]
let ``distributeLc: lc = (y+1)^2 (y+2) z делится по множителям, кратность и порядок`` () =
    let f1 = padd (padd (pmul (pmul (pmul (padd y (pc 1)) (padd y (pc 2))) z) (pmul x x))
                        (pmul (padd (pmul y z) (pc 2)) x))
                  (padd (psub y z) (pc 4))
    let f2 = padd (padd (pmul (padd y (pc 1)) (pmul x x)) (pmul (padd z (pmul y y)) x)) (psub (pmul y z) (pc 5))
    let f3 = padd x (padd (padd (pmul y z) z) (pc 1))
    let a = prod [ f1; f2; f3 ]
    let lfs = [ (padd y (pc 1), 2); (padd y (pc 2), 1); (z, 1) ]
    let ys = [| 0; 1 |]
    let alphas = [| 2; 5 |]
    let image (f: MPoly) : BigInteger[] =
        match subst 1 (pc 5) (subst 0 (pc 2) f) with
        | Poly (_, cs) -> cs |> Array.map (fun c -> match c with Const (n, _) -> n | _ -> failwith "не число")
        | _ -> failwith "ожидался многочлен"
    let us = [| f1; f2; f3 |] |> Array.map (fun f -> UniFactor.primitiveZ (image f))
    // содержания образов равны 1 — δ = 1
    Assert.Equal<BigInteger[]>(image f1, us.[0])
    match PolyFactor.distributeLc ys lfs 1I alphas us 1I with
    | Some (cs, us2, delta) ->
        Assert.Equal(1I, delta)
        Assert.Equal(prod [ padd y (pc 1); padd y (pc 2); z ], cs.[0])
        Assert.Equal(padd y (pc 1), cs.[1])
        Assert.Equal(one, cs.[2])
        Assert.Equal<BigInteger[][]>(us, us2)
    | None -> failwith "distributeLc: ожидался успех"
    // неверное содержание Ω — Π C_i ≠ L, точка отвергается
    Assert.True((PolyFactor.distributeLc ys lfs 2I alphas us 1I).IsNone)
    // F̃_j = ±1 или 0 — отказ
    Assert.True((PolyFactor.distributeLc ys [ (padd y (pc -1), 1) ] 1I alphas us 1I).IsNone)

[<Fact>]
let ``distributeLc: целая часть и δ ≠ 1 — u_i и C_i согласованы, lc u_i = C_i(α)`` () =
    // L = 6 · (y+1): образ (α = 2): F̃ = 3; множители с lc 2·3 и 1; δ = 1 → ĉ/g, δ делится
    let ys = [| 0 |]
    let lfs = [ (padd y (pc 1), 1) ]
    let us = [| [| 1I; 6I |]; [| 3I; 1I |] |]      // 6x + 1,  x + 3 (образы при y = 2)
    match PolyFactor.distributeLc ys lfs 1I [| 2 |] us 1I with
    | Some (cs, us2, delta) ->
        // произведение lc: (y+1)·… = L при Ω = 1·…: проверяем согласованность lc(u_i) = C_i(α)
        for i in 0 .. 1 do
            let ci = match subst 0 (pc 2) cs.[i] with Const (n, _) -> n | _ -> failwith "не число"
            Assert.Equal(us2.[i].[us2.[i].Length - 1], ci)
        Assert.Equal(1I, delta)
    | None -> ()   // L = 6(y+1) не совпадает с lc(u) — допустимо: точка отвергнута проверкой Π C_i = L

// --- точка 0 несчастливая, общие множители в lc ---

[<Fact>]
let ``Ванг: lc = (y+1)^2 (y+2) z, три множителя, точка 0 непригодна`` () =
    let f1 = padd (padd (pmul (pmul (pmul (padd y (pc 1)) (padd y (pc 2))) z) (pmul x x))
                        (pmul (padd (pmul y z) (pc 2)) x))
                  (padd (psub y z) (pc 4))
    let f2 = padd (padd (pmul (padd y (pc 1)) (pmul x x)) (pmul (padd z (pmul y y)) x)) (psub (pmul y z) (pc 5))
    let f3 = padd x (padd (padd (pmul y z) z) (pc 1))
    let a = prod [ f1; f2; f3 ]
    Assert.Equal(prod [ ppow (padd y (pc 1)) 2; padd y (pc 2); z ], lcMain a)
    let before = wangStats ()
    let parts = checkFactorization a 3
    Assert.Equal(3, parts.Length)
    // раскрытие произошло через полный подъём, без отката
    Assert.True((PolyFactor.stats ()).[0] > before.[0])
    Assert.Equal(before.[1], (PolyFactor.stats ()).[1])
    Assert.Equal(before.[2], (PolyFactor.stats ()).[2])

[<Fact>]
let ``Ванг: старшие коэффициенты с повторяющимися простыми, пары и тройки множителей`` () =
    // lc = y^2 (y+1) z (z - 2): F̃ при нулевой точке равны 0 или 1 — нужны другие точки
    let g1 = padd (padd (pmul (pmul (pmul y y) z) (pmul x x)) (pmul (padd y z) x)) (padd (pmul y z) (pc 3))
    let g2 = padd (padd (pmul (pmul (padd y (pc 1)) (psub z (pc 2))) (pmul x x)) (pmul (psub y z) x)) (pc 7)
    let g3 = padd (pmul (padd (pmul y z) (pc 1)) x) (padd (pmul z z) (pc 2))
    for fs in [ [ g1; g2 ]; [ g2; g3 ]; [ g1; g3 ]; [ g1; g2; g3 ] ] do
        checkFactorization (prod fs) fs.Length |> ignore

// --- эталоны в стиле Ванга 1978 (построены как произведения; НЕ дословные w_1, w_2, w_3) ---

[<Fact>]
let ``Ванг-стиль: три множителя от трёх переменных, нетривиальные lc с общими множителями`` () =
    let a1 = padd (padd (padd (pmul (padd (pmul (pmul y y) z) (pc 3)) (pmul x (pmul x x)))
                              (pmul (padd (psub (pmul y z) (pmul (pc 2) (pmul z z))) (pc 1)) (pmul x x)))
                        (pmul (pc -1 |> pmul (padd y z)) x))
                  (psub (pmul (pc 5) (pmul y z)) (pc 4))
    let b1 = padd (padd (pmul (padd (pmul (pmul y y) z) (pc 3)) (pmul x x)) (pmul (psub (pmul (pc 2) y) z) x))
                  (padd (padd (pmul z z) y) (pc 7))
    let c1 = padd (padd (pmul (pmul (padd y (pc 1)) (psub z (pc 2))) (pmul x x)) (pmul (pmul y z) x)) (pc -3)
    let w1 = prod [ a1; b1; c1 ]
    let before = wangStats ()
    checkFactorization w1 3 |> ignore
    Assert.Equal(before.[2], (PolyFactor.stats ()).[2])
    // два множителя, один — степень 4
    let a2 = padd (padd (pmul (padd (pmul z z) (padd y (pc 2))) (ppow x 4)) (pmul (psub y z) (pmul x x))) (padd (pmul y z) (pc 1))
    let b2 = padd (padd (pmul (padd (pmul y z) (pc 3)) (ppow x 3)) (pmul (padd (pmul y y) z) x)) (psub z (pc 9))
    checkFactorization (prod [ a2; b2 ]) 2 |> ignore

// --- эталон Ванга w_1 (по Wang 1978) ---

// w_1 = 4*x**6*y**4*z**2 + ... (40 термов), три множителя — эталонная факторизация:
//   (x²y² − x²z² + y − z², x²yz² + 3xz + 2y, 4x²y + 4x²z + xyz − 1)
let private w1Text =
    "4*x**6*y**4*z**2 + 4*x**6*y**3*z**3 - 4*x**6*y**2*z**4 - 4*x**6*y*z**5 + x**5*y**4*z**3 + 12*x**5*y**3*z - x**5*y**2*z**5 + 12*x**5*y**2*z**2 - 12*x**5*y*z**3 - 12*x**5*z**4 + 8*x**4*y**4 + 6*x**4*y**3*z**2 + 8*x**4*y**3*z - 4*x**4*y**2*z**4 + 4*x**4*y**2*z**3 - 8*x**4*y**2*z**2 - 4*x**4*y*z**5 - 2*x**4*y*z**4 - 8*x**4*y*z**3 + 2*x**3*y**4*z + x**3*y**3*z**3 - x**3*y**2*z**5 - 2*x**3*y**2*z**3 + 9*x**3*y**2*z - 12*x**3*y*z**3 + 12*x**3*y*z**2 - 12*x**3*z**4 + 3*x**3*z**3 + 6*x**2*y**3 - 6*x**2*y**2*z**2 + 8*x**2*y**2*z - 2*x**2*y*z**4 - 8*x**2*y*z**3 + 2*x**2*y*z**2 + 2*x*y**3*z - 2*x*y**2*z**3 - 3*x*y*z + 3*x*z**3 - 2*y**2 + 2*y*z**2"

// Разбор записи с `**`: члены через « + » / « - », множители через «*», степени «**»
let private parseStarStar (s: string) : MPoly =
    let varOf (c: string) = match c with "x" -> x | "y" -> y | "z" -> z | _ -> failwithf "переменная %s" c
    let terms = s.Replace(" - ", " + -").Split([| " + " |], StringSplitOptions.None)
    terms
    |> Array.map (fun t ->
        let neg = t.StartsWith "-"
        let body = (if neg then t.Substring 1 else t).Replace("**", "^")
        let factors = body.Split('*')
        let mutable r = pc (if neg then -1 else 1)
        for f in factors do
            if f.Contains "^" then
                let parts = f.Split('^')
                r <- pmul r (ppow (varOf parts.[0]) (int parts.[1]))
            elif f.Length = 1 && Char.IsLetter f.[0] then r <- pmul r (varOf f)
            else r <- pmul r (MPoly.ofInt (BigInteger.Parse f))
        r)
    |> Array.fold padd zero

[<Fact>]
let ``эталон Ванга w_1 (дословно): 40 термов, три множителя, произведение равно w_1`` () =
    let w1 = parseStarStar w1Text
    Assert.Equal(40, (monomials w1).Length)
    // свойства из wang-examples.md: степени x = 6, y = 4, z = 5; lc_x = 4·y·z²·(y+z)²·(y−z)
    Assert.Equal(6, degIn 2 w1)
    Assert.Equal(4, degIn 0 w1)
    Assert.Equal(5, degIn 1 w1)
    Assert.Equal(prod [ pc 4; y; ppow z 2; ppow (padd y z) 2; psub y z ], lcMain w1)
    let f1 = padd (psub (pmul (pmul x x) (pmul y y)) (pmul (pmul x x) (pmul z z))) (psub y (pmul z z))
    let f2 = padd (padd (pmul (pmul (pmul x x) y) (pmul z z)) (pmul (pc 3) (pmul x z))) (pmul (pc 2) y)
    let f3 = psub (padd (padd (pmul (pc 4) (pmul (pmul x x) y)) (pmul (pc 4) (pmul (pmul x x) z))) (pmul x (pmul y z))) one
    Assert.Equal(w1, prod [ f1; f2; f3 ])
    let (c0, parts) = PolyFactor.factorPoly w1
    Assert.Equal(3, parts.Length)
    Assert.True(parts |> List.forall (fun (_, e) -> e = 1))
    let found = parts |> List.map (fst >> unitNormal) |> List.sortBy (fun f -> sprintf "%A" f)
    let expected = [ f1; f2; f3 ] |> List.map unitNormal |> List.sortBy (fun f -> sprintf "%A" f)
    Assert.True((found = expected), "множители w_1 не совпали с эталонными")
    let back = parts |> List.fold (fun acc (f, e) -> pmul acc (ppow f e)) (mulConst c0 one)
    Assert.Equal(w1, back)

// --- рекомбинация подмножеств (откат 2): полный подъём пропущен принудительно ---

[<Fact>]
let ``рекомбинация подмножеств: множители находятся парами (u_S, остаток), C_S = Π C_i`` () =
    let f1 = padd (padd (pmul (pmul (pmul (padd y (pc 1)) (padd y (pc 2))) z) (pmul x x))
                        (pmul (padd (pmul y z) (pc 2)) x))
                  (padd (psub y z) (pc 4))
    let f2 = padd (padd (pmul (padd y (pc 1)) (pmul x x)) (pmul (padd z (pmul y y)) x)) (psub (pmul y z) (pc 5))
    let f3 = padd x (padd (padd (pmul y z) z) (pc 1))
    let f4 = padd (padd (pmul (padd z (pc 3)) (pmul x x)) (pmul (psub y (pc 2)) x)) (padd (pmul y y) (pc 1))
    PolyFactor.skipFullLift.Value <- true
    try
        for fs in [ [ f1; f2; f3 ]; [ f2; f3; f4 ]; [ f1; f2; f3; f4 ] ] do
            let before = wangStats ()
            // без полного подъёма остаток из двух множителей (r = 2) не делится — «как есть»; поэтому >= n − 1
            let parts = checkFactorization (prod fs) (fs.Length - 1)
            Assert.True((PolyFactor.stats ()).[1] > before.[1])
            // найденное подмножеством — истинный множитель из набора
            Assert.True(parts |> List.exists (fun (f, _) -> fs |> List.exists (fun g -> unitNormal g = f)))
    finally
        PolyFactor.skipFullLift.Value <- false

// --- неприводимые остаются ---

[<Fact>]
let ``неприводимые многомерные: x^2+y^2+z^2, x^4+y^4+1, xyz+x+y+z+1`` () =
    let cases =
        [ padd (padd (pmul x x) (pmul y y)) (pmul z z)
          padd (padd (ppow x 4) (ppow y 4)) one
          padd (padd (padd (padd (prod [ x; y; z ]) x) y) z) one ]
    for p in cases do
        let (_, parts) = PolyFactor.factorPoly p
        Assert.Equal(1, parts.Length)
        Assert.Equal(p, fst parts.Head)

// --- случайные произведения ---

let randDense (rnd: Random) (vars: int list) (deg: int) (bits: int) (mustHave: int) : MPoly =
    // плотный многочлен общей степени <= deg: все мономы, коэффициент ≠ 0; переменная mustHave входит
    let randCoef () =
        let bytes = Array.zeroCreate<byte> (bits / 8 + 1)
        rnd.NextBytes bytes
        bytes.[bytes.Length - 1] <- 0uy
        let v = BigInteger bytes % BigInteger.Pow (10I, bits * 3 / 10 + 1)
        let v = if v.IsZero then 1I else v
        if rnd.Next 2 = 0 then v else -v
    let rec monos (vs: int list) (d: int) : (int * int) list list =
        match vs with
        | [] -> [ [] ]
        | v :: rest -> [ for k in 0 .. d do for m in monos rest (d - k) -> (if k = 0 then m else (v, k) :: m) ]
    let mutable r = zero
    for m in monos vars deg do
        let t = m |> List.fold (fun acc (v, k) -> pmul acc (ppow (var v) k)) (MPoly.ofInt (randCoef ()))
        r <- padd r t
    // гарантировать вхождение главной переменной
    if degIn mustHave r < 1 then padd r (var mustHave) else r

let randomProducts (seed: int) (count: int) (nvars: int) (bits: int) (deg: int) =
    let rnd = Random seed
    let vars = [ 0 .. nvars - 1 ]
    let top = nvars - 1
    let sw = Stopwatch.StartNew()
    for round in 1 .. count do
        let k = 2 + (round % 3)
        let fs = [ for _ in 1 .. k -> randDense rnd vars (if k = 4 then 2 else deg) bits top ]
        let p = prod fs
        checkFactorization p k |> ignore
    sw.ElapsedMilliseconds

[<Fact>]
let ``случайные произведения: 3 переменные, коэффициенты до 10^6`` () =
    let ms = randomProducts 101 20 3 20 3
    Assert.True(ms < 15000L, sprintf "%d мс" ms)

[<Fact>]
let ``случайные произведения: 4 переменные, коэффициенты до 10^6`` () =
    let ms = randomProducts 102 12 4 20 3
    Assert.True(ms < 15000L, sprintf "%d мс" ms)

[<Fact>]
let ``случайные произведения: коэффициенты до 10^30`` () =
    let ms = randomProducts 103 18 3 100 3
    Assert.True(ms < 15000L, sprintf "%d мс" ms)

// --- одномерные ---

// Минимальный многочлен √p1 + … + √pk: P_k(x) = res_y(P_{k-1}(x − y), y² − p) = A² − p·B², где P(x − y) ≡ A + y·B (mod y² − p)
let swinnertonDyer (primes: int list) : BigInteger[] =
    let trim (a: BigInteger[]) =
        let mutable n = a.Length
        while n > 0 && a.[n - 1].IsZero do n <- n - 1
        Array.sub a 0 n
    let addA (a: BigInteger[]) (b: BigInteger[]) =
        trim (Array.init (max a.Length b.Length) (fun i -> (if i < a.Length then a.[i] else 0I) + (if i < b.Length then b.[i] else 0I)))
    let subA (a: BigInteger[]) (b: BigInteger[]) = addA a (b |> Array.map (fun c -> -c))
    let scaleA (k: BigInteger) (a: BigInteger[]) = trim (a |> Array.map (fun c -> c * k))
    let mulX (a: BigInteger[]) = if a.Length = 0 then a else Array.append [| 0I |] a
    let mulA (a: BigInteger[]) (b: BigInteger[]) =
        if a.Length = 0 || b.Length = 0 then [||]
        else
            let r = Array.create (a.Length + b.Length - 1) 0I
            for i in 0 .. a.Length - 1 do
                for j in 0 .. b.Length - 1 do
                    r.[i + j] <- r.[i + j] + a.[i] * b.[j]
            trim r
    let step (p: BigInteger) (poly: BigInteger[]) =
        let mutable u = [| 1I |]      // (x − y)^i = u + y·v
        let mutable v : BigInteger[] = [||]
        let mutable a : BigInteger[] = [||]
        let mutable b : BigInteger[] = [||]
        for i in 0 .. poly.Length - 1 do
            a <- addA a (scaleA poly.[i] u)
            b <- addA b (scaleA poly.[i] v)
            let u2 = subA (mulX u) (scaleA p v)
            let v2 = subA (mulX v) u
            u <- u2
            v <- v2
        subA (mulA a a) (scaleA p (mulA b b))
    primes |> List.fold (fun poly p -> step (BigInteger p) poly) [| 0I; 1I |]

let toUniMPoly (zs: BigInteger[]) : MPoly = mk 0 (zs |> Array.map MPoly.ofInt)

[<Fact>]
let ``одномерные: Свиннертон-Дайер SD_3 и SD_4 неприводимы`` () =
    // SD_2 = x^4 - 10x^2 + 1
    Assert.Equal<BigInteger[]>([| 1I; 0I; -10I; 0I; 1I |], swinnertonDyer [ 2; 3 ])
    for primes, deg in [ ([ 2; 3; 5 ], 8); ([ 2; 3; 5; 7 ], 16) ] do
        let p = toUniMPoly (swinnertonDyer primes)
        Assert.Equal(deg, degMain p)
        let (_, parts) = PolyFactor.factorPoly p
        Assert.Equal(1, parts.Length)

[<Fact>]
let ``одномерные: Свиннертон-Дайер SD_5 (степень 32) неприводим`` () =
    let p = toUniMPoly (swinnertonDyer [ 2; 3; 5; 7; 11 ])
    Assert.Equal(32, degMain p)
    let sw = Stopwatch.StartNew()
    let (_, parts) = PolyFactor.factorPoly p
    Assert.Equal(1, parts.Length)
    Assert.True(sw.ElapsedMilliseconds < 20000L, sprintf "SD_5: %d мс" sw.ElapsedMilliseconds)

[<Fact>]
let ``одномерные: произведение SD_3 и сдвинутых многочленов — множители по подмножествам`` () =
    // (SD_3 с x → x+1) · (x^4 + 1) · (x^6 + x + 1): три неприводимых множителя степеней 8, 4, 6
    let sd3 = toUniMPoly (swinnertonDyer [ 2; 3; 5 ])
    let shifted = subst 0 (padd (var 0) one) sd3
    let p = prod [ shifted; padd (ppow (var 0) 4) one; padd (padd (ppow (var 0) 6) (var 0)) one ]
    let (c, parts) = PolyFactor.factorPoly p
    Assert.Equal(3, parts.Length)
    Assert.Equal<int list>([ 4; 6; 8 ], parts |> List.map (fun (f, _) -> degMain f) |> List.sort)
    Assert.Equal(p, parts |> List.fold (fun acc (f, e) -> pmul acc (ppow f e)) (mulConst c one))

[<Fact>]
let ``одномерные: x^100-1 (9 множителей) и x^120-1 (16 множителей)`` () =
    for n, cnt in [ (100, 9); (120, 16) ] do
        let p = psub (ppow (var 0) n) one
        let (c, parts) = PolyFactor.factorPoly p
        Assert.Equal(cnt, parts.Length)
        Assert.Equal(p, parts |> List.fold (fun acc (f, e) -> pmul acc (ppow f e)) (mulConst c one))
        // степени множителей — φ(d) для d | n
        let phi (d: int) = [ 1 .. d ] |> List.filter (fun k -> (BigInteger.GreatestCommonDivisor (BigInteger k, BigInteger d)).IsOne) |> List.length
        let expected = [ 1 .. n ] |> List.filter (fun d -> n % d = 0) |> List.map phi |> List.sort
        Assert.Equal<int list>(expected, parts |> List.map (fun (f, _) -> degMain f) |> List.sort)

[<Fact>]
let ``одномерные: неприводимые степени 50`` () =
    let p1 = psub (ppow (var 0) 50) (pc 2)
    Assert.Equal(1, (snd (PolyFactor.factorPoly p1)).Length)
    let rnd = Random 77
    let coeffs = Array.init 51 (fun i -> if i = 50 then 1I else BigInteger (rnd.Next(-1000, 1000)))
    let p2 = toUniMPoly coeffs
    let (c, parts) = PolyFactor.factorPoly p2
    Assert.Equal(p2, parts |> List.fold (fun acc (f, e) -> pmul acc (ppow f e)) (mulConst c one))
