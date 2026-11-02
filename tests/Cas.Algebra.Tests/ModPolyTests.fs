// Тесты многочленов по модулю m (Шаг 21f): ModPoly.fs
module ModPolyTests

open System
open System.Numerics
open Xunit
open ModPoly

// Случайный целочисленный MPoly от переменных 0..nv-1 (плотность неполная), коэффициенты до 2^bits
let randMPoly (rnd: Random) (nv: int) (maxDeg: int) (terms: int) (bits: int) : MPoly.MPoly =
    let randCoef () =
        let bytes = Array.zeroCreate<byte> (bits / 8 + 1)
        rnd.NextBytes bytes
        bytes.[bytes.Length - 1] <- bytes.[bytes.Length - 1] &&& 0x7Fuy
        let v = BigInteger bytes
        if rnd.Next 2 = 0 then v else -v
    let mutable r = MPoly.zero
    for _ in 1 .. terms do
        let mutable t = MPoly.ofInt (let c = randCoef () in if c.IsZero then 1I else c)
        for i in 0 .. nv - 1 do
            let d = rnd.Next(0, maxDeg + 1)
            if d > 0 then t <- MPoly.mul t (MPoly.pow (MPoly.var i) d)
        r <- MPoly.add r t
    r

let rec maxAbs (p: MPoly.MPoly) : BigInteger =
    match p with
    | MPoly.Const (n, _) -> BigInteger.Abs n
    | MPoly.Poly (_, cs) -> cs |> Array.map maxAbs |> Array.max

let bigPrime = BigInteger.Parse "2147483647"

let modOf (p: BigInteger) (l: int) : Mod = { M = BigInteger.Pow (p, l); P = p }

[<Fact>]
let ``ModPoly: toMPoly (ofMPoly a) = a при большом модуле`` () =
    let rnd = Random 11
    for bits in [ 8; 40; 120 ] do
        for _ in 1 .. 20 do
            let a = randMPoly rnd 3 3 6 bits
            let m = { M = BigInteger.Pow (2I, bits + 40) + 15I; P = 3I }   // M > 2·max|coef|; простота не нужна
            Assert.True(m.M > 2I * maxAbs a)
            Assert.Equal(a, toMPoly m (ofMPoly m a))

[<Fact>]
let ``ModPoly: вычеты лежат в [0, M), симметричные — в (-M/2, M/2]`` () =
    let m = modOf 7I 3     // M = 343
    let a = ofMPoly m (MPoly.ofInt -1I)
    Assert.Equal(MC 342I, a)
    Assert.Equal(MPoly.ofInt -1I, toMPoly m a)
    // M/2 = 171: 171 остаётся, 172 → -171
    Assert.Equal(MPoly.ofInt 171I, toMPoly m (MC 171I))
    Assert.Equal(MPoly.ofInt -171I, toMPoly m (MC 172I))

[<Fact>]
let ``ModPoly: mk — инварианты (старшие нули, вырожденные массивы)`` () =
    Assert.Equal(zero, mk 3 [| zero; zero |])
    Assert.Equal(MC 5I, mk 3 [| MC 5I; zero; zero |])
    Assert.Equal(MP (3, [| MC 1I; MC 2I |]), mk 3 [| MC 1I; MC 2I; zero |])

[<Fact>]
let ``ModPoly: add, sub, mul, mulConst согласованы с MPoly по модулю`` () =
    let rnd = Random 12
    for l, bits in [ (1, 20); (3, 60); (8, 200) ] do
        let m = modOf bigPrime l
        for _ in 1 .. 15 do
            let a = randMPoly rnd 3 3 6 bits
            let b = randMPoly rnd 3 3 6 bits
            let am, bm = ofMPoly m a, ofMPoly m b
            Assert.Equal(ofMPoly m (MPoly.add a b), add m am bm)
            Assert.Equal(ofMPoly m (MPoly.sub a b), sub m am bm)
            Assert.Equal(ofMPoly m (MPoly.mul a b), mul m am bm)
            let c = BigInteger (rnd.Next(-1000, 1000)) * BigInteger.Pow (3I, 40)
            Assert.Equal(ofMPoly m (MPoly.mulConst (c, 1I) a), mulConst m c am)

[<Fact>]
let ``ModPoly: переменные разных уровней (скаляр · многочлен, многочлен ниже главной)`` () =
    let m = modOf 101I 2
    let a = ofMPoly m (MPoly.add (MPoly.mul (MPoly.var 2) (MPoly.var 0)) (MPoly.ofInt 7I))   // x2*x0 + 7
    let b = ofMPoly m (MPoly.add (MPoly.var 1) (MPoly.ofInt 3I))                              // x1 + 3
    let p = mul m a b
    Assert.Equal(ofMPoly m (MPoly.mul (MPoly.add (MPoly.mul (MPoly.var 2) (MPoly.var 0)) (MPoly.ofInt 7I))
                                      (MPoly.add (MPoly.var 1) (MPoly.ofInt 3I))), p)
    Assert.Equal(zero, mul m a zero)
    Assert.Equal(a, add m a zero)
    Assert.Equal(zero, add m a (neg m a))

[<Fact>]
let ``ModPoly: coeffIn, degIn, degMain, lcMain, subst0 согласованы с MPoly`` () =
    let rnd = Random 13
    let m = modOf bigPrime 4
    for _ in 1 .. 20 do
        let a = randMPoly rnd 3 3 8 50
        let am = ofMPoly m a
        Assert.Equal(MPoly.degMain a, degMain am)
        Assert.Equal(ofMPoly m (MPoly.lcMain a), lcMain am)
        for v in 0 .. 2 do
            Assert.Equal(MPoly.degIn v a, degIn v am)
            for k in 0 .. 3 do
                Assert.Equal(ofMPoly m (MPoly.coeffIn v k a), coeffIn v k am)
            Assert.Equal(ofMPoly m (MPoly.coeffIn v 0 a), subst0 v am)

[<Fact>]
let ``ModPoly: replaceLc и truncDeg`` () =
    let m = modOf 13I 2
    // x = переменная 2, y = переменная 0: g = x^2 + (y+1) x + 3
    let x, y = MPoly.var 2, MPoly.var 0
    let g = MPoly.add (MPoly.add (MPoly.mul x x) (MPoly.mul (MPoly.add y (MPoly.ofInt 1I)) x)) (MPoly.ofInt 3I)
    let gm = ofMPoly m g
    let l = ofMPoly m (MPoly.add y (MPoly.ofInt 2I))
    let g2 = replaceLc 2 l gm
    Assert.Equal(l, lcMain g2)
    Assert.Equal(coeffIn 2 0 gm, coeffIn 2 0 g2)
    Assert.Equal(coeffIn 2 1 gm, coeffIn 2 1 g2)
    // truncDeg: отбрасывает y^k, k > d
    let h = ofMPoly m (MPoly.add (MPoly.mul (MPoly.pow y 3) x) (MPoly.add (MPoly.mul (MPoly.pow y 2) x) x))
    Assert.Equal(ofMPoly m (MPoly.add (MPoly.mul (MPoly.pow y 2) x) x), truncDeg 0 2 h)
    Assert.Equal(ofMPoly m x, truncDeg 0 0 h)
    Assert.Equal(h, truncDeg 0 5 h)

[<Fact>]
let ``ModPoly: invMod`` () =
    let m = BigInteger.Pow (bigPrime, 3)
    for a in [ 1I; 2I; 12345I; m - 1I; BigInteger.Pow (7I, 30) ] do
        Assert.True((invMod a m * a % m).IsOne)
    Assert.Throws<Exception>(fun () -> invMod 6I 9I |> ignore) |> ignore

[<Fact>]
let ``ModPoly: divModUni — a = q·b + r, deg r < deg b`` () =
    let rnd = Random 14
    let m = modOf bigPrime 3
    let x = 2
    for _ in 1 .. 20 do
        // b — многочлен по x степени 2..3 с константным старшим коэффициентом, обратимым mod M; a — с коэффициентами от y, z
        let db = rnd.Next(2, 4)
        let b = ofMPoly m (MPoly.add (MPoly.mul (MPoly.ofInt (BigInteger (rnd.Next(1, 100)))) (MPoly.pow (MPoly.var x) db))
                                     (MPoly.mul (MPoly.ofInt 5I) (MPoly.var x)))
        let a = ofMPoly m (MPoly.add (MPoly.mul (randMPoly rnd 2 2 4 30) (MPoly.pow (MPoly.var x) (db + rnd.Next(0, 4))))
                                     (randMPoly rnd 2 2 4 30))
        let (q, r) = divModUni m x a b
        Assert.Equal(a, add m (mul m q b) r)
        Assert.True(mainVar r <> x || degMain r < db)
    // делитель-константа и «a без x»
    let a = ofMPoly m (MPoly.add (MPoly.var 0) (MPoly.ofInt 9I))
    let b = ofMPoly m (MPoly.add (MPoly.var x) (MPoly.ofInt 1I))
    Assert.Equal((zero, a), divModUni m x a b)
    let (q, r) = divModUni m x a (MC 7I)
    Assert.Equal(zero, r)
    Assert.Equal(a, mul m (MC 7I) q)

// --- диофантовы уравнения (часть 2) ---

let randBelow (rnd: Random) (m: BigInteger) : BigInteger =
    let bytes = Array.zeroCreate<byte> (m.ToByteArray().Length + 4)
    rnd.NextBytes bytes
    bytes.[bytes.Length - 1] <- 0uy
    BigInteger bytes % m

// Случайный многочлен от x степени d (старший коэффициент — ненулевая константа mod p), остальные — случайные константы
let randUni (rnd: Random) (m: Mod) (x: int) (d: int) : MPolyM =
    let lc = 1I + randBelow rnd (m.P - 1I)
    mk x (Array.init (d + 1) (fun i -> if i = d then MC lc else MC (randBelow rnd m.M)))

// Многочлен от x степени d с коэффициентами — многочленами от переменных 0..nv-1 (lc — константа mod p, deg_y <= 2)
let randMulti (rnd: Random) (m: Mod) (x: int) (nv: int) (d: int) (lcDeg: int) : MPolyM =
    // ненулевой свободный член: иначе множители при y = 0 имеют общий корень x = 0
    let coef () = ofMPoly m (MPoly.add (randMPoly rnd nv 2 4 70) (MPoly.ofInt (BigInteger (rnd.Next(1, 1000000)))))
    let lc = if lcDeg = 0 then MC (1I + randBelow rnd (m.P - 1I)) else coef ()
    mk x (Array.init (d + 1) (fun i -> if i = d then lc else coef ()))

let prodExcept (m: Mod) (fs: MPolyM[]) (i: int) =
    fs |> Array.mapi (fun j f -> (j, f)) |> Array.filter (fun (j, _) -> j <> i) |> Array.fold (fun acc (_, f) -> mul m acc f) one

[<Fact>]
let ``diophUni: Σσ_i·b_i = c mod p^l для r = 2, 3, 4, неунитарные множители`` () =
    let rnd = Random 21
    let x = 0
    for r in [ 2; 3; 4 ] do
        for l in [ 1; 3; 6 ] do
            let m = modOf bigPrime l
            let fs = Array.init r (fun _ -> randUni rnd m x (rnd.Next(1, 5)))
            let sigmaStar = fs |> Array.map (fun f -> randUni rnd m x (degMain f - 1 |> max 0))
            // σ* — любые многочлены степени < deg f_i (включая константы)
            let c = Array.fold2 (fun acc s i -> add m acc (mul m s (prodExcept m fs i))) zero sigmaStar [| 0 .. r - 1 |]
            let sol = diophUni m x c fs
            Assert.Equal<MPolyM[]>(sigmaStar, sol)
            // degree: σ_i короче f_i
            for i in 0 .. r - 1 do Assert.True(degMain sol.[i] < degMain fs.[i])

[<Fact>]
let ``diophUni: не взаимно простые множители и слишком высокая степень c — отказ`` () =
    let m = modOf bigPrime 2
    let x = 0
    let lin (a: BigInteger) = mk x [| MC a; one |]
    let f1 = mul m (lin 1I) (lin 2I)
    let f2 = mul m (lin 1I) (lin 3I)
    let fails (f: unit -> unit) = try f (); false with LiftFail -> true
    Assert.True(fails (fun () -> diophUni m x (lin 5I) [| f1; f2 |] |> ignore))
    // c степени >= Σ deg f_i не раскладывается
    let g1, g2 = lin 1I, lin 2I
    Assert.True(fails (fun () -> diophUni m x (mk x [| zero; zero; one |]) [| g1; g2 |] |> ignore))
    // c нулевой — нулевое решение
    Assert.Equal<MPolyM[]>([| zero; zero |], diophUni m x zero [| g1; g2 |])

[<Fact>]
let ``diophMulti: рекурсия по переменным, уровни 1..3, r = 2 и 3`` () =
    let rnd = Random 22
    let x = 3
    let ys = [| 0; 1; 2 |]
    for r in [ 2; 3 ] do
        for l in [ 2; 4 ] do
            let m = modOf bigPrime l
            for level in 1 .. 3 do
                // старшие коэффициенты множителей — константы (обратимы mod p)
                let fs = Array.init r (fun _ -> randMulti rnd m x level (rnd.Next(1, 4)) 0)
                // σ*_i: степень по x меньше deg f_i, коэффициенты — произвольные многочлены от y
                let sigmaStar =
                    fs |> Array.map (fun f ->
                        mk x (Array.init (degMain f) (fun _ -> ofMPoly m (randMPoly rnd level 2 4 70))))
                let c = Array.fold2 (fun acc s i -> add m acc (mul m s (prodExcept m fs i))) zero sigmaStar [| 0 .. r - 1 |]
                match diophMulti m x ys (fun _ -> 6) level c fs with
                | Some sol ->
                    // уникальность: решение совпадает с σ* (степень по x < deg f_i)
                    Assert.Equal<MPolyM[]>(sigmaStar, sol)
                | None -> failwithf "диофантово уравнение не решено: r=%d l=%d level=%d" r l level

[<Fact>]
let ``diophMulti: нет решения с недостаточной границей степеней`` () =
    let m = modOf bigPrime 2
    let x = 1
    let ys = [| 0 |]
    // f1 = x + 1, f2 = x + 2 (по y не зависят); c = y^3: σ_1 = -y^3, σ_2 = y^3 нужна степень 3
    let f1 = mk x [| one; one |]
    let f2 = mk x [| MC 2I; one |]
    let c = mk 0 [| zero; zero; zero; one |]
    Assert.Equal(None, diophMulti m x ys (fun _ -> 2) 1 c [| f1; f2 |])
    match diophMulti m x ys (fun _ -> 3) 1 c [| f1; f2 |] with
    | Some [| s1; s2 |] ->
        Assert.Equal(add m (mul m s1 f2) (mul m s2 f1), c)
    | _ -> failwith "ожидалось решение"

// --- многомерный Хензель (часть 3) ---

// Подъём всех множителей: a = Π f_i, известны lc_i и образы при y = 0 — подъём восстанавливает f_i
let henselRoundTrip (rnd: Random) (r: int) (nv: int) (l: int) =
    let m = modOf bigPrime l
    let x = nv
    let ys = [| 0 .. nv - 1 |]
    let fs =
        Array.init r (fun _ ->
            let d = rnd.Next(1, 4)
            // старший коэффициент — многочлен от y с ненулевым свободным членом (обратим mod p)
            let lc = ofMPoly m (MPoly.add (randMPoly rnd nv 2 3 40) (MPoly.ofInt (BigInteger (rnd.Next(2, 1000)))))
            let coef () = ofMPoly m (MPoly.add (randMPoly rnd nv 2 4 40) (MPoly.ofInt (BigInteger (rnd.Next(1, 1000000)))))
            mk x (Array.init (d + 1) (fun i -> if i = d then lc else coef ())))
    let a = Array.fold (mul m) one fs
    let lcs = fs |> Array.map lcMain
    let zeroAll (p: MPolyM) = ys |> Array.fold (fun q y -> subst0 y q) p
    let fs0 = fs |> Array.map zeroAll
    match henselMulti m x ys a lcs fs0 with
    | Some sol -> Assert.Equal<MPolyM[]>(fs, sol)
    | None -> failwithf "подъём не удался: r=%d nv=%d l=%d" r nv l

[<Fact>]
let ``henselMulti: восстановление r = 2, 3, 4 множителей с нетривиальными lc, 1..3 переменных`` () =
    let rnd = Random 31
    for r in [ 2; 3; 4 ] do
        for nv in [ 1; 2; 3 ] do
            henselRoundTrip rnd r nv 3

[<Fact>]
let ``henselMulti: неверные старшие коэффициенты — отказ`` () =
    let m = modOf bigPrime 3
    // a = (x + y)(x - y) = x^2 - y^2; lc-коэффициенты заданы неверно (2 и 1/2 не дают lc a)
    let x, y = 1, 0
    let fa = mk x [| MC 1I; one |]
    let fb = mk x [| MC 2I; one |]
    let a = mul m (mk x [| MP (y, [| MC 1I; one |]); one |]) (mk x [| MP (y, [| MC 2I; one |]); one |])
    // верные lc: 1, 1
    Assert.True((henselMulti m x [| y |] a [| one; one |] [| fa; fb |]).IsSome)
    // неверные lc: Π lcs ≠ lc a — подъём обязан отказать
    Assert.Equal(None, henselMulti m x [| y |] a [| MC 2I; one |] [| mulConst m 2I fa; fb |])
