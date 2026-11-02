// Тесты модулярного НОД многочленов (Шаг 21e): сверка с субрезультантным PRS
module ModGcdTests

open System
open System.Numerics
open Xunit
open MPoly
open PolyGcd
open ModGcd
open Zippel

let private v (i: int) = var i
let private c (n: int) = ofInt (BigInteger n)

// Случайный многочлен от переменных 0..nv-1: заданное число термов, степени до maxDeg, коэффициенты до maxCoef
let private randPoly (rnd: Random) (nv: int) (terms: int) (maxDeg: int) (maxCoef: int) : MPoly =
    let mutable r = zero
    for _ in 1 .. terms do
        let mutable t = c (rnd.Next(1, maxCoef + 1) * (if rnd.Next 2 = 0 then 1 else -1))
        for i in 0 .. nv - 1 do
            let d = rnd.Next(0, maxDeg + 1)
            if d > 0 then t <- mul t (pow (v i) d)
        r <- add r t
    r

let private sameAsPrs (a: MPoly) (b: MPoly) =
    let m = gcd a b
    let p = gcdPrs a b
    Assert.Equal(p, m)
    // модулярный путь сам (без отката на PRS) на примитивных по главной переменной частях
    if mainVar a = mainVar b && mainVar a >= 0 then
        let pa, pb = divExactExn a (contentMain a), divExactExn b (contentMain b)
        match tryModularPrimitiveGcd pa pb with
        | Some h ->
            let h = if isConst h then h else unitNormal h
            Assert.Equal(unitNormal (gcdPrs pa pb), h)
        | None -> failwith "модулярный НОД отказал"
    m

[<Fact>]
let ``модулярный НОД: одномерные случайные, как PRS`` () =
    let rnd = Random 11
    for _ in 1 .. 60 do
        let g = randPoly rnd 1 4 4 20
        let a = mul g (randPoly rnd 1 4 5 20)
        let b = mul g (randPoly rnd 1 4 5 20)
        if not (isZero a) && not (isZero b) then
            let r = sameAsPrs a b
            Assert.True((divExact a r).IsSome && (divExact b r).IsSome)

[<Fact>]
let ``модулярный НОД: одномерные высокой степени (публичный gcd идёт модулярным путём)`` () =
    let rnd = Random 44
    for _ in 1 .. 6 do
        let g = randPoly rnd 1 5 7 50 |> fun p -> add p (pow (v 0) 7)
        let a = mul g (add (pow (v 0) 8) (randPoly rnd 1 4 7 30))
        let b = mul g (add (pow (v 0) 7) (randPoly rnd 1 4 6 30))
        let r = sameAsPrs a b
        Assert.True((divExact r (unitNormal g)).IsSome)

[<Fact>]
let ``модулярный НОД: двумерные случайные, как PRS`` () =
    let rnd = Random 22
    for _ in 1 .. 40 do
        let g = randPoly rnd 2 4 3 9
        let a = mul g (randPoly rnd 2 4 3 9)
        let b = mul g (randPoly rnd 2 4 3 9)
        if not (isZero a) && not (isZero b) then
            let r = sameAsPrs a b
            Assert.True((divExact a r).IsSome && (divExact b r).IsSome)
            if not (isZero g) then Assert.True((divExact r (unitNormal g)).IsSome)

[<Fact>]
let ``модулярный НОД: трёхмерные случайные, как PRS`` () =
    let rnd = Random 33
    for _ in 1 .. 12 do
        let g = randPoly rnd 3 3 2 5
        let a = mul g (randPoly rnd 3 3 2 5)
        let b = mul g (randPoly rnd 3 3 2 5)
        if not (isZero a) && not (isZero b) then
            let r = sameAsPrs a b
            Assert.True((divExact a r).IsSome && (divExact b r).IsSome)

[<Fact>]
let ``модулярный НОД: большие коэффициенты`` () =
    let big = BigInteger.Pow(10I, 25) + 7I
    let g = add (mul (ofInt big) (pow (v 0) 3)) (add (mul (ofInt (big * 3I + 1I)) (mul (v 0) (v 1))) (ofInt 12345678901234567890I))
    let a = mul g (add (pow (v 0) 2) (add (v 1) (c 3)))
    let b = mul g (add (mul (v 0) (v 1)) (add (pow (v 1) 2) (c -5)))
    let r = sameAsPrs a b
    Assert.Equal(unitNormal g, r)

[<Fact>]
let ``модулярный НОД: взаимно простые, делимость, содержание`` () =
    let x, y = v 1, v 0
    let a = add (pow x 3) (add (mul x y) (c 7))
    let b = add (pow x 2) (add (pow y 2) (c 1))
    Assert.Equal(one, sameAsPrs a b)
    // один делит другой
    let d = mul a (add x (c 2))
    Assert.Equal(unitNormal a, sameAsPrs d a)
    Assert.Equal(unitNormal a, sameAsPrs a d)
    // содержание (число и многочлен от младшей переменной)
    let cont = mul (c 6) (add y (c 1))
    let r = sameAsPrs (mul cont (mul a (add x y))) (mul cont (mul a (add x (c 5))))
    Assert.Equal(unitNormal (mul (add y (c 1)) a), r)
    // рациональные коэффициенты
    let ra = mulConst (1I, 3I) (mul a (add x y))
    let rb = mulConst (2I, 5I) (mul a (add x (c 5)))
    Assert.Equal(unitNormal a, sameAsPrs ra rb)

[<Fact>]
let ``модулярный НОД: старшие коэффициенты по x зависят от y`` () =
    let x, y = v 1, v 0
    let g = add (mul (add y (c 2)) (pow x 2)) (add (mul (c 3) x) y)
    let a = mul g (add (mul (pow y 2) (pow x 2)) (c 1))
    let b = mul g (add (mul (add y (c -1)) x) (c 4))
    Assert.Equal(unitNormal g, sameAsPrs a b)
