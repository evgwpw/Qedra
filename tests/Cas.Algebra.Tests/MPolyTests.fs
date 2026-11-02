// Тесты многочленов от нескольких переменных (Шаг 17, коммит 1): точное деление, псевдоделение, НОД.
// Шаг 21h': чистая алгебра — многочлены строятся из инфиксной записи (PolyText), результаты сравниваются как MPoly.
// Тесты преобразований выражение ↔ многочлен и ядер остались в Lisp.Tests (PolyExprTests.fs)
module MPolyTests

open System
open System.Numerics
open Xunit
open MPoly
open PolyGcd
open PolyText

let private ctxOfSrc (srcs: string list) = ctxOf srcs []

// --- деление ---

[<Fact>]
let ``точное деление`` () =
    let ctx = ctxOfSrc ["x+y"; "x-y"]
    let a = mul (mul (polyIn ctx "x+y") (polyIn ctx "x-y")) (polyIn ctx "x+1")
    let b = polyIn ctx "x+y"
    match divExact a b with
    | Some q -> Assert.Equal(mul (polyIn ctx "x-y") (polyIn ctx "x+1"), q)
    | None -> Assert.Fail "должно делиться"
    Assert.True((divExact a (polyIn ctx "x+2")).IsNone)

[<Fact>]
let ``псевдоделение: lc^e a = q b + r`` () =
    let ctx = ctxOfSrc ["x+y"; "x-y"]
    let a = mul (polyIn ctx "3*x*x*x+y") (polyIn ctx "x+y")
    let b = polyIn ctx "2*y*x*x+1"
    let (q, r, e) = pseudoDivMod a b
    let lc = lcMain b
    Assert.Equal(mul (pow lc e) a, add (mul q b) r)
    Assert.True(mainVar r < mainVar b || degMain r < degMain b)

// --- НОД ---

[<Fact>]
let ``НОД: одномерный`` () =
    let ctx = ctxOfSrc ["x+1"]
    let a = mul (polyIn ctx "x+1") (polyIn ctx "x+2")
    let b = mul (polyIn ctx "x+1") (polyIn ctx "x-5")
    Assert.Equal(polyIn ctx "x+1", gcd a b)
    Assert.Equal(one, gcd (polyIn ctx "x+1") (polyIn ctx "x+2"))

[<Fact>]
let ``НОД: константы и нуль`` () =
    let ctx = ctxOfSrc ["x"]
    Assert.Equal(one, gcd (ofInt 6I) (polyIn ctx "x"))
    Assert.Equal(unitNormal (polyIn ctx "4*x"), gcd zero (polyIn ctx "4*x"))

[<Fact>]
let ``НОД: многомерный`` () =
    let ctx = ctxOfSrc ["x+y"]
    let g = mul (polyIn ctx "x^2+y+1") (polyIn ctx "x-2*y")
    let a = mul g (polyIn ctx "x+y")
    let b = mul g (polyIn ctx "x*y-3")
    let r = gcd a b
    Assert.Equal(unitNormal g, r)

[<Fact>]
let ``НОД: содержание по переменной`` () =
    let ctx = ctxOfSrc ["x+y"]
    // x и y главная: gcd(y*(x+1), y*(x-1)) = y
    let a = polyIn ctx "y*(x+1)"
    let b = polyIn ctx "y*(x-1)"
    Assert.Equal(polyIn ctx "y", gcd a b)
    Assert.Equal(polyIn ctx "x+y", gcd (polyIn ctx "(x+y)*(x+3)") (polyIn ctx "(x+y)*y"))

[<Fact>]
let ``НОД и НОК с рациональными коэффициентами`` () =
    let ctx = ctxOfSrc ["x"]
    let a = polyIn ctx "1/2*(x+1)*(x+2)"
    let b = polyIn ctx "1/3*(x+1)*(x+3)"
    Assert.Equal(polyIn ctx "x+1", gcd a b)
    Assert.Equal(unitNormal (polyIn ctx "(x+1)*(x+2)*(x+3)"), lcm a b)

// Случайный разреженный многочлен от двух переменных (фиксированный seed)
let randomPoly (rnd: Random) (x: int) (y: int) (maxDeg: int) (terms: int) : MPoly =
    let mutable p = zero
    for _ in 1 .. terms do
        let c = rnd.Next(-5, 6)
        let i, j = rnd.Next(0, maxDeg + 1), rnd.Next(0, maxDeg + 1)
        p <- add p (mulConst (BigInteger c, 1I) (mul (pow (var x) i) (pow (var y) j)))
    p

[<Fact>]
let ``НОД: случайные многочлены — НОД(a g, b g) делится на g и делит оба`` () =
    let rnd = Random 20271012
    for _ in 1 .. 25 do
        let a = randomPoly rnd 0 1 3 5
        let b = randomPoly rnd 0 1 3 5
        let g = randomPoly rnd 0 1 2 3
        if not (isZero a || isZero b || isZero g) then
            let ag, bg = mul a g, mul b g
            let r = gcd ag bg
            Assert.True((divExact r g).IsSome, "g | gcd")
            Assert.True((divExact ag r).IsSome, "gcd | a g")
            Assert.True((divExact bg r).IsSome, "gcd | b g")
            Assert.Equal(unitNormal r, r)

[<Fact>]
let ``НОД: трёхмерные случайные`` () =
    let rnd = Random 77
    let randomPoly3 () =
        let mutable p = zero
        for _ in 1 .. 4 do
            let c = rnd.Next(-3, 4)
            p <- add p (mulConst (BigInteger c, 1I) (mul (mul (pow (var 0) (rnd.Next 3)) (pow (var 1) (rnd.Next 3))) (pow (var 2) (rnd.Next 3))))
        p
    for _ in 1 .. 15 do
        let a, b, g = randomPoly3 (), randomPoly3 (), randomPoly3 ()
        if not (isZero a || isZero b || isZero g) then
            let ag, bg = mul a g, mul b g
            let r = gcd ag bg
            Assert.True((divExact r g).IsSome)
            Assert.True((divExact ag r).IsSome)
            Assert.True((divExact bg r).IsSome)

[<Fact>]
let ``НОД: плотные двумерные степени 10`` () =
    let rnd = Random 5
    let dense () =
        let mutable p = zero
        for i in 0 .. 5 do
            for j in 0 .. 5 do
                p <- add p (mulConst (BigInteger (rnd.Next(-3, 4)), 1I) (mul (pow (var 0) i) (pow (var 1) j)))
        p
    let g = dense ()
    let a, b = mul (dense ()) g, mul (dense ()) g
    let sw = Diagnostics.Stopwatch.StartNew()
    let r = gcd a b
    sw.Stop()
    Assert.True((divExact r g).IsSome)
    Assert.True((divExact a r).IsSome && (divExact b r).IsSome)
    Assert.True(sw.ElapsedMilliseconds < 20000L)

// --- тесты самого помощника PolyText (разбор инфиксной записи) ---

[<Fact>]
let ``PolyText: порядок переменных и разбор`` () =
    let ctx = ctxOf ["b*a + c"] ["t"]
    Assert.Equal<string[]>([| "c"; "b"; "a"; "t" |], ctx.Names)
    let p = polyIn ctx "(a + 1)*(a - 1) - a^2 + 3/2*b"
    let expected = sub (mulConst (3I, 2I) (var (idx ctx "b"))) one
    Assert.Equal(expected, p)
