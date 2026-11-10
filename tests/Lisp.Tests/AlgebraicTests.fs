// Тесты алгебраических чисел (Шаг 12)
module AlgebraicTests

open System.Numerics
open Xunit
open Types
open Reader
open Numeric
open Algebraic
open Sturm
open Resultant
open Evaluator

// Вспомогательные проверки
let isInt (expected: BigInteger) (v: LispValue) =
    match v with
    | LispInteger n -> Assert.Equal(expected, n)
    | other -> Assert.Fail($"Ожидался LispInteger {expected}, получено {other}")

let isAlgebraicRoot (poly: BigInteger list) (v: LispValue) =
    match v with
    | LispAlgebraic (p, _, _) -> Assert.Equal<BigInteger list>(poly, p)
    | other -> Assert.Fail($"Ожидался LispAlgebraic, получено {other}")

let evalStr (s: string) : LispValue =
    readAll s |> List.head |> fun e -> eval e globalEnv

// --- Изоляция корней: тесты Sturm.isolateRoots — в Cas.Algebra.Tests (SturmTests.fs, шаг 21h') ---

// --- Конструкция ---

[<Fact>]
let ``algebraic создаёт с явным интервалом`` () =
    let r = evalStr "(algebraic '(1 0 -2) 1 2)"
    match r with
    | LispAlgebraic (p, (loN, loD), (hiN, hiD)) ->
        Assert.Equal<BigInteger list>([1I; 0I; -2I], p)
        Assert.Equal(1I, loN)
        Assert.Equal(1I, loD)
        Assert.Equal(2I, hiN)
        Assert.Equal(1I, hiD)
    | other -> Assert.Fail($"Ожидался LispAlgebraic, получено {other}")

[<Fact>]
let ``algebraic принимает рациональные границы`` () =
    let r = evalStr "(algebraic '(1 0 -2) 0 3/2)"
    match r with
    | LispAlgebraic (_, (loN, loD), (hiN, hiD)) ->
        Assert.Equal(0I, loN)
        Assert.Equal(3I, hiN)
        Assert.Equal(2I, hiD)
    | other -> Assert.Fail($"Ожидался LispAlgebraic, получено {other}")

[<Fact>]
let ``algebraic poly сохраняется как есть`` () =
    let r = evalStr "(algebraic '(1 -3 1) 0 1)"
    match r with
    | LispAlgebraic (p, _, _) -> Assert.Equal<BigInteger list>([1I; -3I; 1I], p)
    | other -> Assert.Fail($"Ожидался LispAlgebraic, получено {other}")

// --- Сравнение ---

[<Fact>]
let ``sqrt2 < sqrt3`` () =
    let a = evalStr "(sqrt 2)"
    let b = evalStr "(sqrt 3)"
    Assert.Equal(-1, algCompare a b)

[<Fact>]
let ``sqrt3 > sqrt2`` () =
    let a = evalStr "(sqrt 3)"
    let b = evalStr "(sqrt 2)"
    Assert.Equal(1, algCompare a b)

[<Fact>]
let ``sqrt2 = sqrt2`` () =
    let a = evalStr "(sqrt 2)"
    let b = evalStr "(sqrt 2)"
    Assert.Equal(0, algCompare a b)

[<Fact>]
let ``sqrt2 > 1`` () =
    let a = evalStr "(sqrt 2)"
    let b = LispInteger 1I
    Assert.Equal(1, algCompare a b)

[<Fact>]
let ``1 < sqrt2`` () =
    let a = LispInteger 1I
    let b = evalStr "(sqrt 2)"
    Assert.Equal(-1, algCompare a b)

[<Fact>]
let ``-sqrt2 < sqrt2`` () =
    let a = algNeg (evalStr "(sqrt 2)")
    let b = evalStr "(sqrt 2)"
    Assert.Equal(-1, algCompare a b)

// --- Арифметика ---

[<Fact>]
let ``sqrt2 + sqrt2 → 2 (число через результатант и simplify)`` () =
    let a = evalStr "(sqrt 2)"
    let r = evalStr "(+ (sqrt 2) (sqrt 2))"
    // 2*sqrt2 — корень x²-8; проверим что algCompare с 2√2 = 0
    match r with
    | LispAlgebraic _ -> Assert.Equal(0, algCompare r (algMulRaw (LispInteger 2I) a))
    | other -> Assert.Fail($"Ожидался LispAlgebraic, получено {other}")

[<Fact>]
let ``sqrt2 * sqrt2 → 2`` () =
    let r = evalStr "(* (sqrt 2) (sqrt 2))"
    isInt 2I r

[<Fact>]
let ``sqrt2 - sqrt2 → 0`` () =
    let r = evalStr "(- (sqrt 2) (sqrt 2))"
    isInt 0I r

[<Fact>]
let ``sqrt2 + 1 → корень x^2-2x-1`` () =
    let r = evalStr "(+ (sqrt 2) 1)"
    match r with
    | LispAlgebraic (p, _, _) ->
        // (√2+1) удовлетворяет x²-2x-1 = 0; сравним результат с algAddRaw
        Assert.Equal(0, algCompare r (algAddRaw (evalStr "(sqrt 2)") (LispInteger 1I)))
    | other -> Assert.Fail($"Ожидался LispAlgebraic, получено {other}")

[<Fact>]
let ``sqrt2 * 3 → 3sqrt2`` () =
    let r = evalStr "(* (sqrt 2) 3)"
    let expected = algMulRaw (evalStr "(sqrt 2)") (LispInteger 3I)
    Assert.Equal(0, algCompare r expected)

[<Fact>]
let ``alg-neg sqrt2 → -sqrt2`` () =
    let r = algNeg (evalStr "(sqrt 2)")
    let zero = evalStr "(+ (sqrt 2) (alg-neg (sqrt 2)))"
    Assert.Equal(0, algCompare zero (LispInteger 0I))

[<Fact>]
let ``sqrt2 * sqrt3 → sqrt6`` () =
    let r = evalStr "(* (sqrt 2) (sqrt 3))"
    let expected = evalStr "(sqrt 6)"
    Assert.Equal(0, algCompare r expected)

[<Fact>]
let ``sqrt2 + sqrt3 → корень x^4-10x^2+1`` () =
    let r = evalStr "(+ (sqrt 2) (sqrt 3))"
    match r with
    | LispAlgebraic (p, _, _) ->
        // минимальный многочлен √2+√3: x⁴ - 10x² + 1
        Assert.Equal<BigInteger list>([1I; 0I; -10I; 0I; 1I], p)
    | other -> Assert.Fail($"Ожидался LispAlgebraic, получено {other}")

// --- sqrt override ---

[<Fact>]
let ``sqrt 4 → 2`` () =
    let r = evalStr "(sqrt 4)"
    isInt 2I r

[<Fact>]
let ``sqrt 2 → алгебраическое`` () =
    let r = evalStr "(sqrt 2)"
    match r with
    | LispAlgebraic (p, _, _) -> Assert.Equal<BigInteger list>([1I; 0I; -2I], p)
    | other -> Assert.Fail($"Ожидался LispAlgebraic, получено {other}")

[<Fact>]
let ``sqrt 9 → 3`` () =
    let r = evalStr "(sqrt 9)"
    isInt 3I r

// --- Интеграция через evalStr ---

[<Fact>]
let ``+ с алгебраическим через eval`` () =
    let r = evalStr "(+ (sqrt 2) (sqrt 8))"
    // √2+√8 = 3√2
    let expected = algMulRaw (LispInteger 3I) (evalStr "(sqrt 2)")
    Assert.Equal(0, algCompare r expected)

[<Fact>]
let ``* с алгебраическим через eval`` () =
    let r = evalStr "(* (sqrt 2) (sqrt 2))"
    isInt 2I r

[<Fact>]
let ``< с алгебраическим через eval`` () =
    let r = evalStr "(< (sqrt 2) (sqrt 3))"
    match r with
    | LispBool true -> ()
    | other -> Assert.Fail($"Ожидался #t, получено {other}")

[<Fact>]
let ``= с алгебраическим через eval`` () =
    let r = evalStr "(= (sqrt 2) (sqrt 2))"
    match r with
    | LispBool true -> ()
    | other -> Assert.Fail($"Ожидался #t, получено {other}")

// --- Предикат alg? ---

[<Fact>]
let ``alg? (sqrt 2) → #t`` () =
    let r = evalStr "(alg? (sqrt 2))"
    match r with
    | LispBool true -> ()
    | other -> Assert.Fail($"Ожидался #t, получено {other}")

[<Fact>]
let ``alg? 5 → #f`` () =
    let r = evalStr "(alg? 5)"
    match r with
    | LispBool false -> ()
    | other -> Assert.Fail($"Ожидался #f, получено {other}")

// --- Вспомогательные модульные функции ---

// isqrtBigint, resultant, rationalRoots — в Cas.Algebra.Tests (RationalTests.fs, SturmTests.fs, шаг 21h')

[<Fact>]
let ``simplifyAlgebraic степени 1 → рациональное`` () =
    // 2x - 4 = 0 → x = 2
    let r = simplifyAlgebraic [2I; -4I] (1I, 1I) (3I, 1I)
    isInt 2I r

[<Fact>]
let ``alg-refine сужает интервал`` () =
    let before = evalStr "(sqrt 2)"
    let r = evalStr "(alg-refine (sqrt 2))"
    match before, r with
    | LispAlgebraic (_, (bloN, bloD), (bhiN, bhiD)), LispAlgebraic (_, (loN, loD), (hiN, hiD)) ->
        // после уточнения интервал содержит √2 (lo² < 2 < hi²) и уже исходного
        Assert.True(loN * loN < 2I * loD * loD)
        Assert.True(hiN * hiN > 2I * hiD * hiD)
        Assert.True(ratCompare (hiN - loN, hiD) (bhiN - bloN, bhiD) <= 0)
    | a, b -> Assert.Fail($"Ожидались LispAlgebraic, получено {a} и {b}")
