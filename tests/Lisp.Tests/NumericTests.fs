// Тесты числовой башни (Numeric.fs)
module NumericTests

open System.Numerics
open Xunit
open Types
open Numeric

// --- Вспомогательные функции для проверки ---

let isInt (expected: BigInteger) (v: LispValue) =
    match v with
    | LispInteger n -> Assert.Equal(expected, n)
    | other -> Assert.Fail($"Ожидался LispInteger {expected}, получено {other}")

let isRat (expectedP: BigInteger) (expectedQ: BigInteger) (v: LispValue) =
    match v with
    | LispRational (p, q) ->
        Assert.Equal(expectedP, p)
        Assert.Equal(expectedQ, q)
    | other -> Assert.Fail($"Ожидался LispRational {expectedP}/{expectedQ}, получено {other}")

let isFloat (expected: float) (v: LispValue) =
    match v with
    | LispFloat f -> Assert.Equal(expected, f, 3)
    | other -> Assert.Fail($"Ожидался LispFloat {expected}, получено {other}")

// --- Целочисленная арифметика ---

[<Fact>]
let ``Сложение целых`` () =
    add (LispInteger 2I) (LispInteger 3I) |> isInt 5I

[<Fact>]
let ``Вычитание целых`` () =
    sub (LispInteger 10I) (LispInteger 3I) |> isInt 7I

[<Fact>]
let ``Умножение целых`` () =
    mul (LispInteger 6I) (LispInteger 7I) |> isInt 42I

[<Fact>]
let ``Деление целых — точное`` () =
    div (LispInteger 10I) (LispInteger 2I) |> isInt 5I

[<Fact>]
let ``Деление целых — неточное даёт рациональное`` () =
    div (LispInteger 1I) (LispInteger 3I) |> isRat 1I 3I

// --- Рациональные ---

[<Fact>]
let ``makeRational сокращает дробь`` () =
    makeRational 6I 8I |> isRat 3I 4I

[<Fact>]
let ``makeRational возвращает целое если знаменатель 1`` () =
    makeRational 10I 2I |> isInt 5I

[<Fact>]
let ``makeRational нормализует знак`` () =
    makeRational 1I (-2I) |> isRat (-1I) 2I

[<Fact>]
let ``Сложение рациональных`` () =
    add (LispRational (1I, 2I)) (LispRational (1I, 3I)) |> isRat 5I 6I

[<Fact>]
let ``Умножение рациональных`` () =
    mul (LispRational (2I, 3I)) (LispRational (3I, 4I)) |> isRat 1I 2I

// --- Type promotion ---

[<Fact>]
let ``Сложение целого и рационального — promotion к рациональному`` () =
    add (LispInteger 1I) (LispRational (1I, 2I)) |> isRat 3I 2I

[<Fact>]
let ``Сложение целого и float — promotion к float`` () =
    add (LispInteger 1I) (LispFloat 2.5) |> isFloat 3.5

[<Fact>]
let ``Сложение рационального и float — promotion к float`` () =
    add (LispRational (1I, 2I)) (LispFloat 1.0) |> isFloat 1.5

// --- Комплексные ---

[<Fact>]
let ``Сложение комплексных`` () =
    let a = LispComplex (LispInteger 1I, LispInteger 2I)   // 1 + 2i
    let b = LispComplex (LispInteger 3I, LispInteger 4I)   // 3 + 4i
    let result = add a b
    match result with
    | LispComplex (re, im) ->
        re |> isInt 4I
        im |> isInt 6I
    | other -> Assert.Fail($"Ожидался комплексный, получено {other}")

[<Fact>]
let ``Сложение целого и комплексного — promotion к комплексному`` () =
    let a = LispInteger 5I
    let b = LispComplex (LispInteger 1I, LispInteger 1I)
    let result = add a b
    match result with
    | LispComplex (re, im) ->
        re |> isInt 6I
        im |> isInt 1I
    | other -> Assert.Fail($"Ожидался комплексный, получено {other}")

// --- GCD ---

[<Fact>]
let ``GCD двух чисел`` () =
    Assert.Equal(6I, gcd 12I 18I)

[<Fact>]
let ``GCD с нулём`` () =
    Assert.Equal(7I, gcd 7I 0I)

// --- Сравнения ---

[<Fact>]
let ``Сравнение целых на равенство`` () =
    Assert.True(numEqual (LispInteger 5I) (LispInteger 5I))
    Assert.False(numEqual (LispInteger 5I) (LispInteger 6I))

[<Fact>]
let ``Сравнение целых на меньше`` () =
    Assert.True(numLess (LispInteger 3I) (LispInteger 5I))
    Assert.False(numLess (LispInteger 5I) (LispInteger 3I))

[<Fact>]
let ``Сравнение целого и рационального`` () =
    // 2 = 4/2 → равны
    Assert.True(numEqual (LispInteger 2I) (LispRational (4I, 2I)))
