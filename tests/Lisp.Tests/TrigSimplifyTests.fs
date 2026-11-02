// Тесты тригонометрических тождеств в simplify (Шаг 8c)
// Правила живут в PatternMatching.fs (trigRules), применяются в Simplify.fs
module TrigSimplifyTests

open System.Numerics
open Xunit
open Types
open Reader
open Simplify
open Order
open Expand
open Factor

// Вспомогательные проверки
let isInt (expected: BigInteger) (v: LispValue) =
    match v with
    | LispInteger n -> Assert.Equal(expected, n)
    | other -> Assert.Fail($"Ожидался LispInteger {expected}, получено {other}")

let isListHead (expected: string) (v: LispValue) =
    match v with
    | LispList (LispSym h :: _) -> Assert.Equal(expected, h)
    | other -> Assert.Fail($"Ожидался список с головой {expected}, получено {other}")

// Упростить строку
let simpStr (s: string) : LispValue =
    readAll s |> List.head |> simplify

// Проверка: результат — (fn x) в степени 2: (^ (sin x) 2)
let isSquareOf (fn: string) (v: LispValue) =
    match v with
    | LispList [LispSym "^"; LispList [LispSym f; LispSym "x"]; LispInteger n] ->
        Assert.Equal(fn, f)
        Assert.Equal(BigInteger(2), n)
    | other -> Assert.Fail($"Ожидался (^ ({fn} x) 2), получено {other}")

// --- Пифагоровы тождества ---

[<Fact>]
let ``sin^2(x) + cos^2(x) → 1`` () =
    simpStr "(+ (^ (sin x) 2) (^ (cos x) 2))" |> isInt 1I

[<Fact>]
let ``cos^2(x) + sin^2(x) → 1 (обратный порядок)`` () =
    simpStr "(+ (^ (cos x) 2) (^ (sin x) 2))" |> isInt 1I

[<Fact>]
let ``sin^2(y) + cos^2(y) → 1 (другая переменная)`` () =
    simpStr "(+ (^ (sin y) 2) (^ (cos y) 2))" |> isInt 1I

[<Fact>]
let ``1 - cos^2(x) → sin^2(x)`` () =
    simpStr "(- 1 (^ (cos x) 2))" |> isSquareOf "sin"

[<Fact>]
let ``1 - sin^2(x) → cos^2(x)`` () =
    simpStr "(- 1 (^ (sin x) 2))" |> isSquareOf "cos"

[<Fact>]
let ``sin^2(x) + cos^2(x) внутри большего выражения`` () =
    // (* 3 (+ sin²x cos²x)) → (* 3 1) → 3
    simpStr "(* 3 (+ (^ (sin x) 2) (^ (cos x) 2)))" |> isInt 3I

// --- Сведение к sin/cos ---

[<Fact>]
let ``tan(x) → sin(x)/cos(x)`` () =
    let result = simpStr "(tan x)"
    match result with
    | LispList [LispSym "*"; LispList [LispSym "^"; LispList [LispSym "cos"; _]; LispInteger m]; LispList [LispSym "sin"; _]] when m = -1I -> ()
    | other -> Assert.Fail($"Ожидалось (* (^ (cos x) -1) (sin x)), получено {other}")

[<Fact>]
let ``cot(x) → cos(x)/sin(x)`` () =
    let result = simpStr "(cot x)"
    match result with
    | LispList [LispSym "*"; LispList [LispSym "cos"; _]; LispList [LispSym "^"; LispList [LispSym "sin"; _]; LispInteger m]] when m = -1I -> ()
    | other -> Assert.Fail($"Ожидалось (* (cos x) (^ (sin x) -1)), получено {other}")

[<Fact>]
let ``sec(x) → 1/cos(x)`` () =
    let result = simpStr "(sec x)"
    match result with
    | LispList [LispSym "^"; LispList [LispSym "cos"; _]; LispInteger m] when m = -1I -> ()
    | other -> Assert.Fail($"Ожидалось (^ (cos x) -1), получено {other}")

[<Fact>]
let ``csc(x) → 1/sin(x)`` () =
    let result = simpStr "(csc x)"
    match result with
    | LispList [LispSym "^"; LispList [LispSym "sin"; _]; LispInteger m] when m = -1I -> ()
    | other -> Assert.Fail($"Ожидалось (^ (sin x) -1), получено {other}")

// --- Негативные: правила не должны срабатывать зря ---

[<Fact>]
let ``sin^2(x) + cos^2(y) ≠ 1 (разные аргументы)`` () =
    // Правило не срабатывает — остаётся сумма
    let result = simpStr "(+ (^ (sin x) 2) (^ (cos y) 2))"
    match result with
    | LispList (LispSym "+" :: _) -> ()
    | other -> Assert.Fail($"Ожидалась сумма, получено {other}")

[<Fact>]
let ``sin^2(x) + cos(x) ≠ 1 (нет квадрата у cos)`` () =
    let result = simpStr "(+ (^ (sin x) 2) (cos x))"
    match result with
    | LispList (LispSym "+" :: _) -> ()
    | other -> Assert.Fail($"Ожидалась сумма, получено {other}")

[<Fact>]
let ``sin(x) остаётся sin(x)`` () =
    simpStr "(sin x)" |> isListHead "sin"

// --- Вызов из REPL ---

open Evaluator

[<Fact>]
let ``Simplify из REPL: sin^2 + cos^2 → 1`` () =
    let result =
        readAll "(simplify '(+ (^ (sin x) 2) (^ (cos x) 2)))"
        |> List.head |> fun e -> eval e globalEnv
    result |> isInt 1I

[<Fact>]
let ``Simplify из REPL: tan(x) → sin/cos`` () =
    let result =
        readAll "(simplify '(tan x))"
        |> List.head |> fun e -> eval e globalEnv
    match result with
    | LispList [LispSym "*"; LispList [LispSym "^"; LispList [LispSym "cos"; _]; LispInteger m]; LispList [LispSym "sin"; _]] when m = -1I -> ()
    | other -> Assert.Fail($"Ожидалось (* (^ (cos x) -1) (sin x)), получено {other}")
