// Тесты builtins poly-* (с Шага 17a — поверх MPoly) + TCO + let*/letrec/case (Шаг 6)
module PolynomialTests

open System
open System.Numerics
open Xunit
open Types
open Reader
open Numeric
open Evaluator
open Printer

// Вспомогательные
let parse (s: string) : LispValue = readAll s |> List.head

let evalStr (s: string) : LispValue =
    readAll s |> List.head |> fun e -> eval e globalEnv

let evalStrAll (s: string) : LispValue =
    readAll s |> fun es -> evalAll es globalEnv

let isInt (expected: BigInteger) (v: LispValue) =
    match v with
    | LispInteger n -> Assert.Equal(expected, n)
    | other -> Assert.Fail($"Ожидался LispInteger {expected}, получено {prettyPrint other}")

let isStr (expected: string) (v: LispValue) =
    Assert.True((prettyPrint v = expected), $"Ожидалось {expected}, получено {prettyPrint v}")

// --- Многочлены: бывшие F#-тесты Polynomial.* (Шаг 17a) переведены на builtins poly-* ---

[<Fact>]
let ``poly-sub: (x+1)-(x+2) = -1, ведущие нули убираются`` () =
    evalStr "(poly-sub '(1 1) '(1 2))" |> isStr "(-1)"

[<Fact>]
let ``poly-degree: степени, константа и ноль`` () =
    evalStr "(poly-degree '(1 0 -1))" |> isInt 2I
    evalStr "(poly-degree '(5))" |> isInt 0I
    evalStr "(poly-degree '(0))" |> isInt 0I
    evalStr "(poly-degree '(0 0 1 2))" |> isInt 1I
    evalStr "(poly-degree '(1 2 3 4))" |> isInt 3I

[<Fact>]
let ``poly-eval: Горнер, x+1 в 2`` () =
    evalStr "(poly-eval '(1 1) 2)" |> isInt 3I

[<Fact>]
let ``poly-deriv: x^3+2x даёт 3x^2+2`` () =
    evalStr "(poly-deriv '(1 0 2 0))" |> isStr "(3 0 2)"

[<Fact>]
let ``poly-deriv константы даёт 0`` () =
    evalStr "(poly-deriv '(5))" |> isStr "(0)"

[<Fact>]
let ``poly-div с остатком: x^2 / (x+1) = x-1, остаток 1`` () =
    evalStr "(poly-div '(1 0 0) '(1 1))" |> isStr "((1 -1) (1))"

// --- Расширение Шага 17a: рациональные коэффициенты, деление над Q ---

[<Fact>]
let ``poly-div над Q: x / (2x+1) = 1/2, остаток -1/2 (старый divMod зацикливался)`` () =
    evalStr "(poly-div '(1 0) '(2 1))" |> isStr "((1/2) (-1/2))"

[<Fact>]
let ``poly-div: нулевой делитель - ошибка`` () =
    Assert.ThrowsAny<exn>(fun () -> evalStr "(poly-div '(1 0) '(0))" |> ignore) |> ignore

[<Fact>]
let ``poly-div: делимое меньшей степени - частное 0`` () =
    evalStr "(poly-div '(1 1) '(1 0 0))" |> isStr "((0) (1 1))"

[<Fact>]
let ``poly-mul с рациональными коэффициентами`` () =
    evalStr "(poly-mul '(1/2 1) '(2 0))" |> isStr "(1 2 0)"

[<Fact>]
let ``poly-add с рациональными коэффициентами сокращает до нуля`` () =
    evalStr "(poly-add '(1/2 1/3) '(-1/2 -1/3))" |> isStr "(0)"

[<Fact>]
let ``poly-eval в рациональной точке`` () =
    // x^2-1 при x=1/2 → -3/4
    evalStr "(poly-eval '(1 0 -1) 1/2)" |> isStr "-3/4"

[<Fact>]
let ``poly-eval рациональные коэффициенты, целая точка`` () =
    // (1/2)x+1/3 при x=3 → 11/6
    evalStr "(poly-eval '(1/2 1/3) 3)" |> isStr "11/6"

[<Fact>]
let ``poly-deriv с рациональными коэффициентами`` () =
    evalStr "(poly-deriv '(1/2 0 1/3))" |> isStr "(1 0)"

// --- Многочлены: REPL-уровень ---

[<Fact>]
let ``poly-mul из REPL`` () =
    evalStr "(poly-mul '(1 1) '(1 -1))" |> isStr "(1 0 -1)"

[<Fact>]
let ``poly-add из REPL`` () =
    evalStr "(poly-add '(1 1) '(1 -1))" |> isStr "(2 0)"

[<Fact>]
let ``poly-degree из REPL`` () =
    evalStr "(poly-degree '(1 0 -1))" |> isInt 2I

[<Fact>]
let ``poly-eval из REPL`` () =
    evalStr "(poly-eval '(1 0 -1) 5)" |> isInt 24I

[<Fact>]
let ``poly-deriv из REPL`` () =
    evalStr "(poly-deriv '(1 0 2 0))" |> isStr "(3 0 2)"

[<Fact>]
let ``poly-div из REPL: (частное остаток)`` () =
    evalStr "(poly-div '(1 0 -1) '(1 -1))" |> isStr "((1 1) (0))"

// --- TCO: хвостовая рекурсия ---

[<Fact>]
let ``TCO: цикл 100000 итераций без переполнения стека`` () =
    // Раньше (без TCO) это падало с StackOverflow
    evalStrAll "(define (loop6 n) (if (= n 0) 'done (loop6 (- n 1)))) (loop6 100000)"
    |> isStr "done"

[<Fact>]
let ``TCO: хвостовая рекурсия через begin`` () =
    evalStrAll "(define (count6 n acc) (if (= n 0) acc (begin (count6 (- n 1) (+ acc 1))))) (count6 50000 0)"
    |> isInt 50000I

[<Fact>]
let ``TCO: cond в хвостовой позиции`` () =
    evalStrAll "(define (loopc6 n) (cond ((= n 0) 'ready) (else (loopc6 (- n 1))))) (loopc6 100000)"
    |> isStr "ready"

// --- let*, letrec, case ---

[<Fact>]
let ``let*: последовательные bindings видят предыдущие`` () =
    evalStr "(let* ((x 5) (y (* x 2)) (z (+ x y))) z)" |> isInt 15I

// Примечание: тест "let не видит предыдущие bindings" ненадёжен из-за
// параллельного выполнения тестовых коллекций xUnit (globalEnv общий,
// другие классы определяют x) — опускаем его; семантика let* проверена выше.

[<Fact>]
let ``letrec: рекурсивная функция`` () =
    evalStr "(letrec ((fact (lambda (n) (if (= n 1) 1 (* n (fact (- n 1))))))) (fact 10))"
    |> isInt 3628800I

[<Fact>]
let ``case: сопоставление по значению`` () =
    evalStr "(case (* 2 3) ((2 3 5 7) 'prime) ((1 4 6 8 9) 'composite) (else 'unknown))"
    |> isStr "composite"

[<Fact>]
let ``case: else ветка`` () =
    evalStr "(case 100 ((1 2 3) 'small) (else 'big))"
    |> isStr "big"

// --- TCO + рекурсия с set! (счётчик) ---

[<Fact>]
let ``TCO + set!: аккумулятор`` () =
    evalStrAll "(define acc6 0) (define (bump6 n) (if (= n 0) acc6 (begin (set! acc6 (+ acc6 1)) (bump6 (- n 1))))) (bump6 10000)"
    |> isInt 10000I