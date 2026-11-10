// Тесты упрощения выражений (Simplify.fs)
module SimplifyTests

open System.Numerics
open Xunit
open Types
open Reader
open Simplify
open Order
open Expand
open Factor

// Вспомогательные функции
let isInt (expected: BigInteger) (v: LispValue) =
    match v with
    | LispInteger n -> Assert.Equal(expected, n)
    | other -> Assert.Fail($"Ожидался LispInteger {expected}, получено {other}")

let isSym (expected: string) (v: LispValue) =
    match v with
    | LispSym s -> Assert.Equal(expected, s)
    | other -> Assert.Fail($"Ожидался LispSym {expected}, получено {other}")

let isListHead (expected: string) (v: LispValue) =
    match v with
    | LispList (LispSym h :: _) -> Assert.Equal(expected, h)
    | other -> Assert.Fail($"Ожидался список с головой {expected}, получено {other}")

// Упростить строку
let simpStr (s: string) : LispValue =
    readAll s |> List.head |> simplify

// --- Упрощение сложения ---

[<Fact>]
let ``Упрощение (+ x 0) → x`` () =
    simpStr "(+ x 0)" |> isSym "x"

[<Fact>]
let ``Упрощение (+ 0 x) → x`` () =
    simpStr "(+ 0 x)" |> isSym "x"

[<Fact>]
let ``Константная свёртка сложения`` () =
    simpStr "(+ 2 3)" |> isInt 5I

[<Fact>]
let ``Константная свёртка с символом`` () =
    // (+ 2 3 x) → (+ 5 x)
    let result = simpStr "(+ 2 3 x)"
    match result with
    | LispList [LispSym "+"; LispInteger n; LispSym s] ->
        Assert.Equal(5I, n)
        Assert.Equal("x", s)
    | other -> Assert.Fail($"Ожидался (+ 5 x), получено {other}")

// --- Упрощение умножения ---

[<Fact>]
let ``Упрощение (* x 0) → 0`` () =
    simpStr "(* x 0)" |> isInt 0I

[<Fact>]
let ``Упрощение (* x 1) → x`` () =
    simpStr "(* x 1)" |> isSym "x"

[<Fact>]
let ``Константная свёртка умножения`` () =
    simpStr "(* 2 3)" |> isInt 6I

// --- Упрощение вычитания ---

[<Fact>]
let ``Упрощение (- x 0) → x`` () =
    simpStr "(- x 0)" |> isSym "x"

[<Fact>]
let ``Константная свёртка вычитания`` () =
    simpStr "(- 5 3)" |> isInt 2I

// --- Упрощение степени ---

[<Fact>]
let ``Упрощение (^ x 0) → 1`` () =
    simpStr "(^ x 0)" |> isInt 1I

[<Fact>]
let ``Упрощение (^ x 1) → x`` () =
    simpStr "(^ x 1)" |> isSym "x"

[<Fact>]
let ``Константная свёртка степени`` () =
    simpStr "(^ 2 10)" |> isInt 1024I

// --- Рекурсивное упрощение ---

[<Fact>]
let ``Упрощение вложенных выражений`` () =
    // (* (+ x 0) 1) → x
    simpStr "(* (+ x 0) 1)" |> isSym "x"

[<Fact>]
let ``Упрощение вложенных констант`` () =
    // (+ (* 2 3) (* 4 5)) → (+ 6 20) → 26
    simpStr "(+ (* 2 3) (* 4 5))" |> isInt 26I

// --- Вызов simplify из Lisp ---

open Evaluator

[<Fact>]
let ``Simplify из REPL: (+ x 0) → x`` () =
    let result = readAll "(simplify '(+ x 0))" |> List.head |> fun e -> eval e globalEnv
    result |> isSym "x"

[<Fact>]
let ``Simplify из REPL: (* 2 3) → 6`` () =
    let result = readAll "(simplify '(* 2 3))" |> List.head |> fun e -> eval e globalEnv
    result |> isInt 6I

[<Fact>]
let ``Simplify из REPL: (^ x 1) → x`` () =
    let result = readAll "(simplify '(^ x 1))" |> List.head |> fun e -> eval e globalEnv
    result |> isSym "x"
