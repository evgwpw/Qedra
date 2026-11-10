// Тесты символьного интегрирования (lib/integrate.lisp; до шага 19 — Integrate.fs, шаг 7)
// Ожидания записаны под фактический вывод simplify (порядок слагаемых может
// отличаться от математической записи — это нормально)
module IntegrateTests

open System
open System.Numerics
open Xunit
open Types
open Reader
open Simplify
open Order
open Expand
open Factor
open Differentiate
open Evaluator
open Printer

let parse (s: string) : LispValue = readAll s |> List.head

let evalStr (s: string) : LispValue =
    readAll s |> List.head |> fun e2 -> eval e2 globalEnv

// Шаг 19: интегратор — Lisp-функция (integrate e x); математика та же, что в Integrate.fs (шаг 7)
let integrate (x: string) (e: LispValue) : LispValue =
    eval (LispList [LispSym "integrate"; LispList [LispSym "quote"; e]; LispList [LispSym "quote"; LispSym x]]) globalEnv

let isStr (expected: string) (v: LispValue) =
    Assert.True((prettyPrint v = expected), $"Ожидалось {expected}, получено {prettyPrint v}")

// --- Базовые степени ---

[<Fact>]
let ``int x dx = x^2/2`` () =
    integrate "x" (parse "x") |> isStr "(* 1/2 (^ x 2))"

[<Fact>]
let ``int x^2 dx = x^3/3`` () =
    integrate "x" (parse "(^ x 2)") |> isStr "(* 1/3 (^ x 3))"

[<Fact>]
let ``int x^5 dx = x^6/6`` () =
    integrate "x" (parse "(^ x 5)") |> isStr "(* 1/6 (^ x 6))"

[<Fact>]
let ``int c dx = c*x`` () =
    integrate "x" (parse "5") |> isStr "(* 5 x)"

[<Fact>]
let ``int a^2 dx = a^2*x (не зависит от x)`` () =
    integrate "x" (parse "(^ a 2)") |> isStr "(* (^ a 2) x)"

// --- Суммы, разности, числовые множители ---

[<Fact>]
let ``int (x^2 + 3x + 5) dx`` () =
    integrate "x" (parse "(+ (^ x 2) (* 3 x) 5)")
    |> isStr "(+ (* 5 x) (* 3/2 (^ x 2)) (* 1/3 (^ x 3)))"

[<Fact>]
let ``int (a - b) dx = (a-b)*x — константа от x`` () =
    integrate "x" (parse "(- a b)") |> isStr "(* x (+ a (* -1 b)))"

[<Fact>]
let ``int 3*sin(x) dx = -3*cos(x)`` () =
    integrate "x" (parse "(* 3 (sin x))") |> isStr "(* -3 (cos x))"

// --- Линейная подстановка u = a*x + b ---

[<Fact>]
let ``int sin(2x+1) dx = -cos(2x+1)/2`` () =
    integrate "x" (parse "(sin (+ (* 2 x) 1))") |> isStr "(* -1/2 (cos (+ 1 (* 2 x))))"

[<Fact>]
let ``int cos(3x+b) dx = sin(3x+b)/3`` () =
    integrate "x" (parse "(cos (+ (* 3 x) b))") |> isStr "(* 1/3 (sin (+ b (* 3 x))))"

[<Fact>]
let ``int exp(3x) dx = exp(3x)/3`` () =
    integrate "x" (parse "(exp (* 3 x))") |> isStr "(* 1/3 (exp (* 3 x)))"

[<Fact>]
let ``int (2x+1)^2 dx = (2x+1)^3/6`` () =
    integrate "x" (parse "(^ (+ (* 2 x) 1) 2)") |> isStr "(* 1/6 (^ (+ 1 (* 2 x)) 3))"

[<Fact>]
let ``int sin(5x+2) dx`` () =
    integrate "x" (parse "(sin (+ (* 5 x) 2))") |> isStr "(* -1/5 (cos (+ 2 (* 5 x))))"

// --- Обратные степени и логарифм ---

[<Fact>]
let ``int 1/x dx = log(x)`` () =
    integrate "x" (parse "(/ 1 x)") |> isStr "(log x)"

[<Fact>]
let ``int 1/(3x+2) dx = log(3x+2)/3`` () =
    integrate "x" (parse "(/ 1 (+ (* 3 x) 2))") |> isStr "(* 1/3 (log (+ 2 (* 3 x))))"

[<Fact>]
let ``int x^(-1) через степень = log(x)`` () =
    integrate "x" (parse "(^ x -1)") |> isStr "(log x)"

[<Fact>]
let ``int log(x) dx = x*log(x) - x`` () =
    integrate "x" (parse "(log x)") |> isStr "(+ (* -1 x) (* x (log x)))"

// --- Суммы функций ---

[<Fact>]
let ``int (log x + exp x) dx`` () =
    integrate "x" (parse "(+ (log x) (exp x))") |> isStr "(+ (* -1 x) (* x (log x)) (exp x))"

[<Fact>]
let ``int (x^3 + 2cos x + 7) dx`` () =
    integrate "x" (parse "(+ (^ x 3) (* 2 (cos x)) 7)")
    |> isStr "(+ (* 7 x) (* 1/4 (^ x 4)) (* 2 (sin x)))"

// --- REPL-уровень ---

[<Fact>]
let ``integrate builtin из REPL`` () =
    evalStr "(integrate (quote x) (quote (^ x 2)))" |> isStr "(* 1/3 (^ x 3))"

[<Fact>]
let ``integrate с quote-сокращением 'expr`` () =
    evalStr "(integrate 'x '(^ x 3))" |> isStr "(* 1/4 (^ x 4))"