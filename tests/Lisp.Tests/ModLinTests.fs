// Шаг PERF.F1: треугольный базис по модулю простого (ModLinBuiltins) и комплексный Li₂ (SolveNum.li2Complex)
module ModLinTests

open System
open System.Numerics
open Xunit
open Types
open Reader
open Evaluator
open Builtins

let evalStr (s: string) : LispValue = readAll s |> List.head |> fun e -> eval e globalEnv

let P = 2147483579L

// --- базис ---

[<Fact>]
let ``PERF.F1: modbasis — ранг, зависимая и несовместная строки, решение`` () =
    // x + y = 3, x - y = 1 → x = 2, y = 1; третья строка 2x = 4 зависима; четвёртая x = 5 несовместна
    let r = evalStr "(let ((b (modbasis-new 2 2147483579))) (list (modbasis-add! b '(1 1 3)) (modbasis-add! b '(1 -1 1)) (modbasis-add! b '(2 0 4)) (modbasis-solve b) (modbasis-rank b) (modbasis-add! b '(1 0 5))))"
    Assert.Equal("(indep indep dep (2 1) 2 bad)", Printer.prettyPrint r)

[<Fact>]
let ``PERF.F1: modbasis — свободные неизвестные равны 0, отрицательные и большие числа приводятся`` () =
    let r = evalStr "(let ((b (modbasis-new 3 2147483579))) (list (modbasis-add! b '(2 4 6 8)) (modbasis-add! b (list 0 -1 0 (- 2147483579 3))) (modbasis-solve b)))"
    // 2x + 4y + 6z = 8; −y = −3 (по модулю) → y = 3; z свободна (0): x = (8 − 12) / 2 = −2
    Assert.Equal(sprintf "(indep indep (%d 3 0))" (P - 2L), Printer.prettyPrint r)

// --- Li₂ ---

let li2 (re: float) (im: float) = SolveNum.li2Complex (Complex(re, im))

let near (tol: float) (expected: Complex) (actual: Complex) =
    Assert.True(Complex.Abs (expected - actual) < tol, sprintf "ожидалось %A, получено %A" expected actual)

[<Fact>]
let ``PERF.F1: Li₂ — эталонные значения`` () =
    let pi2 = Math.PI * Math.PI
    let catalan = 0.915965594177219015054603514932384110774
    near 1e-13 (Complex(-pi2 / 48.0, catalan)) (li2 0.0 1.0)                       // Li₂(i)
    near 1e-13 (Complex(-pi2 / 12.0, 0.0)) (li2 -1.0 0.0)                          // Li₂(−1)
    near 1e-13 (Complex(pi2 / 4.0, -Math.PI * Math.Log 2.0)) (li2 2.0 0.0)         // Li₂(2), разрез «снизу»
    near 1e-13 (Complex(pi2 / 12.0 - Math.Log 2.0 ** 2.0 / 2.0, 0.0)) (li2 0.5 0.0) // Li₂(1/2)
    near 1e-13 (Complex(pi2 / 6.0, 0.0)) (li2 1.0 0.0)
    // Li₂(e^{iπ/3}): Re = π²/36, Im = Cl₂(π/3) = 1,0149416064096536…
    near 1e-13 (Complex(pi2 / 36.0, 1.0149416064096536)) (li2 0.5 (Math.Sqrt 3.0 / 2.0))
    // Li₂((1+i)/2): Re = 5π²/96 − ln²2/8, Im = G − π·ln2/8
    near 1e-13 (Complex(5.0 * pi2 / 96.0 - Math.Log 2.0 ** 2.0 / 8.0, catalan - Math.PI * Math.Log 2.0 / 8.0)) (li2 0.5 0.5)

[<Fact>]
let ``PERF.F1: Li₂ — отражение Эйлера, Li₂(z) + Li₂(−z) = ½Li₂(z²)`` () =
    for (x, y) in [ (0.3, 0.4); (-0.7, 0.2); (0.9, -0.3); (1.5, 2.0); (-3.0, -1.0) ] do
        let z = Complex(x, y)
        near 1e-12 (0.5 * SolveNum.li2Complex (z * z)) (SolveNum.li2Complex z + SolveNum.li2Complex (-z))

[<Fact>]
let ``PERF.F1: Li₂ — eval-num и builtin li2-complex`` () =
    Assert.Equal("(2.4674011002723395 . -2.177586090303602)", Printer.prettyPrint (evalStr "(li2-complex 2 0)"))
    Assert.Equal("(2.4674011002723395 . -2.177586090303602)", Printer.prettyPrint (evalStr "(polylog2-cx 2 0)"))
    // eval-num: комплексный аргумент и вещественный z > 1
    let v = evalStr "(eval-num '(polylog 2 (* 2 %i)))"
    Assert.Contains("%i", Printer.prettyPrint v)
    let w = evalStr "(eval-num '(polylog 2 2))"
    Assert.Contains("%i", Printer.prettyPrint w)
