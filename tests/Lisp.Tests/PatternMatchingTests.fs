// Тесты паттерн-матчинга и rewrite rules (PatternMatching.fs + Simplify.fs)
module PatternMatchingTests

open System.Numerics
open Xunit
open Types
open Reader
open Numeric
open PatternMatching
open Simplify
open Order
open Expand
open Factor
open Evaluator
open Printer

// Вспомогательные
let isInt (expected: BigInteger) (v: LispValue) =
    match v with
    | LispInteger n -> Assert.Equal(expected, n)
    | other -> Assert.Fail($"Ожидался LispInteger {expected}, получено {other}")

let isBool (expected: bool) (v: LispValue) =
    match v with
    | LispBool b -> Assert.Equal(expected, b)
    | other -> Assert.Fail($"Ожидался LispBool {expected}, получено {other}")

let isSym (expected: string) (v: LispValue) =
    match v with
    | LispSym s -> Assert.Equal(expected, s)
    | other -> Assert.Fail($"Ожидался LispSym {expected}, получено {other}")

// Проверка: (* n sym) где n = expected, sym = expectedSym
let isCoeffTimes (coeff: BigInteger) (sym: string) (v: LispValue) =
    match v with
    | LispList [LispSym "*"; LispInteger n; LispSym s] ->
        Assert.Equal(coeff, n); Assert.Equal(sym, s)
    | other -> Assert.Fail($"Ожидался (* {coeff} {sym}), получено {other}")

let parse (s: string) : LispValue = readAll s |> List.head

// --- Паттерн-матчинг: базовые тесты ---

[<Fact>]
let ``?x связывается с символом`` () =
    let pattern = parse "(+ ?x 0)"
    let expr = parse "(+ y 0)"
    match matchPattern pattern expr noBindings with
    | Some b ->
        match Map.tryFind "?x" b with
        | Some (LispSym s) -> Assert.Equal("y", s)
        | other -> Assert.Fail($"?x = {other}")
    | None -> Assert.Fail("Паттерн должен совпасть")

[<Fact>]
let ``?x связывается с числом`` () =
    let pattern = parse "(+ ?x 0)"
    let expr = parse "(+ 42 0)"
    match matchPattern pattern expr noBindings with
    | Some b ->
        match Map.tryFind "?x" b with
        | Some (LispInteger n) -> Assert.Equal(42I, n)
        | other -> Assert.Fail($"?x = {other}")
    | None -> Assert.Fail("Паттерн должен совпасть")

[<Fact>]
let ``Литералы не совпадают с разными значениями`` () =
    let pattern = parse "(+ ?x 1)"
    let expr = parse "(+ y 2)"
    match matchPattern pattern expr noBindings with
    | Some _ -> Assert.Fail("Паттерн не должен совпасть: 1 ≠ 2")
    | None -> ()

[<Fact>]
let ``Переменная дважды — проверка консистентности`` () =
    let pattern = parse "(+ ?x ?x)"
    match matchPattern pattern (parse "(+ y y)") noBindings with
    | Some b ->
        match Map.tryFind "?x" b with
        | Some (LispSym s) -> Assert.Equal("y", s)
        | other -> Assert.Fail($"?x = {other}")
    | None -> Assert.Fail("Должно совпасть: (+ y y)")
    match matchPattern pattern (parse "(+ y z)") noBindings with
    | Some _ -> Assert.Fail("Не должно совпасть: y ≠ z")
    | None -> ()

[<Fact>]
let ``Подстановка переменных`` () =
    let bindings = Map.ofList [("?x", LispSym "y"); ("?y", parse "(* 2 z)")]
    let template = parse "(+ ?x ?y)"
    let result = substitute bindings template
    // Ожидаем: (+ y (* 2 z))
    match result with
    | LispList [LispSym "+"; LispSym "y"; inner] ->
        match inner with
        | LispList [LispSym "*"; LispInteger n; LispSym "z"] -> Assert.Equal(2I, n)
        | other -> Assert.Fail($"Внутренний терм: {other}")
    | other -> Assert.Fail($"Результат: {other}")

[<Fact>]
let ``applyRule: (+ ?x 0) → ?x`` () =
    let pattern = parse "(+ ?x 0)"
    let replacement = parse "?x"
    let expr = parse "(+ y 0)"
    match applyRule pattern replacement expr with
    | Some (LispSym "y") -> ()
    | other -> Assert.Fail($"Результат: {other}")

[<Fact>]
let ``applyRule не совпадает → None`` () =
    let pattern = parse "(+ ?x 0)"
    let replacement = parse "?x"
    let expr = parse "(* y 0)"
    match applyRule pattern replacement expr with
    | Some _ -> Assert.Fail("Не должно совпасть")
    | None -> ()

// --- Упрощение: сбор подобных ---

[<Fact>]
let ``simplify: (+ x x) → (* 2 x)`` () =
    parse "(+ x x)" |> simplify |> isCoeffTimes 2I "x"

[<Fact>]
let ``simplify: (+ (* 2 x) (* 3 x)) → (* 5 x)`` () =
    parse "(+ (* 2 x) (* 3 x))" |> simplify |> isCoeffTimes 5I "x"

[<Fact>]
let ``simplify: (+ x x x) → (* 3 x)`` () =
    parse "(+ x x x)" |> simplify |> isCoeffTimes 3I "x"

[<Fact>]
let ``simplify: (+ (* 2 x) x) → (* 3 x)`` () =
    parse "(+ (* 2 x) x)" |> simplify |> isCoeffTimes 3I "x"

[<Fact>]
let ``simplify: (+ x y x) → (+ (* 2 x) y)`` () =
    let result = parse "(+ x y x)" |> simplify
    // Проверяем наличие (* 2 x) и y в сумме
    match result with
    | LispList [LispSym "+"; t1; t2] ->
        let has2x = structEqual t1 (LispList [LispSym "*"; LispInteger 2I; LispSym "x"]) || structEqual t2 (LispList [LispSym "*"; LispInteger 2I; LispSym "x"])
        let hasY = structEqual t1 (LispSym "y") || structEqual t2 (LispSym "y")
        Assert.True(has2x, $"Ожидался (* 2 x) в результате: {result}")
        Assert.True(hasY, $"Ожидался y в результате: {result}")
    | other -> Assert.Fail($"Ожидался (+ (* 2 x) y), получено {other}")

[<Fact>]
let ``simplify: (- x x) → 0`` () =
    parse "(- x x)" |> simplify |> isInt 0I

// --- Раскрытие скобок (expand) ---

[<Fact>]
let ``expand: (* a (+ b c)) → (+ (* a b) (* a c))`` () =
    let result = parse "(* a (+ b c))" |> expand
    match result with
    | LispList [LispSym "+"; t1; t2] ->
        Assert.True(structEqual t1 (LispList [LispSym "*"; LispSym "a"; LispSym "b"]) || structEqual t2 (LispList [LispSym "*"; LispSym "a"; LispSym "b"]))
        Assert.True(structEqual t1 (LispList [LispSym "*"; LispSym "a"; LispSym "c"]) || structEqual t2 (LispList [LispSym "*"; LispSym "a"; LispSym "c"]))
    | other -> Assert.Fail($"Результат: {other}")

[<Fact>]
let ``expand: (* (+ a b) (+ c d)) → 4 члена`` () =
    let result = parse "(* (+ a b) (+ c d))" |> expand
    match result with
    | LispList [LispSym "+"; a; b; c; d] ->
        let all = [a; b; c; d] |> List.map prettyPrint
        Assert.Contains("(* a c)", all)
        Assert.Contains("(* a d)", all)
        Assert.Contains("(* b c)", all)
        Assert.Contains("(* b d)", all)
    | other -> Assert.Fail($"Результат: {other}")

[<Fact>]
let ``expand: (* 2 (+ x y)) → (+ (* 2 x) (* 2 y))`` () =
    let result = parse "(* 2 (+ x y))" |> expand
    match result with
    | LispList [LispSym "+"; t1; t2] ->
        let has2x = structEqual t1 (LispList [LispSym "*"; LispInteger 2I; LispSym "x"]) || structEqual t2 (LispList [LispSym "*"; LispInteger 2I; LispSym "x"])
        let has2y = structEqual t1 (LispList [LispSym "*"; LispInteger 2I; LispSym "y"]) || structEqual t2 (LispList [LispSym "*"; LispInteger 2I; LispSym "y"])
        Assert.True(has2x, $"Ожидался (* 2 x): {result}")
        Assert.True(has2y, $"Ожидался (* 2 y): {result}")
    | other -> Assert.Fail($"Результат: {other}")

// --- match и rewrite из REPL ---

[<Fact>]
let ``match из REPL: (+ ?x 0) vs (+ y 0) → #t`` () =
    parse "(match '(+ ?x 0) '(+ y 0))" |> fun e -> eval e globalEnv |> isBool true

[<Fact>]
let ``match из REPL: несовпадение → #f`` () =
    parse "(match '(+ ?x 0) '(* y 0))" |> fun e -> eval e globalEnv |> isBool false

[<Fact>]
let ``rewrite из REPL: (+ ?x 0) → ?x, expr (+ y 0) → y`` () =
    parse "(rewrite '(+ ?x 0) '?x '(+ y 0))" |> fun e -> eval e globalEnv |> isSym "y"

[<Fact>]
let ``expand из REPL: (* a (+ b c)) → (+ (* a b) (* a c))`` () =
    let result = parse "(expand '(* a (+ b c)))" |> fun e -> eval e globalEnv
    match result with
    | LispList [LispSym "+"; _; _] -> ()
    | other -> Assert.Fail($"Результат: {other}")

// --- Усиленное simplify + diff ---

[<Fact>]
let ``simplify + diff: d/dx(x^2) → (* 2 x)`` () =
    parse "(^ x 2)" |> Differentiate.diff "x" |> simplify |> isCoeffTimes 2I "x"

[<Fact>]
let ``simplify + diff: d/dx(x*x) → (* 2 x)`` () =
    parse "(* x x)" |> Differentiate.diff "x" |> simplify |> isCoeffTimes 2I "x"

[<Fact>]
let ``simplify + diff: d/dx(+ x x) → 2`` () =
    parse "(+ x x)" |> Differentiate.diff "x" |> simplify |> isInt 2I
