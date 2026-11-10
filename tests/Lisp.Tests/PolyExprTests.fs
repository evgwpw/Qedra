// Тесты моста «выражение Lisp ↔ многочлен» (PolyExpr.fs, Lisp.Core; Шаг 17, коммит 1): арифметика, преобразования, ядра,
// рациональные функции. Шаг 21h': точное деление, псевдоделение и НОД (чистая алгебра) — в Cas.Algebra.Tests (MPolyTests.fs)
module PolyExprTests

open System
open System.Numerics
open Xunit
open Types
open Reader
open Printer
open MPoly
open PolyExpr

let parse (s: string) : LispValue = readAll s |> List.head
let ctxOfSrc (srcs: string list) = makeCtx (srcs |> List.map parse) []
let poly (ctx: Ctx) (s: string) : MPoly =
    match toPoly ctx (parse s) with
    | Some p -> p
    | None -> failwithf "не многочлен: %s" s
let show (ctx: Ctx) (p: MPoly) = prettyPrint (toExpr ctx p)
let canon (s: string) = prettyPrint (Expand.expand (parse s))

// --- арифметика ---

[<Fact>]
let ``арифметика: (x+1)(x-1) = x^2-1`` () =
    let ctx = ctxOfSrc ["(+ x 1)"; "(- x 1)"]
    let p = mul (poly ctx "(+ x 1)") (poly ctx "(- x 1)")
    Assert.Equal("(+ -1 (^ x 2))", show ctx p)

[<Fact>]
let ``арифметика: сложение, вычитание, степень`` () =
    let ctx = ctxOfSrc ["(+ x y)"]
    let s = poly ctx "(+ x y)"
    Assert.Equal(canon "(^ (+ x y) 5)", show ctx (pow s 5))
    Assert.Equal("0", show ctx (sub s s))
    Assert.Equal("(* 2 x)", show ctx (add s (sub (poly ctx "x") (poly ctx "y"))))

[<Fact>]
let ``арифметика: рациональные коэффициенты`` () =
    let ctx = ctxOfSrc ["(+ (* 1/2 x) 1/3)"]
    let p = poly ctx "(+ (* 1/2 x) 1/3)"
    Assert.Equal(canon "(+ (* 1/4 (^ x 2)) (* 1/3 x) 1/9)", show ctx (mul p p))

[<Fact>]
let ``производная, степень, коэффициент, подстановка`` () =
    let ctx = ctxOfSrc ["(+ (* x x y) (* 3 x) (^ y 3))"]
    let p = poly ctx "(+ (* x x y) (* 3 x) (^ y 3))"
    let x, y = varIndex ctx (LispSym "x"), varIndex ctx (LispSym "y")
    Assert.Equal(2, degIn x p)
    Assert.Equal(3, degIn y p)
    Assert.Equal("(+ 3 (* 2 x y))", show ctx (deriv x p))
    Assert.Equal(canon "(+ (* 3 (^ y 2)) (^ x 2))", show ctx (deriv y p))
    Assert.Equal("3", show ctx (coeffIn x 1 p))
    Assert.Equal("(* 3 x)", show ctx (coeffIn y 0 p))
    Assert.Equal("y", show ctx (coeffIn x 2 p))
    // подстановка x = 2: 4y + 6 + y^3
    Assert.Equal(canon "(+ (* 4 y) 6 (^ y 3))", show ctx (subst x (ofInt 2I) p))
    // подстановка x = y + 1
    let q = subst x (add (var y) one) p
    Assert.Equal(canon "(+ (* (+ y 1) (+ y 1) y) (* 3 (+ y 1)) (^ y 3))", show ctx q)

// --- преобразования ---

let roundTrip = [
    "(+ (* 3 (^ x 2)) (* 2 x y) 5)"
    "(* (+ x 1) (+ x 2) (+ y 3))"
    "(^ (+ x y z) 4)"
    "(+ (* 1/2 x) (* 1/3 y))"
    "(- (^ x 3) (* 2 x) 7)"
    "(* 7 (^ a 2) (^ b 3))"
]

[<Fact>]
let ``выражение -> многочлен -> выражение = expand`` () =
    for s in roundTrip do
        let ctx = ctxOfSrc [s]
        let back = toExpr ctx (poly ctx s)
        Assert.Equal(canon s, prettyPrint back)

[<Fact>]
let ``toExpr — неподвижная точка simplify`` () =
    for s in roundTrip do
        let ctx = ctxOfSrc [s]
        let e = toExpr ctx (poly ctx s)
        Assert.Equal(prettyPrint e, prettyPrint (Simplify.simplify e))

// --- ядра ---

[<Fact>]
let ``ядра: (+ (sin x) (* 2 (sin x))) — одна переменная`` () =
    let e = parse "(+ (sin x) (* 2 (sin x)))"
    let ctx = makeCtx [e] []
    Assert.Equal(1, ctx.Vars.Length)
    Assert.Equal("(sin x)", prettyPrint ctx.Vars.[0])
    Assert.Equal("(* 3 (sin x))", show ctx (poly ctx "(+ (sin x) (* 2 (sin x)))"))

[<Fact>]
let ``ядра: символы, корни, логарифмы, float`` () =
    let ctx = ctxOfSrc ["(+ x (^ x 1/2) (sqrt 2) (log y) 0.5 (sin x))"]
    // x, (^ x 1/2), (sqrt 2), (log y), 0.5, (sin x)
    Assert.Equal(6, ctx.Vars.Length)
    let p = poly ctx "(* (+ x (sqrt 2)) (+ x (sqrt 2)))"
    Assert.Equal(canon "(* (+ x (sqrt 2)) (+ x (sqrt 2)))", show ctx p)

[<Fact>]
let ``ядра: структурно равные — одна переменная при разных порядках`` () =
    let ctx = ctxOfSrc ["(* (sin (+ x y)) (sin (+ y x)))"]
    Assert.Equal(1, (ctx.Vars |> Array.filter (fun v -> prettyPrint v <> "x")).Length)

// --- рациональные функции ---

[<Fact>]
let ``рациональная функция: сокращение`` () =
    let e = parse "(/ (- (^ x 2) 1) (+ x 1))"
    let ctx = makeCtx [e] []
    let (n, d) = toRatFun ctx e
    Assert.Equal("(+ -1 x)", prettyPrint (toExpr ctx n))
    Assert.True(isOne d)

[<Fact>]
let ``рациональная функция: знаменатель остаётся`` () =
    let e = parse "(+ (/ 1 x) (/ 1 y))"
    let ctx = makeCtx [e] []
    let (n, d) = toRatFun ctx e
    Assert.Equal("(+ x y)", prettyPrint (toExpr ctx n))
    Assert.Equal("(* x y)", prettyPrint (toExpr ctx d))
    Assert.True((toPoly ctx e).IsNone)

[<Fact>]
let ``рациональная функция: целая отрицательная степень суммы`` () =
    let e = parse "(* (+ x 1) (^ (+ x 1) -3))"
    let ctx = makeCtx [e] []
    let (n, d) = toRatFun ctx e
    Assert.True(isOne n)
    Assert.Equal(canon "(^ (+ x 1) 2)", prettyPrint (toExpr ctx d))
