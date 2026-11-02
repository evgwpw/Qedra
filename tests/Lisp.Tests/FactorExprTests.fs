// Тесты factor / sqfree над выражениями Lisp (Factor.fs, Lisp.Core; Шаг 17, коммит 2).
// Шаг 21h': случайные многомерные произведения над MPoly (factorPoly) — в Cas.Algebra.Tests (PolyFactorTests.fs)
module FactorExprTests

open System
open System.Diagnostics
open System.Numerics
open Xunit
open Types
open Reader
open Printer

let parse (s: string) : LispValue = readAll s |> List.head
let factorStr (s: string) : string = prettyPrint (Factor.factorExpr (parse s))
let expandStr (v: LispValue) : string = prettyPrint (Expand.expand v)

// Инвариант: expand(factor(p)) = expand(p); возвращает результат factor
let checkFactor (s: string) : LispValue =
    let p = parse s
    let f = Factor.factorExpr p
    Assert.Equal(expandStr p, expandStr f)
    f

// Число неприводимых множителей (с учётом кратности не считаем): аргументы верхнего `*`, не числа
let factorCount (v: LispValue) : int =
    match v with
    | LispList (LispSym "*" :: args) -> args |> List.filter (fun a -> not (Numeric.isNumber a)) |> List.length
    | LispList (LispSym "+" :: _) -> 1
    | _ -> 1

[<Fact>]
let ``factor: x^2-1`` () =
    Assert.Equal("(* (+ -1 x) (+ 1 x))", prettyPrint (checkFactor "(- (^ x 2) 1)"))

[<Fact>]
let ``factor: x^4-1 над Z`` () =
    Assert.Equal("(* (+ -1 x) (+ 1 x) (+ 1 (^ x 2)))", prettyPrint (checkFactor "(- (^ x 4) 1)"))

[<Fact>]
let ``factor: x^20-1 — циклотомические множители`` () =
    let f = checkFactor "(- (^ x 20) 1)"
    Assert.Equal(6, factorCount f)
    let s = prettyPrint f
    Assert.Contains("(+ 1 x (^ x 2) (^ x 3) (^ x 4))", s)
    Assert.Contains("(+ 1 (* -1 (^ x 2)) (^ x 4) (* -1 (^ x 6)) (^ x 8))", s)

[<Fact>]
let ``factor: 2x^2+4x+2 -> 2(x+1)^2`` () =
    Assert.Equal("(* 2 (^ (+ 1 x) 2))", prettyPrint (checkFactor "(+ (* 2 (^ x 2)) (* 4 x) 2)"))

[<Fact>]
let ``factor: x^4+4 = (x^2-2x+2)(x^2+2x+2)`` () =
    Assert.Equal("(* (+ 2 (* -2 x) (^ x 2)) (+ 2 (* 2 x) (^ x 2)))", prettyPrint (checkFactor "(+ (^ x 4) 4)"))

[<Fact>]
let ``factor: Свиннертон-Дайер x^4-10x^2+1 неприводим`` () =
    Assert.Equal("(+ 1 (* -10 (^ x 2)) (^ x 4))", prettyPrint (checkFactor "(+ (^ x 4) (* -10 (^ x 2)) 1)"))

[<Fact>]
let ``factor: Свиннертон-Дайер степени 8 неприводим`` () =
    // x^8 - 40x^6 + 352x^4 - 960x^2 + 576 — минимальный многочлен √2+√3+√5, неприводим
    let s = "(+ (^ x 8) (* -40 (^ x 6)) (* 352 (^ x 4)) (* -960 (^ x 2)) 576)"
    Assert.Equal(1, factorCount (checkFactor s))

[<Fact>]
let ``factor: степень 12 с известными множителями`` () =
    let parts = [ "(+ (^ x 2) 1)"; "(+ (^ x 3) (* -1 x) -1)"; "(+ (^ x 3) x 1)"; "(+ (^ x 4) x 1)" ]
    let prod = parse ("(* " + String.Join(" ", parts) + ")")
    let expanded = Expand.expand prod
    let f = Factor.factorExpr expanded
    Assert.Equal(prettyPrint (Simplify.simplify prod), prettyPrint f)

[<Fact>]
let ``factor: кратные множители`` () =
    Assert.Equal("(* (^ (+ -1 x) 3) (^ (+ 1 x) 2) (+ 2 x))",
                 prettyPrint (checkFactor "(* (^ (- x 1) 3) (^ (+ x 1) 2) (+ x 2))" |> fun _ ->
                     Factor.factorExpr (Expand.expand (parse "(* (^ (- x 1) 3) (^ (+ x 1) 2) (+ x 2))"))))

[<Fact>]
let ``factor: рациональные коэффициенты и знак`` () =
    Assert.Equal("(* 1/2 (+ -1 x) (+ 1 x))", prettyPrint (checkFactor "(+ (* 1/2 (^ x 2)) -1/2)"))
    Assert.Equal("(* -1 (+ -1 x) (+ 1 x))", prettyPrint (checkFactor "(- 1 (^ x 2))"))

[<Fact>]
let ``factor: линейные множители с рациональными корнями`` () =
    Assert.Equal("(* (+ -1 (* 2 x)) (+ 1 (* 3 x)))", prettyPrint (checkFactor "(+ -1 (* -1 x) (* 6 (^ x 2)))"))

// --- многомерные ---

[<Fact>]
let ``factor: x^2-y^2`` () =
    Assert.Equal("(* (+ x y) (+ x (* -1 y)))", prettyPrint (checkFactor "(- (^ x 2) (^ y 2))"))

[<Fact>]
let ``factor: x^2 y + x y^2`` () =
    Assert.Equal("(* x y (+ x y))", prettyPrint (checkFactor "(+ (* (^ x 2) y) (* x (^ y 2)))"))

[<Fact>]
let ``factor: (x+y)^3 после expand`` () =
    Assert.Equal("(^ (+ x y) 3)", prettyPrint (Factor.factorExpr (Expand.expand (parse "(^ (+ x y) 3)"))))

[<Fact>]
let ``factor: однородные двумерные`` () =
    // x^4 - y^4 = (x-y)(x+y)(x^2+y^2)
    let f = checkFactor "(- (^ x 4) (^ y 4))"
    Assert.Equal(3, factorCount f)
    // x^3 + y^3 = (x+y)(x^2 - xy + y^2)
    Assert.Equal(2, factorCount (checkFactor "(+ (^ x 3) (^ y 3))"))

[<Fact>]
let ``factor: содержание по переменной`` () =
    // (y+1)(x^2 - 1) = ... содержание по x
    let p = Expand.expand (parse "(* (+ y 1) (- (^ x 2) 1))")
    let f = Factor.factorExpr p
    Assert.Equal(3, factorCount f)
    Assert.Equal(expandStr p, expandStr f)

[<Fact>]
let ``factor: неоднородный многомерный раскладывается (Шаг 21e)`` () =
    // x^2 + x - y^2 - y = (x - y)(x + y + 1) — раньше (до шага 21e) оставался как есть
    let s = "(+ (^ x 2) x (* -1 (^ y 2)) (* -1 y))"
    let f = checkFactor s
    Assert.Equal(2, factorCount f)

// --- рациональные функции и ядра ---

[<Fact>]
let ``factor: рациональная функция (x^2-1)/(x^2+2x+1) -> (x-1)/(x+1)`` () =
    let f = Factor.factorExpr (parse "(/ (- (^ x 2) 1) (+ (^ x 2) (* 2 x) 1))")
    Assert.Equal("(* (+ -1 x) (^ (+ 1 x) -1))", prettyPrint f)

[<Fact>]
let ``factor: ядра — sin^2 - 4`` () =
    // sin^2 - 1 simplify сворачивает по Пифагору в -cos^2 ещё до разложения
    Assert.Equal("(* (+ -2 (sin x)) (+ 2 (sin x)))", prettyPrint (checkFactor "(+ (^ (sin x) 2) -4)"))
    Assert.Equal("(* (+ -1 (exp x)) (+ 1 (exp x)))", prettyPrint (checkFactor "(+ (^ (exp x) 2) -1)"))
    Assert.Equal("(* -1 (^ (cos x) 2))", prettyPrint (checkFactor "(+ (^ (sin x) 2) -1)"))

[<Fact>]
let ``factor: константы и нуль`` () =
    Assert.Equal("5", factorStr "5")
    Assert.Equal("0", factorStr "0")
    Assert.Equal("1/3", factorStr "(/ 1 3)")
    Assert.Equal("x", factorStr "x")

[<Fact>]
let ``factor: неприводимые остаются`` () =
    Assert.Equal("(+ 1 x)", factorStr "(+ x 1)")
    Assert.Equal("(+ 1 (^ x 2))", factorStr "(+ (^ x 2) 1)")

// --- sqfree ---

[<Fact>]
let ``sqfree: бесквадратное разложение`` () =
    let e = Expand.expand (parse "(* (^ (+ x 1) 3) (^ (- x 2) 2) (+ x 3))")
    let s = Factor.sqfreeExpr e
    Assert.Equal(expandStr e, expandStr s)
    Assert.Equal("(* (^ (+ -2 x) 2) (^ (+ 1 x) 3) (+ 3 x))", prettyPrint s)

// --- случайные произведения: инвариант и идемпотентность ---

[<Fact>]
let ``factor: случайные произведения (seed)`` () =
    let rnd = Random 4242
    let randPoly () =
        let deg = rnd.Next(1, 4)
        let terms = [ for i in 0 .. deg -> sprintf "(* %d (^ x %d))" (let c = rnd.Next(-4, 5) in if i = deg && c = 0 then 1 else c) i ]
        "(+ " + String.Join(" ", terms) + ")"
    for _ in 1 .. 20 do
        let p = Expand.expand (parse (sprintf "(* %s %s %s)" (randPoly ()) (randPoly ()) (randPoly ())))
        let f = Factor.factorExpr p
        Assert.Equal(expandStr p, expandStr f)
        // factor идемпотентен
        Assert.Equal(prettyPrint f, prettyPrint (Factor.factorExpr f))
        // неприводимых множителей (с кратностью) не меньше, чем перемножено нетривиальных многочленов
        let ctx = PolyExpr.makeCtx [p] []
        let (_, fs) = PolyFactor.factorPoly (PolyExpr.toPoly ctx p).Value
        Assert.True((fs |> List.sumBy snd) >= 3)

[<Fact>]
let ``factor: случайные произведения из пяти многочленов`` () =
    let rnd = Random 99
    let randPoly () =
        let deg = rnd.Next(1, 4)
        let terms = [ for i in 0 .. deg -> sprintf "(* %d (^ x %d))" (let c = rnd.Next(-6, 7) in if i = deg && c = 0 then 2 else c) i ]
        "(+ " + String.Join(" ", terms) + ")"
    for _ in 1 .. 8 do
        let p = Expand.expand (parse (sprintf "(* %s %s %s %s %s)" (randPoly ()) (randPoly ()) (randPoly ()) (randPoly ()) (randPoly ())))
        let f = Factor.factorExpr p
        Assert.Equal(expandStr p, expandStr f)
        let ctx = PolyExpr.makeCtx [p] []
        let (_, fs) = PolyFactor.factorPoly (PolyExpr.toPoly ctx p).Value
        Assert.True((fs |> List.sumBy snd) >= 5)

// --- многомерное разложение (Шаг 21e) ---

[<Fact>]
let ``factor многомерный: обязательные примеры`` () =
    let cases =
        [ "(- (^ x 2) (^ y 2))", 2
          "(- (* (^ x 2) (^ y 2)) 1)", 2
          "(- (^ x 3) (^ y 3))", 2
          "(- (^ x 4) (^ y 4))", 3
          "(- (+ (^ x 2) (* 2 x y) (^ y 2)) (^ z 2))", 2
          "(+ (* x y) x y 1)", 2 ]
    for (s, n) in cases do
        let f = checkFactor s
        Assert.Equal(n, factorCount f)

[<Fact>]
let ``factor многомерный: произведения и неприводимые`` () =
    let prod (s: string) = Expand.expand (parse s)
    let check (s: string) (n: int) =
        let p = prod s
        let f = Factor.factorExpr p
        Assert.Equal(expandStr p, expandStr f)
        Assert.Equal(n, factorCount f)
    check "(* (+ (^ x 2) y 1) (+ x (^ y 2) 2))" 2
    check "(* (+ (* x y) z) (+ x (* y z)) (+ x (* -1 y) 1))" 3
    check "(+ (* (^ x 2) y) (* x (^ y 2)) x y)" 2
    check "(* (^ (+ x y) 2) (- x y))" 2
    // неприводимые остаются как есть
    for s in [ "(+ (^ x 2) (^ y 2))"; "(+ (^ x 2) (^ y 2) (^ z 2))"; "(+ (^ x 3) (^ y 2) 1)" ] do
        let p = parse s
        Assert.Equal(prettyPrint (Simplify.simplify p), prettyPrint (Factor.factorExpr p))

// --- время ---

[<Fact>]
let ``время: x^20-1 и Свиннертон-Дайер быстрее секунды`` () =
    Factor.factorExpr (parse "(- (^ x 6) 1)") |> ignore
    let sw = Stopwatch.StartNew()
    Factor.factorExpr (parse "(- (^ x 20) 1)") |> ignore
    let t1 = sw.ElapsedMilliseconds
    sw.Restart()
    Factor.factorExpr (parse "(+ (^ x 4) (* -10 (^ x 2)) 1)") |> ignore
    Factor.factorExpr (parse "(+ (^ x 8) (* -40 (^ x 6)) (* 352 (^ x 4)) (* -960 (^ x 2)) 576)") |> ignore
    let t2 = sw.ElapsedMilliseconds
    Assert.True(t1 < 1000L, sprintf "x^20-1: %d мс" t1)
    Assert.True(t2 < 1000L, sprintf "Свиннертон-Дайер: %d мс" t2)
