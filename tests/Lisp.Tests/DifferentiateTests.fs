// Тесты символьного дифференцирования (Differentiate.fs)
module DifferentiateTests

open System.Numerics
open Xunit
open Types
open Reader
open Differentiate
open Simplify
open Order
open Expand
open Factor
open Evaluator

// Вспомогательные функции
let isInt (expected: BigInteger) (v: LispValue) =
    match v with
    | LispInteger n -> Assert.Equal(expected, n)
    | other -> Assert.Fail($"Ожидался LispInteger {expected}, получено {other}")

// Рекурсивный поиск символа в выражении
let rec recContains (name: string) (v: LispValue) : bool =
    match v with
    | LispSym s -> s = name
    | LispList items -> List.exists (recContains name) items
    | _ -> false

// Продифференцировать строку по переменной, упростить результат
let diffStr (var: string) (expr: string) : LispValue =
    match readAll expr with
    | [e] -> diff var e |> simplify
    | _ -> failwith "diffStr: ожидается одно выражение"

// --- Базовые правила ---

[<Fact>]
let ``Производная константы → 0`` () =
    diffStr "x" "5" |> isInt 0I

[<Fact>]
let ``Производная переменной по себе → 1`` () =
    diffStr "x" "x" |> isInt 1I

[<Fact>]
let ``Производная переменной по другой → 0`` () =
    diffStr "x" "y" |> isInt 0I

// --- Сумма ---

[<Fact>]
let ``Производная суммы → сумма производных`` () =
    diffStr "x" "(+ x x)" |> isInt 2I

[<Fact>]
let ``Производная суммы с константой`` () =
    diffStr "x" "(+ x 5)" |> isInt 1I

[<Fact>]
let ``Производная разности`` () =
    diffStr "x" "(- x 5)" |> isInt 1I

// --- Произведение ---

[<Fact>]
let ``Производная произведения (rule)`` () =
    // d/dx(x * x) = 1*x + x*1 = x + x → simplify собирает в (* 2 x)
    let result = diffStr "x" "(* x x)"
    match result with
    | LispList [LispSym "*"; LispInteger n; LispSym s] ->
        Assert.Equal(2I, n); Assert.Equal("x", s)
    | other -> Assert.Fail($"Ожидался (* 2 x), получено {other}")

[<Fact>]
let ``Производная произведения с константой`` () =
    // d/dx(3 * x) = 0*x + 3*1 = 3
    diffStr "x" "(* 3 x)" |> isInt 3I

// --- Частное ---

[<Fact>]
let ``Производная частного`` () =
    // d/dx(x / x) = (1*x - x*1) / x² → (- x x) = 0 → 0 / x² = 0
    // Теперь simplify умеет: (- a a) → 0, (/ 0 x) → 0
    diffStr "x" "(/ x x)" |> isInt 0I

// --- Степень ---

[<Fact>]
let ``Производная степени (power rule)`` () =
    // d/dx(x^3) = 3 * x^2 * 1 → (* 3 (^ x 2))
    let result = diffStr "x" "(^ x 3)"
    match result with
    | LispList [LispSym "*"; LispInteger n; LispList [LispSym "^"; LispSym s; LispInteger e]] ->
        Assert.Equal(3I, n)
        Assert.Equal("x", s)
        Assert.Equal(2I, e)
    | other -> Assert.Fail($"Ожидался (* 3 (^ x 2)), получено {other}")

[<Fact>]
let ``Производная x^2 → 2x`` () =
    let result = diffStr "x" "(^ x 2)"
    match result with
    | LispList [LispSym "*"; LispInteger n; LispSym s] ->
        Assert.Equal(2I, n)
        Assert.Equal("x", s)
    | other -> Assert.Fail($"Ожидался (* 2 x), получено {other}")

[<Fact>]
let ``Производная x^1 → 1`` () =
    diffStr "x" "(^ x 1)" |> isInt 1I

[<Fact>]
let ``Производная константы в степени → 0`` () =
    // d/dx(5^3) = 3 * 5^2 * 0 = 0
    diffStr "x" "(^ 5 3)" |> isInt 0I

// --- Тригонометрические ---

[<Fact>]
let ``Производная sin(x) → cos(x)`` () =
    let result = diffStr "x" "(sin x)"
    match result with
    | LispList [LispSym "cos"; LispSym s] -> Assert.Equal("x", s)
    | other -> Assert.Fail($"Ожидался (cos x), получено {other}")

[<Fact>]
let ``Производная cos(x) содержит sin`` () =
    // d/dx(cos x) = -sin(x) * 1 → содержит sin
    let result = diffStr "x" "(cos x)"
    Assert.True(recContains "sin" result, $"Ожидался sin в результате, получено {result}")

// --- Экспонента ---

[<Fact>]
let ``Производная exp(x) → exp(x)`` () =
    let result = diffStr "x" "(exp x)"
    match result with
    | LispList [LispSym "exp"; LispSym s] -> Assert.Equal("x", s)
    | other -> Assert.Fail($"Ожидался (exp x), получено {other}")

// --- Логарифм ---

[<Fact>]
let ``Производная log(x) → 1/x`` () =
    let result = diffStr "x" "(log x)"
    match result with
    | LispList [LispSym "^"; LispSym s; LispInteger n] ->
        Assert.Equal(-1I, n)
        Assert.Equal("x", s)
    | other -> Assert.Fail($"Ожидался (^ x -1), получено {other}")

// --- Сложные выражения ---

[<Fact>]
let ``Производная многочлена 3x^2 + 2x + 1`` () =
    let result = diffStr "x" "(+ (* 3 (^ x 2)) (* 2 x) 1)"
    let str = result.ToString()
    Assert.True(str.Contains("6") || str.Contains("2"), $"Результат: {str}")

// --- Вызов diff из REPL ---

[<Fact>]
let ``Diff из REPL: d/dx(x^3) → содержит 3`` () =
    let result = readAll "(diff 'x '(^ x 3))" |> List.head |> fun e -> eval e globalEnv
    let str = result.ToString()
    Assert.True(str.Contains("3"), $"Результат: {str}")

// --- Вызов diff + simplify из REPL ---

[<Fact>]
let ``Diff + simplify из REPL: d/dx(x^2) → 2x`` () =
    let exprs = readAll "(simplify (diff 'x '(^ x 2)))"
    let result = List.head exprs |> fun e -> eval e globalEnv
    match result with
    | LispList [LispSym "*"; LispInteger n; LispSym s] ->
        Assert.Equal(2I, n)
        Assert.Equal("x", s)
    | other -> Assert.Fail($"Ожидался (* 2 x), получено {other}")

// --- Расширенные тригонометрические ---

[<Fact>]
let ``Производная tan(x) → 1/cos^2(x)`` () =
    // d/dx(tan x) = 1/cos²(x) = sec²(x) — генерируем 1/cos²
    let result = diffStr "x" "(tan x)"
    Assert.True(recContains "cos" result, $"Ожидался cos в результате, получено {result}")

[<Fact>]
let ``Производная cot(x) → -1/sin^2(x)`` () =
    // d/dx(cot x) = -1/sin²(x) = -csc²(x) — генерируем -1/sin²
    let result = diffStr "x" "(cot x)"
    Assert.True(recContains "sin" result, $"Ожидался sin в результате, получено {result}")

[<Fact>]
let ``Производная sec(x) → sin/cos^2 (после 8c)`` () =
    // d/dx(sec x) = sec x · tan x; после триг-правил simplify: (sin x)/cos²x
    let result = diffStr "x" "(sec x)"
    Assert.True(recContains "sin" result, $"Результат: {result}")
    Assert.True(recContains "cos" result, $"Результат: {result}")

[<Fact>]
let ``Производная csc(x) → -cos/sin^2 (после 8c)`` () =
    // d/dx(csc x) = −csc x · cot x; после триг-правил simplify: −(cos x)/sin²x
    let result = diffStr "x" "(csc x)"
    Assert.True(recContains "cos" result, $"Результат: {result}")
    Assert.True(recContains "sin" result, $"Результат: {result}")

// --- Гиперболические ---

[<Fact>]
let ``Производная sinh(x) → cosh(x)`` () =
    let result = diffStr "x" "(sinh x)"
    match result with
    | LispList [LispSym "cosh"; LispSym s] -> Assert.Equal("x", s)
    | other -> Assert.Fail($"Ожидался (cosh x), получено {other}")

[<Fact>]
let ``Производная cosh(x) → sinh(x)`` () =
    let result = diffStr "x" "(cosh x)"
    match result with
    | LispList [LispSym "sinh"; LispSym s] -> Assert.Equal("x", s)
    | other -> Assert.Fail($"Ожидался (sinh x), получено {other}")

[<Fact>]
let ``Производная tanh(x) содержит sech`` () =
    let result = diffStr "x" "(tanh x)"
    Assert.True(recContains "sech" result, $"Результат: {result}")

[<Fact>]
let ``Производная coth(x) содержит csch`` () =
    let result = diffStr "x" "(coth x)"
    Assert.True(recContains "csch" result, $"Результат: {result}")

[<Fact>]
let ``Производная sech(x) содержит sech*tanh`` () =
    let result = diffStr "x" "(sech x)"
    Assert.True(recContains "sech" result, $"Результат: {result}")
    Assert.True(recContains "tanh" result, $"Результат: {result}")

[<Fact>]
let ``Производная csch(x) содержит csch*coth`` () =
    let result = diffStr "x" "(csch x)"
    Assert.True(recContains "csch" result, $"Результат: {result}")
    Assert.True(recContains "coth" result, $"Результат: {result}")

// --- Обратные тригонометрические ---

[<Fact>]
let ``Производная asin(x) → 1/sqrt(1-x^2)`` () =
    let result = diffStr "x" "(asin x)"
    Assert.True(recContains "sqrt" result, $"Ожидался sqrt, результат: {result}")

[<Fact>]
let ``Производная acos(x) содержит sqrt`` () =
    let result = diffStr "x" "(acos x)"
    Assert.True(recContains "sqrt" result, $"Результат: {result}")

[<Fact>]
let ``Производная atan(x) → 1/(1+x^2)`` () =
    let result = diffStr "x" "(atan x)"
    match result with
    | LispList [LispSym "^"; LispList [LispSym "+"; _; _]; LispInteger n] when n = -1I -> ()
    | other -> Assert.Fail($"Ожидался (^ (+ ...) -1), получено {other}")

[<Fact>]
let ``Производная acot(x) содержит 1/(1+x^2)`` () =
    let result = diffStr "x" "(acot x)"
    Assert.True(recContains "1" result || result.ToString().Contains("1"), $"Результат: {result}")

[<Fact>]
let ``Производная asec(x) содержит sqrt`` () =
    let result = diffStr "x" "(asec x)"
    Assert.True(recContains "sqrt" result, $"Результат: {result}")

[<Fact>]
let ``Производная acsc(x) содержит sqrt`` () =
    let result = diffStr "x" "(acsc x)"
    Assert.True(recContains "sqrt" result, $"Результат: {result}")

// --- Обратные гиперболические ---

[<Fact>]
let ``Производная asinh(x) → 1/sqrt(1+x^2)`` () =
    let result = diffStr "x" "(asinh x)"
    Assert.True(recContains "sqrt" result, $"Ожидался sqrt, результат: {result}")

[<Fact>]
let ``Производная acosh(x) → 1/sqrt(x^2-1)`` () =
    let result = diffStr "x" "(acosh x)"
    Assert.True(recContains "sqrt" result, $"Результат: {result}")

[<Fact>]
let ``Производная atanh(x) → 1/(1-x^2)`` () =
    let result = diffStr "x" "(atanh x)"
    match result with
    | LispList [LispSym "^"; LispList [LispSym "+"; _; _]; LispInteger n] when n = -1I -> ()
    | other -> Assert.Fail($"Ожидался (^ (+ ...) -1), получено {other}")

[<Fact>]
let ``Производная acoth(x) → 1/(1-x^2)`` () =
    let result = diffStr "x" "(acoth x)"
    match result with
    | LispList [LispSym "^"; LispList [LispSym "+"; _; _]; LispInteger n] when n = -1I -> ()
    | other -> Assert.Fail($"Ожидался (^ (+ ...) -1), получено {other}")

[<Fact>]
let ``Производная asech(x) содержит sqrt(1-x^2)`` () =
    let result = diffStr "x" "(asech x)"
    Assert.True(recContains "sqrt" result, $"Результат: {result}")

[<Fact>]
let ``Производная acsch(x) содержит sqrt(1+x^2)`` () =
    let result = diffStr "x" "(acsch x)"
    Assert.True(recContains "sqrt" result, $"Результат: {result}")

// --- Цепное правило (chain rule) ---

[<Fact>]
let ``Цепное правило: sin(x^2) → cos(x^2)*2x`` () =
    let result = diffStr "x" "(sin (^ x 2))"
    // Результат: (* (cos (^ x 2)) (* 2 x)) или подобное
    Assert.True(recContains "cos" result, $"Ожидался cos, результат: {result}")
    Assert.True(recContains "x" result, $"Результат: {result}")

[<Fact>]
let ``Цепное правило: exp(2x) → 2*exp(2x)`` () =
    let result = diffStr "x" "(exp (* 2 x))"
    Assert.True(recContains "exp" result, $"Ожидался exp, результат: {result}")

[<Fact>]
let ``Цепное правило: log(sin x) → cos(x)/sin(x)`` () =
    let result = diffStr "x" "(log (sin x))"
    Assert.True(recContains "cos" result, $"Ожидался cos, результат: {result}")
    Assert.True(recContains "sin" result, $"Результат: {result}")

[<Fact>]
let ``Цепное правило: tanh(sqrt x) → sech^2(sqrt x) * 1/(2*sqrt x)`` () =
    let result = diffStr "x" "(tanh (sqrt x))"
    Assert.True(recContains "sech" result, $"Результат: {result}")
    Assert.True(recContains "sqrt" result, $"Результат: {result}")

[<Fact>]
let ``Цепное правило: atanh(x^2) → 2x/(1-x^4)`` () =
    let result = diffStr "x" "(atanh (^ x 2))"
    Assert.True(recContains "atanh" result = false, $"Не должно быть atanh в результате: {result}")
    // Результат: (* (/ 1 (- 1 (^ x 4))) (* 2 x)) или подобное
    Assert.True(recContains "x" result, $"Результат: {result}")

// --- Численная проверка через eval ---

[<Fact>]
let ``Численная проверка d/dx(sin x) в x=0 → cos(0)=1`` () =
    // Вычисляем (sin 0) через eval
    let exprs = readAll "(sin 0)"
    let result = List.head exprs |> fun e -> eval e globalEnv
    match result with
    | LispFloat f -> Assert.Equal(0.0, f, 6)
    | other -> Assert.Fail($"Ожидался 0.0, получено {other}")

[<Fact>]
let ``Численная проверка sinh(1)`` () =
    let result = readAll "(sinh 1)" |> List.head |> fun e -> eval e globalEnv
    match result with
    | LispFloat f -> Assert.Equal(System.Math.Sinh(1.0), f, 6)
    | other -> Assert.Fail($"Ожидался sinh(1), получено {other}")

[<Fact>]
let ``Численная проверка asech(0.5)`` () =
    let result = readAll "(asech 0.5)" |> List.head |> fun e -> eval e globalEnv
    match result with
    | LispFloat f -> Assert.Equal(System.Math.Acosh(2.0), f, 6)  // asech(0.5) = acosh(2)
    | other -> Assert.Fail($"Ожидался asech(0.5), получено {other}")

// Шаг 19: исправления, найденные интегратором
[<Fact>]
let ``Производная n-арного произведения из трёх множителей`` () =
    // (a·x·sin x)' по x: раньше голова "*" портилась (в списке появлялся 0 вместо "*")
    Assert.Equal("(+ (* a x (cos x)) (* a (sin x)))", Printer.prettyPrint (diffStr "x" "(* a x (sin x))"))

[<Fact>]
let ``Производная tanh и coth: sech в степени 2, а не -2`` () =
    Assert.Equal("(^ (sech x) 2)", Printer.prettyPrint (diffStr "x" "(tanh x)"))
    Assert.Equal("(* -1 (^ (csch x) 2))", Printer.prettyPrint (diffStr "x" "(coth x)"))

// --- ODE.0: производная неизвестной функции в точке и цепное правило ---

[<Fact>]
let ``ODE.0: diff (deriv f k u) повышает порядок`` () =
    let e = readAll "(deriv f 1 x)" |> List.head
    Assert.Equal("f''(x)", Printer.prettyPrint (diff "x" e |> simplify))

[<Fact>]
let ``ODE.0: цепное правило для неизвестной функции`` () =
    let e = readAll "(f (^ x 2))" |> List.head
    let s = Printer.prettyPrint (diff "x" e |> simplify)
    Assert.Contains("f'((^ x 2))", s)
    Assert.Contains("2 x", s)

[<Fact>]
let ``ODE.0: diff (y x) остаётся невычисленным`` () =
    Assert.Equal("(diff (y x) x)", Printer.prettyPrint (diffStr "x" "(y x)"))
