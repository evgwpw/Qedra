// Тесты инфиксного pretty-printer'а математических выражений (MathPrinter.fs, Шаг 8a)
// Имена тестов — с префиксом «MathPrinter:» (классы не параллелятся, имена в разных файлах могут пересекаться)
module MathPrinterTests

open Xunit
open Types
open Reader
open Numeric
open Evaluator
open Printer
open MathPrinter

// Разбор одной формы
let mpParse (s: string) : LispValue = readAll s |> List.head

// mathPrint (разобранная форма) = ожидаемая строка
let mpIs (expected: string) (code: string) : unit =
    let v = mpParse code
    Assert.True((mathPrint v = expected),
                 $"Ожидалось «{expected}», получено «{mathPrint v}»")

// --- Неявное умножение ---

[<Fact>]
let ``MathPrinter: 2x`` () =
    mpIs "2x" "(* 2 x)"

[<Fact>]
let ``MathPrinter: 3(x + 1) — скобки при неявном умножении`` () =
    mpIs "3(x + 1)" "(* 3 (+ x 1))"

[<Fact>]
let ``MathPrinter: (x + 1)(y + 2) — произведение сумм`` () =
    mpIs "(x + 1)(y + 2)" "(* (+ x 1) (+ y 2))"

[<Fact>]
let ``MathPrinter: 2sin(x) — функция после числа`` () =
    mpIs "2sin(x)" "(* 2 (sin x))"

[<Fact>]
let ``MathPrinter: x*y и 2*3 — явная звёздочка между символами и числами`` () =
    mpIs "x*y" "(* x y)"
    mpIs "2*3" "(* 2 3)"

[<Fact>]
let ``MathPrinter: 2*(-x) — звёздочка и скобки перед унарным минусом`` () =
    mpIs "2*(-x)" "(* 2 (- 0 x))"

// --- Приоритеты и минимальные скобки ---

[<Fact>]
let ``MathPrinter: 2x^2 + 3x + 5`` () =
    mpIs "2x^2 + 3x + 5" "(+ (* 2 (^ x 2)) (* 3 x) 5)"

[<Fact>]
let ``MathPrinter: 1 + 2x — без лишних скобок`` () =
    mpIs "1 + 2x" "(+ 1 (* 2 x))"

[<Fact>]
let ``MathPrinter: (x + 1)/2 и x/(a*b)`` () =
    mpIs "(x + 1)/2" "(/ (+ x 1) 2)"
    mpIs "x/(a*b)" "(/ x (* a b))"

[<Fact>]
let ``MathPrinter: a - b - c — цепочка вычитаний`` () =
    mpIs "a - b - c" "(- a b c)"

// --- Степени ---

[<Fact>]
let ``MathPrinter: x^2`` () =
    mpIs "x^2" "(^ x 2)"

[<Fact>]
let ``MathPrinter: (x + 1)^2 — скобки вокруг суммы-основания`` () =
    mpIs "(x + 1)^2" "(^ (+ x 1) 2)"

[<Fact>]
let ``MathPrinter: x^y^2 и (x^2)^3 — ассоциативность степени`` () =
    mpIs "x^y^2" "(^ x (^ y 2))"
    mpIs "(x^2)^3" "(^ (^ x 2) 3)"

// --- Унарный минус и отрицательные числа ---

[<Fact>]
let ``MathPrinter: -cos(x)`` () =
    mpIs "-cos(x)" "(- 0 (cos x))"

[<Fact>]
let ``MathPrinter: -x^2 и -(x + 1)`` () =
    mpIs "-x^2" "(- 0 (^ x 2))"
    mpIs "-(x + 1)" "(- 0 (+ x 1))"

[<Fact>]
let ``MathPrinter: (-2)^2 и x^-2 → 1/x^2 — отрицательные в степени`` () =
    mpIs "(-2)^2" "(^ -2 2)"
    mpIs "1/x^2" "(^ x -2)"  // Шаг 13: отрицательный показатель печатается дробью

// --- Функции ---

[<Fact>]
let ``MathPrinter: sin(x) и sin(x + 1)`` () =
    mpIs "sin(x)" "(sin x)"
    mpIs "sin(x + 1)" "(sin (+ x 1))"
    mpIs "sqrt(x)" "(sqrt x)"
    mpIs "ln(x)" "(ln x)"

// --- Рациональные дроби ---

[<Fact>]
let ``MathPrinter: дроби 1/3, 1/3 + x, x^(1/2), 1/3*x^3`` () =
    mpIs "1/3" "1/3"
    mpIs "1/3 + x" "(+ 1/3 x)"
    mpIs "x^(1/2)" "(^ x 1/2)"
    mpIs "1/3*x^3" "(* 1/3 (^ x 3))"

// --- Не-математические значения — s-выражение ---

[<Fact>]
let ``MathPrinter: не-математика — обычный prettyPrint`` () =
    mpIs "(foo x y)" "(foo x y)"
    mpIs "\"hello\"" "\"hello\""
    mpIs "#t" "#t"
    mpIs "42" "42"
    mpIs "2.5" "2.5"
    mpIs "(+ 1 \"str\")" "(+ 1 \"str\")"

// --- Интеграция: builtin math-print ---

[<Fact>]
let ``MathPrinter: builtin math-print возвращает строку`` () =
    let v = mpParse "(math-print '(+ (* 2 (^ x 2)) (* 3 x) 5))"
    let r = eval v globalEnv
    Assert.True((structEqual r (LispStr "2x^2 + 3x + 5")), $"Получено: {prettyPrint r}")