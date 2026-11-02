// Тесты инфикс-ридера математической записи (MathReader.fs, Шаг 8b)
// Имена тестов — с префиксом «MathReader:» (имена в globalEnv пересекаются между файлами)
module MathReaderTests

open Xunit
open Types
open Reader
open Numeric
open Evaluator
open Printer
open MathPrinter
open MathReader

// Разобрать инфиксную строку → сравнить prettyPrint с ожидаемым s-выражением
let mrIs (src: string) (expected: string) : unit =
    let v = mathParse src
    Assert.True((prettyPrint v = expected),
                 $"Ожидалось «{expected}», получено «{prettyPrint v}»")

// Вычислить инфиксную строку с заданными значениями переменных
let mrEval (bindings: (string * LispValue) list) (src: string) : LispValue =
    let env = globalEnv.Extend []   // дочернее окружение — globalEnv не загрязняется
    for (n, v) in bindings do env.Define n v |> ignore
    eval (mathParse src) env

// Число-результат равен ожидаемому (сравнение через числовую башню)
let mrNum (expected: LispValue) (actual: LispValue) : unit =
    Assert.True(numEqual actual expected, $"Ожидалось {prettyPrint expected}, получено {prettyPrint actual}")

// --- Числа ---

[<Fact>]
let ``MathReader: целые числа`` () =
    Assert.True(structEqual (mathParse "42") (LispInteger 42I))
    mrIs "-5" "(- 0 5)"

[<Fact>]
let ``MathReader: float-литералы 2.5, 1e10, 1E+10`` () =
    match mathParse "2.5" with
    | LispFloat f -> Assert.Equal(2.5, f)
    | v -> failwithf "Ожидался float, получено %A" v
    match mathParse "1e10" with
    | LispFloat f -> Assert.Equal(1e10, f)
    | v -> failwithf "Ожидался float, получено %A" v
    match mathParse "1E+10" with
    | LispFloat f -> Assert.Equal(1e10, f)
    | v -> failwithf "Ожидался float, получено %A" v

[<Fact>]
let ``MathReader: рациональные 1/3 — число, не форма (/ 1 3)`` () =
    Assert.True(structEqual (mathParse "1/3") (LispRational (1I, 3I)))
    Assert.True(structEqual (mathParse "6/2") (LispInteger 3I))  // сокращается
    mrIs "x/2" "(/ x 2)"        // символ — обычное деление

// --- Приоритеты ---

[<Fact>]
let ``MathReader: приоритет умножения — 2+3*4 = 14`` () =
    mrEval [] "2+3*4" |> mrNum (LispInteger 14I)

[<Fact>]
let ``MathReader: 2*3+1 = 7`` () =
    mrEval [] "2*3+1" |> mrNum (LispInteger 7I)

[<Fact>]
let ``MathReader: скобки меняют приоритет — (2+3)*4 = 20`` () =
    mrEval [] "(2+3)*4" |> mrNum (LispInteger 20I)

[<Fact>]
let ``MathReader: степень правоассоциативна — 2^3^2 = 512`` () =
    mrEval [] "2^3^2" |> mrNum (LispInteger 512I)
    mrIs "x^y^2" "(^ x (^ y 2))"

// --- Неявное умножение ---

[<Fact>]
let ``MathReader: 2x при x=5 равно 10`` () =
    mrEval [("x", LispInteger 5I)] "2x" |> mrNum (LispInteger 10I)

[<Fact>]
let ``MathReader: 3(x+1) при x=2 равно 9`` () =
    mrEval [("x", LispInteger 2I)] "3(x+1)" |> mrNum (LispInteger 9I)

[<Fact>]
let ``MathReader: (x+1)(y+2) — произведение сумм`` () =
    mrEval [("x", LispInteger 1I); ("y", LispInteger 2I)] "(x+1)(y+2)"
    |> mrNum (LispInteger 8I)

[<Fact>]
let ``MathReader: 2sin(x) и x y — неявное умножение с функцией и символами`` () =
    mrEval [("x", LispInteger 0I)] "2sin(x)" |> mrNum (LispInteger 0I)
    mrEval [("x", LispInteger 3I); ("y", LispInteger 4I)] "x y" |> mrNum (LispInteger 12I)

// --- Унарный минус ---

[<Fact>]
let ``MathReader: -x^2 при x=3 равно -9 (минус слабее степени)`` () =
    mrEval [("x", LispInteger 3I)] "-x^2" |> mrNum (LispInteger (-9I))
    mrIs "-x^2" "(- 0 (^ x 2))"

[<Fact>]
let ``MathReader: 2^-3 — унарный минус в показателе (точная дробь — LANG.1)`` () =
    // LANG.1: (^ 2 -3) вычисляется точно: 1/8 (прежде — символьная форма (^ 2 -3))
    let r = mrEval [] "2^-3"
    Assert.Equal("1/8", prettyPrint r)
    mrIs "x^-2" "(^ x (- 0 2))"

// --- Цепочки операций ---

[<Fact>]
let ``MathReader: a - b - c — n-ary цепочка вычитаний`` () =
    mrIs "a - b - c" "(- a b c)"
    mrEval [] "5 - 3 - 1" |> mrNum (LispInteger 1I)

[<Fact>]
let ``MathReader: 8/2/2 — n-ary цепочка делений`` () =
    mrIs "8/2/2" "(/ 8 2 2)"
    mrEval [] "8/2/2" |> mrNum (LispInteger 2I)

[<Fact>]
let ``MathReader: 2x^2 + 3x - 5 — смешанная сумма`` () =
    mrIs "2x^2 + 3x - 5" "(- (+ (* 2 (^ x 2)) (* 3 x)) 5)"

// --- Функции и имена ---

[<Fact>]
let ``MathReader: sin(0) = 0, sqrt(4) = 2`` () =
    mrEval [] "sin(0)" |> mrNum (LispInteger 0I)
    mrEval [] "sqrt(4)" |> mrNum (LispInteger 2I)

[<Fact>]
let ``MathReader: sin(x + 1) — полный аргумент в скобках`` () =
    mrIs "sin(x + 1)" "(sin (+ x 1))"

[<Fact>]
let ``MathReader: π транслитерируется в pi`` () =
    mrIs "π" "pi"
    mrIs "2π" "(* 2 pi)"

// --- Ошибки парсинга ---

[<Theory>]
[<InlineData("2+")>]
[<InlineData("(x+1")>]
[<InlineData("2+3)")>]
[<InlineData("")>]
[<InlineData("*x")>]
let ``MathReader: синтаксические ошибки — исключение, не падение`` (src: string) =
    Assert.ThrowsAny<System.Exception>(fun () -> mathParse src |> ignore) |> ignore

// --- Round-trip: mathParse(mathPrint e) = e ---

[<Fact>]
let ``MathReader: round-trip канонических форм`` () =
    // n-ary цепочки, унарный минус, рациональные, функции, степень
    let forms = [
        "(+ (* 2 (^ x 2)) (* 3 x) 5)"
        "(- (* 2 (^ x 2)) (* 3 x) 5)"
        "(- (+ (* 2 (^ x 2)) (* 3 x)) 5)"
        "(- 0 x)"
        "(* 2 (- 0 x))"
        "(/ (+ x 1) 2)"
        "(* 1/3 (^ x 3))"
        "(+ 1/3 x)"
        "(sin (+ x 1))"
        "(^ x (^ y 2))"
    ]
    for src in forms do
        let e = readAll src |> List.head
        let back = mathParse (mathPrint e)
        Assert.True(structEqual back e,
                    $"Round-trip нарушен: {src} → «{mathPrint e}» → {prettyPrint back}")

// --- Интеграция: builtins и JSON-API ---

[<Fact>]
let ``MathReader: builtin math-read возвращает дерево`` () =
    let v = readAll "(math-read \"2x^2 + 3x - 5\")" |> List.head
    let r = eval v globalEnv
    Assert.True(structEqual r (readAll "(- (+ (* 2 (^ x 2)) (* 3 x)) 5)" |> List.head),
                $"Получено: {prettyPrint r}")

[<Fact>]
let ``MathReader: builtin math разбирает и упрощает`` () =
    let r1 = eval (readAll "(math \"x + 0\")" |> List.head) globalEnv
    Assert.True(structEqual r1 (LispSym "x"), $"Получено: {prettyPrint r1}")
    let r2 = eval (readAll "(math \"1+2\")" |> List.head) globalEnv
    mrNum (LispInteger 3I) r2

[<Fact>]
let ``MathReader: JSON-API op parse`` () =
    let resp = AgentApi.handleJsonRequest (AgentApi.makeSession ()) "{\"op\":\"parse\",\"code\":\"2x+3\"}"
    Assert.True(resp.Contains("\"ok\":true"), resp)
    Assert.True(resp.Contains("\"result\":\"(+ (* 2 x) 3)\"") || resp.Contains("\"result\":\"(\\u002B (* 2 x) 3)\""), resp)

// --- ODE.0: штрихи производных ---

[<Fact>]
let ``MathReader: ODE.0 — y′, y″, y′(0)`` () =
    mrIs "y'" "(diff (y x) x)"
    mrIs "y''" "(diff (diff (y x) x) x)"
    mrIs "y'(0)" "(at (diff (y x) x) (= x 0))"

[<Fact>]
let ``MathReader: y′ в dsolve(…, y(t)) — по переменной t`` () =
    mrIs "dsolve(y'' = y, y(t))" "(dsolve (= (diff (diff (y t) t) t) y) (y t))"
    mrIs "dsolve(y' = y, y(t), y'(0) = 1, y'(t) = 2)" "(dsolve (= (diff (y t) t) y) (y t) (= (at (diff (y t) t) (= t 0)) 1) (= (diff (y t) t) 2))"
    mrIs "dsolve(y' = y, y(x))" "(dsolve (= (diff (y x) x) y) (y x))"
    mrIs "y'(0) + dsolve(y', y(t))" "(+ (at (diff (y x) x) (= x 0)) (dsolve (diff (y t) t) (y t)))"
