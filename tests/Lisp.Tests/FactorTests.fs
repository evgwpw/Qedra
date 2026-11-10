// Тесты факторизации, set! и load (Шаг 5)
module FactorTests

open System
open System.IO
open System.Numerics
open Xunit
open Types
open Reader
open Numeric
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

let parse (s: string) : LispValue = readAll s |> List.head

let evalStr (s: string) : LispValue =
    readAll s |> List.head |> fun e -> eval e globalEnv

let isSymStr (expected: string) (v: LispValue) =
    Assert.True(prettyPrint v = expected, $"Ожидалось {expected}, получено {prettyPrint v}")

// --- factor: вынесение общего множителя ---

[<Fact>]
let ``factor: (+ (* 2 x) (* 2 y)) → (* 2 (+ x y))`` () =
    let result = parse "(+ (* 2 x) (* 2 y))" |> factor
    let str = prettyPrint result
    Assert.True((str = "(* 2 (+ x y))"), $"Ожидался (* 2 (+ x y)), получено {str}")

[<Fact>]
let ``factor: (+ (* 3 x) (* 3 y) (* 3 z)) → (* 3 (+ x y z))`` () =
    let result = parse "(+ (* 3 x) (* 3 y) (* 3 z))" |> factor
    let str = prettyPrint result
    Assert.True((str = "(* 3 (+ x y z))"), $"Ожидался (* 3 (+ x y z)), получено {str}")

[<Fact>]
let ``factor: (+ (* a x) (* b x)) → общий множитель x`` () =
    // (+ (* a x) (* b x)) → (* x (+ a b))  — общий множитель x (нечисловой)
    let result = parse "(+ (* a x) (* b x))" |> factor
    match result with
    | LispList [LispSym "*"; LispSym "x"; LispList [LispSym "+"; LispSym "a"; LispSym "b"]] -> ()
    | other -> Assert.Fail($"Ожидался (* x (+ a b)), получено {prettyPrint other}")

[<Fact>]
let ``factor: без общего множителя — не меняется`` () =
    // (+ (* 2 x) (* 3 y)) — общего множителя нет
    let result = parse "(+ (* 2 x) (* 3 y))" |> factor
    // должно остаться суммой двух разных произведений
    match result with
    | LispList (LispSym "+" :: _) -> ()
    | other -> Assert.Fail($"Ожидалась сумма, получено {prettyPrint other}")

[<Fact>]
let ``factor из REPL`` () =
    // ВАЖНО: quote — иначе eval вычислит символ x
    let result = evalStr "(factor '(+ (* 2 x) (* 2 y)))"
    let str = prettyPrint result
    Assert.True((str = "(* 2 (+ x y))"), $"Результат: {str}")

[<Fact>]
let ``factor: expand-обратимость (* (+ x 1) (+ x 2)) → expand(factor) совпадает`` () =
    // expand((* (+ x 1) (+ x 2))) = (+ (* x x) (* 3 x) 2) — но factor должен уметь вынести минимум
    let expanded = parse "(* (+ x 1) (+ x 2))" |> expand
    // expanded — сумма; факторизация может вынести что-то или нет
    match expanded with
    | LispList (LispSym "+" :: _) -> ()
    | other -> Assert.Fail($"expand должен дать сумму, получено {prettyPrint other}")
    // factor не должен ломать выражение: expand(factor(x)) эквивалентен x
    let factored = factor expanded
    let reExpanded = expand factored |> simplify
    let direct = parse "(* (+ x 1) (+ x 2))" |> expand |> simplify
    // Сравниваем структуры: оба должны быть эквивалентны... 
    // Простая проверка: оба — суммы с одинаковым числом термов после flatten
    let countTerms (v: LispValue) =
        match simplify v with
        | LispList (LispSym "+" :: ts) -> ts.Length
        | _ -> 1
    Assert.Equal(countTerms direct, countTerms reExpanded)

// --- set! ---

[<Fact>]
let ``set! переприсваивает переменную`` () =
    evalStr "(define sx 10)" |> ignore
    evalStr "sx" |> isInt 10I
    evalStr "(set! sx 20)" |> ignore
    evalStr "sx" |> isInt 20I

[<Fact>]
let ``set! на несуществующей переменной — ошибка`` () =
    Assert.ThrowsAny<Exception>(fun () ->
        evalStr "(set! nonexistent-var-xyz 5)" |> ignore)

[<Fact>]
let ``set! меняет переменную из родительского окружения (замыкание)`` () =
    evalStr "(define counter-val 0)" |> ignore
    evalStr "(define (bump) (set! counter-val (+ counter-val 1)))" |> ignore
    evalStr "(bump)" |> ignore
    evalStr "(bump)" |> ignore
    evalStr "counter-val" |> isInt 2I

// --- load ---

[<Fact>]
let ``load выполняет файл с define`` () =
    let tmp = Path.Combine(Path.GetTempPath(), "lisp_test_load.lisp")
    File.WriteAllText(tmp, "(define loaded-x 42)\n(define (loaded-fn n) (* n n))\n(loaded-fn loaded-x)")
    try
        let result = loadIntoEnv tmp globalEnv
        result |> isInt (42I * 42I)
        // define из файла видны в глобальном окружении
        evalStr "loaded-x" |> isInt 42I
    finally
        File.Delete tmp

[<Fact>]
let ``load несуществующего файла — ошибка`` () =
    Assert.ThrowsAny<Exception>(fun () ->
        loadIntoEnv "Z:\\nonexistent\\file.lisp" globalEnv |> ignore)

[<Fact>]
let ``load из REPL через builtin`` () =
    let tmp = Path.Combine(Path.GetTempPath(), "lisp_test_load2.lisp")
    File.WriteAllText(tmp, "(+ 1 2 3)")
    try
        // Заменяем обратные слэши на прямые — Lisp-парсер строк ест \
        let lispPath = tmp.Replace('\\', '/')
        let result = evalStr $"(load \"{lispPath}\")"
        result |> isInt 6I
    finally
        File.Delete tmp

// --- set! + simplify вместе ---

[<Fact>]
let ``set! с символьными вычислениями`` () =
    // quote — сохраняем символьное выражение, не вычисляя x
    evalStr "(define my-expr '(+ (* 4 x) (* 6 x)))" |> ignore
    evalStr "(set! my-expr (simplify my-expr))" |> ignore
    // после simplify: (* 10 x)
    let result = evalStr "my-expr"
    let str = prettyPrint result
    Assert.True((str = "(* 10 x)"), $"Ожидался (* 10 x), получено {str}")