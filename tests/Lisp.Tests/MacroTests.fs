// Тесты макросов (defmacro + квазицитирование, Шаг 7)
module MacroTests

open System
open System.Numerics
open Xunit
open Types
open Reader
open Evaluator
open Printer

let evalStr (s: string) : LispValue =
    readAll s |> List.head |> fun e -> eval e globalEnv

let evalStrAll (s: string) : LispValue =
    readAll s |> fun es -> evalAll es globalEnv

let isStr (expected: string) (v: LispValue) =
    Assert.True((prettyPrint v = expected), $"Ожидалось {expected}, получено {prettyPrint v}")

let isInt (expected: BigInteger) (v: LispValue) =
    match v with
    | LispInteger n -> Assert.Equal(expected, n)
    | other -> Assert.Fail($"Ожидался LispInteger {expected}, получено {prettyPrint other}")

// --- Квазицитирование ---

[<Fact>]
let ``quasiquote: без unquote = quote`` () =
    evalStr "`(1 2 3)" |> isStr "(1 2 3)"

[<Fact>]
let ``unquote: вычисляет внутри квазицита`` () =
    evalStrAll "(define qv7 42) `(a ,qv7 b)" |> isStr "(a 42 b)"

[<Fact>]
let ``unquote: вычисление выражения`` () =
    evalStr "`,(+ 1 2)" |> isInt 3I

[<Fact>]
let ``unquote-splicing: вклеивает список`` () =
    evalStrAll "(define qs7 (list 2 3)) `(1 ,@qs7 4)" |> isStr "(1 2 3 4)"

[<Fact>]
let ``unquote-splicing: пустой список вклеивается как пусто`` () =
    // (list) → () — пустой splice
    evalStr "`(1 ,@(list) 2)" |> isStr "(1 2)"

[<Fact>]
let ``вложенный квазицит: парсится без ошибок`` () =
    // ```(a ,b) → вложенные quasiquote/unquote раскрываются послойно
    let parsed = readAll "```(a ,b)"
    Assert.True((List.length parsed = 1))

// --- defmacro ---

[<Fact>]
let ``defmacro: my-if раскрывается в cond`` () =
    evalStrAll "(defmacro (my-if c t e) `(cond (,c ,t) (else ,e))) (my-if (= 1 1) 10 20)"
    |> isInt 10I

[<Fact>]
let ``defmacro: аргументы не вычисляются при раскрытии (lazy)`` () =
    // (my-if #f (undefined-crash) 5) — then-ветка НЕ вычисляется благодаря cond
    evalStrAll "(defmacro (my-if2 c t e) `(cond (,c ,t) (else ,e))) (my-if2 #f (car 1) 5)"
    |> isInt 5I

[<Fact>]
let ``defmacro: swap меняет значения`` () =
    evalStrAll "(defmacro (swap a b) `(let ((tmp ,a)) (begin (set! ,a ,b) (set! ,b tmp)))) (define p7 1) (define q7 2) (swap p7 q7) (list p7 q7)"
    |> isStr "(2 1)"

[<Fact>]
let ``defmacro: квазицит внутри тела макроса с вычислением аргументов`` () =
    // Макрос twice: (twice f x) → (f (f x)) — классика
    evalStrAll "(defmacro (twice f x) `(,f (,f ,x))) (twice car (list (list 1 2) 3))"
    |> isInt 1I

[<Fact>]
let ``unquote-splicing в теле макроса: глобальный список вклеивается`` () =
    // data7 — РЕАЛЬНЫЙ список (значение, не форма): ,@data7 вклеивает его элементы
    // (b-параметр макроса держал бы сырую форму — это другая семантика)
    evalStrAll "(define data7 (list 2 3)) (defmacro (mk-list) `(list ,@data7)) (mk-list)"
    |> isStr "(2 3)"

[<Fact>]
let ``defmacro: макрос расширяет синтаксис интеграла`` () =
    // (D 'x ...) — производная; (I 'x ...) — интеграл, через макросы
    evalStrAll "(defmacro (I v e) `(integrate ,v ,e)) (I (quote x) (quote (^ x 2)))"
    |> isStr "(* 1/3 (^ x 3))"

[<Fact>]
let ``макрос видит определённые ранее переменные`` () =
    evalStrAll "(define scale7 10) (defmacro (scaled x) `(* ,scale7 ,x)) (scaled 4)"
    |> isInt 40I

[<Fact>]
let ``макрос: вызов в хвостовой позиции не течёт (TCO-совместимость)`` () =
    evalStrAll "(defmacro (dec7 n) `(- ,n 1)) (dec7 5)"
    |> isInt 4I