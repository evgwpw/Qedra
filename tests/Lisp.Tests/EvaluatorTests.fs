// Тесты вычислителя (Evaluator.fs)
module EvaluatorTests

open System.Numerics
open Xunit
open Types
open Reader
open Evaluator
open Builtins

// Вспомогательные функции для проверки
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

let isList (expected: LispValue list) (v: LispValue) =
    match v with
    | LispList items ->
        Assert.Equal(expected.Length, items.Length)
        List.iter2 (fun (e: LispValue) (a: LispValue) ->
            if not (Builtins.deepEqual e a) then Assert.Fail($"Ожидалось {e}, получено {a}")) expected items
    | other -> Assert.Fail($"Ожидался LispList, получено {other}")

// Вычислить строку в глобальном окружении
let evalStr (s: string) : LispValue =
    readAll s |> List.head |> fun e -> eval e globalEnv

// --- Арифметика ---

[<Fact>]
let ``Сложение двух целых`` () =
    evalStr "(+ 1 2)" |> isInt 3I

[<Fact>]
let ``Сложение нескольких целых`` () =
    evalStr "(+ 1 2 3 4)" |> isInt 10I

[<Fact>]
let ``Вычитание`` () =
    evalStr "(- 10 3)" |> isInt 7I

[<Fact>]
let ``Унарный минус`` () =
    evalStr "(- 5)" |> isInt (-5I)

[<Fact>]
let ``Умножение`` () =
    evalStr "(* 6 7)" |> isInt 42I

[<Fact>]
let ``Деление точное`` () =
    evalStr "(/ 10 2)" |> isInt 5I

[<Fact>]
let ``Деление неточное → рациональное`` () =
    match evalStr "(/ 1 3)" with
    | LispRational (p, q) ->
        Assert.Equal(1I, p)
        Assert.Equal(3I, q)
    | other -> Assert.Fail($"Ожидался 1/3, получено {other}")

[<Fact>]
let ``Остаток от деления`` () =
    evalStr "(mod 10 3)" |> isInt 1I

// --- Сравнения ---

[<Fact>]
let ``Сравнение на равенство`` () =
    evalStr "(= 5 5)" |> isBool true
    evalStr "(= 5 6)" |> isBool false

[<Fact>]
let ``Сравнение меньше`` () =
    evalStr "(< 3 5)" |> isBool true
    evalStr "(< 5 3)" |> isBool false

[<Fact>]
let ``Сравнение больше`` () =
    evalStr "(> 5 3)" |> isBool true
    evalStr "(> 3 5)" |> isBool false

// --- Специальные формы ---

[<Fact>]
let ``Quote возвращает аргумент как есть`` () =
    evalStr "(quote x)" |> isSym "x"
    evalStr "(quote (1 2 3))" |> isList [LispInteger 1I; LispInteger 2I; LispInteger 3I]

[<Fact>]
let ``If с истинным условием`` () =
    evalStr "(if #t 1 2)" |> isInt 1I

[<Fact>]
let ``If с ложным условием`` () =
    evalStr "(if #f 1 2)" |> isInt 2I

[<Fact>]
let ``If без else при ложном условии → nil`` () =
    match evalStr "(if #f 1)" with
    | LispNil -> ()
    | other -> Assert.Fail($"Ожидался nil, получено {other}")

[<Fact>]
let ``Begin возвращает последнее значение`` () =
    evalStr "(begin 1 2 3)" |> isInt 3I

[<Fact>]
let ``Cond с первой подходящей веткой`` () =
    evalStr "(cond (#f 1) (#t 2) (else 3))" |> isInt 2I

[<Fact>]
let ``Cond с else`` () =
    evalStr "(cond (#f 1) (#f 2) (else 3))" |> isInt 3I

[<Fact>]
let ``And короткое замыкание`` () =
    evalStr "(and #t #t)" |> isBool true
    evalStr "(and #t #f)" |> isBool false

[<Fact>]
let ``Or короткое замыкание`` () =
    evalStr "(or #f #t)" |> isBool true
    evalStr "(or #f #f)" |> isBool false

// --- Define и Lambda ---

[<Fact>]
let ``Define переменной`` () =
    // define мутирует глобальное окружение
    evalStr "(define x 42)" |> isSym "x"
    evalStr "x" |> isInt 42I

[<Fact>]
let ``Lambda создание и вызов`` () =
    evalStr "((lambda (x) (* x x)) 5)" |> isInt 25I

[<Fact>]
let ``Define функции`` () =
    evalStr "(define (sq x) (* x x))" |> isSym "sq"
    evalStr "(sq 7)" |> isInt 49I

[<Fact>]
let ``Замыкание захватывает окружение`` () =
    evalStr "(define (adder n) (lambda (x) (+ x n)))" |> ignore
    evalStr "(define add5 (adder 5))" |> ignore
    evalStr "(add5 10)" |> isInt 15I

[<Fact>]
let ``Let локальные переменные`` () =
    evalStr "(let ((x 10) (y 20)) (+ x y))" |> isInt 30I

// --- Списки ---

[<Fact>]
let ``Car первого элемента`` () =
    evalStr "(car '(1 2 3))" |> isInt 1I

[<Fact>]
let ``Cdr хвост списка`` () =
    evalStr "(cdr '(1 2 3))" |> isList [LispInteger 2I; LispInteger 3I]

[<Fact>]
let ``Cons добавляет в голову`` () =
    evalStr "(cons 1 '(2 3))" |> isList [LispInteger 1I; LispInteger 2I; LispInteger 3I]

[<Fact>]
let ``List создаёт список`` () =
    evalStr "(list 1 2 3)" |> isList [LispInteger 1I; LispInteger 2I; LispInteger 3I]

[<Fact>]
let ``Null? пустой список → #t`` () =
    evalStr "(null? '())" |> isBool true

[<Fact>]
let ``Null? непустой список → #f`` () =
    evalStr "(null? '(1))" |> isBool false

// --- Логика ---

[<Fact>]
let ``Not отрицание`` () =
    evalStr "(not #t)" |> isBool false
    evalStr "(not #f)" |> isBool true

// --- Equal? ---

[<Fact>]
let ``Equal? для чисел`` () =
    evalStr "(equal? 5 5)" |> isBool true
    evalStr "(equal? 5 6)" |> isBool false

[<Fact>]
let ``Equal? для списков`` () =
    evalStr "(equal? '(1 2 3) '(1 2 3))" |> isBool true
    evalStr "(equal? '(1 2 3) '(1 2 4))" |> isBool false

[<Fact>]
let ``Cond: ветка с несколькими выражениями (неявный begin)`` () =
    evalStr "(cond (#f 1) (#t (define q15a 7) (+ q15a 1)) (else 3))" |> isInt 8I
    evalStr "(cond (#f 1) (else 1 2 3))" |> isInt 3I

[<Fact>]
let ``Cond: хвостовая позиция последнего выражения ветки не растит стек`` () =
    evalStr "(define (loop15a n) (cond ((= n 0) 'done) (else (+ n 0) (loop15a (- n 1)))))" |> ignore
    match evalStr "(loop15a 100000)" with
    | LispSym "done" -> ()
    | other -> Assert.Fail($"Ожидался done, получено {other}")
