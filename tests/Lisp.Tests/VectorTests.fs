// Тесты векторных операций (Шаг 9; Шаг 15: векторы — тензоры ранга 1, написаны на Lisp)
module VectorTests

open System.Numerics
open Xunit
open Types
open Reader
open Simplify
open Order
open Expand
open Factor
open Evaluator

let isInt (expected: BigInteger) (v: LispValue) =
    match v with
    | LispInteger n -> Assert.Equal(expected, n)
    | other -> Assert.Fail($"Ожидался LispInteger {expected}, получено {other}")

let isListHead (expected: string) (v: LispValue) =
    match v with
    | LispList (LispSym h :: _) -> Assert.Equal(expected, h)
    | other -> Assert.Fail($"Ожидался список с головой {expected}, получено {other}")

let isListInts (expected: BigInteger list) (v: LispValue) =
    match v with
    | LispList items ->
        Assert.Equal(expected.Length, items.Length)
        List.iter2 (fun e n ->
            match e with
            | LispInteger n' -> Assert.Equal(n, n')
            | other -> Assert.Fail($"Ожидался LispInteger {n}, получено {other}"))
            items expected
    | other -> Assert.Fail($"Ожидался список, получено {other}")

let isListFloats (expected: float list) (v: LispValue) =
    match v with
    | LispList items ->
        Assert.Equal(expected.Length, items.Length)
        List.iter2 (fun e n ->
            match e with
            | LispFloat f -> Assert.Equal(n, f, 6)
            | other -> Assert.Fail($"Ожидался LispFloat {n}, получено {other}"))
            items expected
    | other -> Assert.Fail($"Ожидался список, получено {other}")

let evalStr (s: string) : LispValue =
    readAll s |> List.head |> fun e -> eval e globalEnv

let simpStr (s: string) : LispValue =
    readAll s |> List.head |> simplify

// Вычислить выражение, давшее тензор, и вернуть вложенный список (tensor->list)
let tl (s: string) : LispValue = evalStr ("(tensor->list " + s + ")")

// --- Builtins: vec+ ---

[<Fact>]
let ``vec+ '(1 2 3) '(4 5 6) → '(5 7 9)`` () =
    let r = tl "(vec+ '(1 2 3) '(4 5 6))"
    isListInts [5I; 7I; 9I] r

[<Fact>]
let ``vec+ с float → float`` () =
    let r = tl "(vec+ '(1 2) '(0.5 0.25))"
    isListFloats [1.5; 2.25] r

[<Fact>]
let ``vec+ разные размерности → ошибка`` () =
    Assert.ThrowsAny<System.Exception>(fun () -> evalStr "(vec+ '(1 2) '(1 2 3))" |> ignore) |> ignore

// --- Builtins: vec- ---

[<Fact>]
let ``vec- '(1 2 3) '(4 5 6) → '(-3 -3 -3)`` () =
    let r = tl "(vec- '(1 2 3) '(4 5 6))"
    isListInts [-3I; -3I; -3I] r

// --- Builtins: scale ---

[<Fact>]
let ``scale 3 '(1 2 3) → '(3 6 9)`` () =
    let r = tl "(scale 3 '(1 2 3))"
    isListInts [3I; 6I; 9I] r

[<Fact>]
let ``scale 0 '(1 2 3) → '(0 0 0)`` () =
    let r = tl "(scale 0 '(1 2 3))"
    isListInts [0I; 0I; 0I] r

// --- Builtins: dot ---

[<Fact>]
let ``dot '(1 2 3) '(4 5 6) → 32`` () =
    evalStr "(dot '(1 2 3) '(4 5 6))" |> isInt 32I

[<Fact>]
let ``dot '(3 4) '(3 4) → 25`` () =
    evalStr "(dot '(3 4) '(3 4))" |> isInt 25I

[<Fact>]
let ``dot пустые списки → ошибка (тензор ранга >= 1 непуст)`` () =
    Assert.ThrowsAny<System.Exception>(fun () -> evalStr "(dot '() '())" |> ignore) |> ignore

// --- Builtins: norm ---

[<Fact>]
let ``norm '(3 4) → 5`` () =
    evalStr "(norm '(3 4))" |> isInt 5I

[<Fact>]
let ``norm '(1 2 2) → 3`` () =
    evalStr "(norm '(1 2 2))" |> isInt 3I

[<Fact>]
let ``norm '(1 1) → sqrt(2) символьно`` () =
    let r = evalStr "(norm '(1 1))"
    isListHead "sqrt" r

// --- Simplify: векторное сложение ---

[<Fact>]
let ``(+ тензор тензор) → (5 7 9)`` () =
    let r = tl "(+ (tensor '(1 2 3)) (tensor '(4 5 6)))"
    isListInts [5I; 7I; 9I] r

[<Fact>]
let ``(+ тензор с символом) — символ в компоненте`` () =
    let r = tl "(+ (tensor '(1 x)) (tensor '(2 3)))"
    match r with
    | LispList [LispInteger n1; LispList [LispSym "+"; LispInteger n2; LispSym "x"]] ->
        Assert.Equal(3I, n1)
        Assert.Equal(3I, n2)
    | other -> Assert.Fail($"Ожидался '(3 (+ 3 x)), получено {other}")

// --- Вычитание ---

[<Fact>]
let ``(- тензор тензор) → (3 3 3)`` () =
    let r = tl "(- (tensor '(4 5 6)) (tensor '(1 2 3)))"
    isListInts [3I; 3I; 3I] r

// --- Скаляр на вектор ---

[<Fact>]
let ``(* 3 тензор) → (3 6 9)`` () =
    let r = tl "(* 3 (tensor '(1 2 3)))"
    isListInts [3I; 6I; 9I] r

[<Fact>]
let ``(* тензор 3) → (3 6 9) — обратный порядок`` () =
    let r = tl "(* (tensor '(1 2 3)) 3)"
    isListInts [3I; 6I; 9I] r

[<Fact>]
let ``simplify через список с тензорами`` () =
    // (simplify (list '* 3 t)) — выражение с объектом внутри
    let r = tl "(simplify (list '* 3 (tensor '(1 2 3))))"
    isListInts [3I; 6I; 9I] r

// --- Differentiate: покомпонентно ---

[<Fact>]
let ``diff по вектору — покомпонентно`` () =
    let r = tl "(diff 'x (make-tensor '(2) (lambda (idx) (list '^ 'x (+ 2 (car idx))))))"
    match r with
    | LispList [a; b] ->
        // a = (* 2 x), b = (* 3 (^ x 2))
        match a with
        | LispList [LispSym "*"; LispInteger n; LispSym "x"] -> Assert.Equal(2I, n)
        | other -> Assert.Fail($"Первый элемент: ожидался (* 2 x), получено {other}")
        match b with
        | LispList [LispSym "*"; LispInteger n; _] -> Assert.Equal(3I, n)
        | other -> Assert.Fail($"Второй элемент: ожидался (* 3 (^ x 2)), получено {other}")
    | other -> Assert.Fail($"Ожидался 2-элементный список, получено {other}")

// --- Негативные ---

[<Fact>]
let ``обычный список (1 2 3) — просто список, не вектор: (+ (1 2) (3 4)) не складывается`` () =
    let r = evalStr "(simplify '(+ (1 2) (3 4)))"
    match r with
    | LispList (LispSym "+" :: _) -> ()
    | other -> Assert.Fail($"Ожидалось символьное выражение (+ ...), получено {other}")

[<Fact>]
let ``(+ 1 2) — обычное сложение`` () =
    let r = readAll "(+ 1 2)" |> List.head |> simplify
    isInt 3I r

[<Fact>]
let ``cross: (1 0 0) x (0 1 0) = (0 0 1)`` () =
    isListInts [0I; 0I; 1I] (tl "(cross '(1 0 0) '(0 1 0))")

[<Fact>]
let ``cross символьный`` () =
    let r = Printer.prettyPrint (tl "(cross '(a b c) '(d e f))")
    Assert.Equal("((+ (* b f) (* -1 c e)) (+ (* -1 a f) (* c d)) (+ (* a e) (* -1 b d)))", r)

[<Fact>]
let ``cross не 3-вектор → ошибка`` () =
    Assert.ThrowsAny<System.Exception>(fun () -> evalStr "(cross '(1 2) '(3 4))" |> ignore) |> ignore
