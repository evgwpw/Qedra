// Тесты матричных операций (Шаг 10; Шаг 15: матрицы — тензоры ранга 2, написаны на Lisp)
module MatrixTests

open System.Numerics
open Xunit
open Types
open Reader
open Simplify
open Order
open Expand
open Factor
open Differentiate
open Evaluator

let isInt (expected: BigInteger) (v: LispValue) =
    match v with
    | LispInteger n -> Assert.Equal(expected, n)
    | other -> Assert.Fail($"Ожидался LispInteger {expected}, получено {other}")

let isRational (expectedNum: BigInteger) (expectedDen: BigInteger) (v: LispValue) =
    match v with
    | LispRational (n, d) -> Assert.Equal(expectedNum, n); Assert.Equal(expectedDen, d)
    | other -> Assert.Fail($"Ожидался LispRational({expectedNum}, {expectedDen}), получено {other}")

let evalStr (s: string) : LispValue =
    readAll s |> List.head |> fun e -> eval e globalEnv

let simpStr (s: string) : LispValue =
    readAll s |> List.head |> simplify

// Вычислить выражение, давшее тензор, и вернуть вложенный список (tensor->list)
let tl (s: string) : LispValue = evalStr ("(tensor->list " + s + ")")

// --- mat ---

[<Fact>]
let ``mat '((1 2) (3 4)) → прямоугольная`` () =
    let r = tl "(mat '((1 2) (3 4)))"
    match r with
    | LispList [LispList [a; b]; LispList [c; d]] ->
        isInt 1I a; isInt 2I b; isInt 3I c; isInt 4I d
    | other -> Assert.Fail($"Ожидалась матрица 2×2, получено {other}")

[<Fact>]
let ``mat '((1 2) (3)) → ошибка`` () =
    Assert.ThrowsAny<System.Exception>(fun () -> tl "(mat '((1 2) (3)))" |> ignore) |> ignore

// --- mat-t ---

[<Fact>]
let ``mat-t '((1 2 3) (4 5 6)) → ((1 4) (2 5) (3 6))`` () =
    let r = tl "(mat-t '((1 2 3) (4 5 6)))"
    match r with
    | LispList [LispList [a1; a2]; LispList [b1; b2]; LispList [c1; c2]] ->
        isInt 1I a1; isInt 4I a2
        isInt 2I b1; isInt 5I b2
        isInt 3I c1; isInt 6I c2
    | other -> Assert.Fail($"Ожидалась транспонированная 3×2, получено {other}")

[<Fact>]
let ``mat-t '((1)) → ((1))`` () =
    let r = tl "(mat-t '((1)))"
    match r with
    | LispList [LispList [a]] -> isInt 1I a
    | other -> Assert.Fail($"Ожидалась ((1)), получено {other}")

[<Fact>]
let ``mat-t '() → ошибка (пустой тензор невозможен)`` () =
    Assert.ThrowsAny<System.Exception>(fun () -> evalStr "(mat-t '())" |> ignore) |> ignore

[<Fact>]
let ``mat-t не матрица (вектор) → ошибка`` () =
    Assert.ThrowsAny<System.Exception>(fun () -> evalStr "(mat-t '(1 2 3))" |> ignore) |> ignore

// --- mat-mul ---

[<Fact>]
let ``mat-mul 2×2 × 2×2`` () =
    let r = tl "(mat-mul '((1 2) (3 4)) '((5 6) (7 8)))"
    match r with
    | LispList [LispList [a; b]; LispList [c; d]] ->
        isInt 19I a; isInt 22I b; isInt 43I c; isInt 50I d
    | other -> Assert.Fail($"Ожидалась ((19 22) (43 50)), получено {other}")

[<Fact>]
let ``mat-mul identity → B`` () =
    let r = tl "(mat-mul '((1 0) (0 1)) '((5 6) (7 8)))"
    match r with
    | LispList [LispList [a; b]; LispList [c; d]] ->
        isInt 5I a; isInt 6I b; isInt 7I c; isInt 8I d
    | other -> Assert.Fail($"Ожидалась ((5 6) (7 8)), получено {other}")

[<Fact>]
let ``mat-mul 2×3 × 3×2`` () =
    let r = tl "(mat-mul '((1 2 3) (4 5 6)) '((1 2) (3 4) (5 6)))"
    match r with
    | LispList [LispList [a; b]; LispList [c; d]] ->
        isInt 22I a; isInt 28I b; isInt 49I c; isInt 64I d
    | other -> Assert.Fail($"Ожидалась ((22 28) (49 64)), получено {other}")

[<Fact>]
let ``mat-mul несогласованные размерности → ошибка`` () =
    Assert.ThrowsAny<System.Exception>(fun () ->
        tl "(mat-mul '((1 2 3)) '((1 2) (3 4)))" |> ignore) |> ignore

// --- det ---

[<Fact>]
let ``det 1×1 → элемент`` () =
    let r = evalStr "(det '((7)))"
    isInt 7I r

[<Fact>]
let ``det 2×2 → ad-bc`` () =
    let r = evalStr "(det '((1 2) (3 4)))"
    isInt (-2I) r

[<Fact>]
let ``det 3×3 → -3`` () =
    let r = evalStr "(det '((1 2 3) (4 5 6) (7 8 10)))"
    isInt (-3I) r

[<Fact>]
let ``det 2×2 символьный → x*w - y*z`` () =
    let r = evalStr "(det '((x y) (z w)))"
    match r with
    | LispList [LispSym "+"
                ; LispList [LispSym "*"; LispSym "w"; LispSym "x"]
                ; LispList [LispSym "*"; LispInteger m; LispSym "y"; LispSym "z"]] when m = -1I -> ()
    | other -> Assert.Fail($"Ожидался (+ (* w x) (* -1 y z)), получено {other}")

[<Fact>]
let ``det не квадратная → ошибка`` () =
    Assert.ThrowsAny<System.Exception>(fun () -> evalStr "(det '((1 2 3) (4 5 6)))" |> ignore) |> ignore

// --- inv ---

[<Fact>]
let ``inv '((1 2) (3 4)) → ((-2 1) (3/2 -1/2))`` () =
    let r = tl "(inv '((1 2) (3 4)))"
    match r with
    | LispList [LispList [a; b]; LispList [c; d]] ->
        isInt (-2I) a; isInt 1I b
        isRational 3I 2I c; isRational (-1I) 2I d
    | other -> Assert.Fail($"Ожидалась ((-2 1) (3/2 -1/2)), получено {other}")

[<Fact>]
let ``inv '((5)) → ((1/5))`` () =
    let r = tl "(inv '((5)))"
    match r with
    | LispList [LispList [a]] -> isRational 1I 5I a
    | other -> Assert.Fail($"Ожидалась ((1/5)), получено {other}")

[<Fact>]
let ``A * inv(A) = I (2×2)`` () =
    let r = tl "(mat-mul '((1 2) (3 4)) (inv '((1 2) (3 4))))"
    match r with
    | LispList [LispList [a; b]; LispList [c; d]] ->
        isInt 1I a; isInt 0I b; isInt 0I c; isInt 1I d
    | other -> Assert.Fail($"Ожидалась единичная матрица, получено {other}")

[<Fact>]
let ``inv вырожденная → ошибка`` () =
    Assert.ThrowsAny<System.Exception>(fun () -> tl "(inv '((1 2) (2 4)))" |> ignore) |> ignore

// --- rank ---

[<Fact>]
let ``rank full 2×2 → 2`` () =
    let r = evalStr "(rank '((1 2) (3 4)))"
    isInt 2I r

[<Fact>]
let ``rank 2×2 rank 1 → 1`` () =
    let r = evalStr "(rank '((1 2) (2 4)))"
    isInt 1I r

[<Fact>]
let ``rank 3×3 identity → 3`` () =
    let r = evalStr "(rank '((1 0 0) (0 1 0) (0 0 1)))"
    isInt 3I r

[<Fact>]
let ``rank 3×3 все пропорциональны → 1`` () =
    let r = evalStr "(rank '((1 2 3) (2 4 6) (3 6 9)))"
    isInt 1I r

[<Fact>]
let ``rank 3×3 rank 2 → 2`` () =
    let r = evalStr "(rank '((1 2 3) (2 4 5) (3 6 7)))"
    isInt 2I r

// --- simplify ---

[<Fact>]
let ``(+ матрица матрица) → покомпонентно`` () =
    let r = tl "(+ (tensor '((1 2) (3 4))) (tensor '((5 6) (7 8))))"
    match r with
    | LispList [LispList [a; b]; LispList [c; d]] ->
        isInt 6I a; isInt 8I b; isInt 10I c; isInt 12I d
    | other -> Assert.Fail($"Ожидалась ((6 8) (10 12)), получено {other}")

[<Fact>]
let ``(- матрица матрица) → покомпонентно`` () =
    let r = tl "(- (tensor '((5 6) (7 8))) (tensor '((1 2) (3 4))))"
    match r with
    | LispList [LispList [a; b]; LispList [c; d]] ->
        isInt 4I a; isInt 4I b; isInt 4I c; isInt 4I d
    | other -> Assert.Fail($"Ожидалась ((4 4) (4 4)), получено {other}")

[<Fact>]
let ``(* скаляр матрица) → покомпонентно`` () =
    let r = tl "(* 3 (tensor '((1 2) (3 4))))"
    match r with
    | LispList [LispList [a; b]; LispList [c; d]] ->
        isInt 3I a; isInt 6I b; isInt 9I c; isInt 12I d
    | other -> Assert.Fail($"Ожидалась ((3 6) (9 12)), получено {other}")

// --- diff ---

[<Fact>]
let ``diff по матрице — покомпонентно`` () =
    // Матрица 1×2: ((^ x 2) x)
    let r = tl "(diff 'x (tensor-from-flat '(1 2) (list '(^ x 2) 'x)))"
    // diff(x^2) = (* 2 x), diff(x) = 1
    match r with
    | LispList [LispList [a; b]] ->
        isInt 1I b
        match a with
        | LispList [LispSym "*"; LispInteger n; LispSym "x"] -> Assert.Equal(2I, n)
        | other -> Assert.Fail($"Ожидался (* 2 x), получено {other}")
    | other -> Assert.Fail($"Ожидалась матрица 1×2, получено {other}")

// --- tensor? ---

[<Fact>]
let ``tensor? на матрице, списке и числе`` () =
    Assert.Equal("#t", Printer.prettyPrint (evalStr "(tensor? (tensor '((1 2) (3 4))))"))
    Assert.Equal("#f", Printer.prettyPrint (evalStr "(tensor? '((1 2) (3 4)))"))
    Assert.Equal("#f", Printer.prettyPrint (evalStr "(tensor? 5)"))

[<Fact>]
let ``mat рваная матрица → ошибка`` () =
    Assert.ThrowsAny<System.Exception>(fun () -> evalStr "(mat '((1 2) (3 4 5)))" |> ignore) |> ignore
