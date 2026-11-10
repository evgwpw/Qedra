// Тесты тензоров (Шаг 11; Шаг 15: тензор — пользовательский тип на Lisp, lib\tensor.lisp)
module TensorTests

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

let isRational (expectedNum: BigInteger) (expectedDen: BigInteger) (v: LispValue) =
    match v with
    | LispRational (n, d) -> Assert.Equal(expectedNum, n); Assert.Equal(expectedDen, d)
    | other -> Assert.Fail($"Ожидался LispRational({expectedNum}, {expectedDen}), получено {other}")

let evalStr (s: string) : LispValue =
    readAll s |> List.head |> fun e -> eval e globalEnv

// Вложенный список компонент тензора
let tl (s: string) : LispValue = evalStr ("(tensor->list " + s + ")")

// Текст результата через prettyPrint (для сравнения символьных результатов)
let pp (s: string) : string = Printer.prettyPrint (evalStr s)
let ppl (s: string) : string = Printer.prettyPrint (tl s)

let throws (s: string) =
    Assert.ThrowsAny<System.Exception>(fun () -> evalStr s |> ignore) |> ignore

// --- shape ---

[<Fact>]
let ``shape скаляр → ()`` () =
    match evalStr "(shape 42)" with
    | LispList [] | LispNil -> ()
    | other -> Assert.Fail($"Ожидался (), получено {other}")

[<Fact>]
let ``shape вектор → (3)`` () =
    Assert.Equal("(3)", pp "(shape '(1 2 3))")

[<Fact>]
let ``shape матрица → (2 2)`` () =
    Assert.Equal("(2 2)", pp "(shape '((1 2) (3 4)))")

[<Fact>]
let ``shape 3-тензор → (2 2 2)`` () =
    Assert.Equal("(2 2 2)", pp "(shape '(((1 2) (3 4)) ((5 6) (7 8))))")

[<Fact>]
let ``shape пустой список → (0)`` () =
    Assert.Equal("(0)", pp "(shape '())")

[<Fact>]
let ``shape объекта-тензора и rank-of`` () =
    Assert.Equal("(2 3)", pp "(shape (tensor '((1 2 3) (4 5 6))))")
    isInt 2I (evalStr "(rank-of (tensor '((1 2 3) (4 5 6))))")
    isInt 1I (evalStr "(rank-of '(a b c))")

// --- конструктор ---

[<Fact>]
let ``tensor строит объект типа tensor`` () =
    Assert.Equal("tensor", pp "(type-of (tensor '((1 2) (3 4))))")
    Assert.Equal("#t", pp "(tensor? (tensor '(1 2)))")

[<Fact>]
let ``tensor рваная форма → ошибка`` () =
    throws "(tensor '((1 2) (3)))"
    throws "(tensor '((1 2) 3))"
    throws "(tensor '())"
    throws "(tensor 5)"

[<Fact>]
let ``tensor идемпотентен и tensor->list обратен`` () =
    Assert.Equal("((1 2) (3 4))", ppl "(tensor (tensor '((1 2) (3 4))))")
    Assert.Equal("(((1 2) (3 4)) ((5 6) (7 8)))", ppl "(tensor '(((1 2) (3 4)) ((5 6) (7 8))))")

[<Fact>]
let ``make-tensor по функции индексов`` () =
    Assert.Equal("((0 1 2) (10 11 12))", ppl "(make-tensor '(2 3) (lambda (idx) (+ (* 10 (car idx)) (cadr idx))))")

[<Fact>]
let ``identity-matrix`` () =
    Assert.Equal("((1 0 0) (0 1 0) (0 0 1))", ppl "(identity-matrix 3)")

// --- tref ---

[<Fact>]
let ``tref вектор индекс 1 → 2`` () =
    isInt 2I (evalStr "(tref '(1 2 3) 1)")

[<Fact>]
let ``tref матрица один индекс → строка (подтензор)`` () =
    Assert.Equal("(3 4)", ppl "(tref '((1 2) (3 4)) 1)")

[<Fact>]
let ``tref матрица два индекса → элемент`` () =
    isInt 3I (evalStr "(tref '((1 2) (3 4)) 1 0)")

[<Fact>]
let ``tref 3-тензор глубокий индекс → элемент`` () =
    isInt 6I (evalStr "(tref '(((1 2) (3 4)) ((5 6) (7 8))) 1 0 1)")

[<Fact>]
let ``tref выход за границы, нецелый индекс, лишние индексы → ошибка`` () =
    throws "(tref '(1 2 3) 5)"
    throws "(tref '(1 2 3) -1)"
    throws "(tref '(1 2 3) 1.5)"
    throws "(tref '(1 2 3) 0 0)"

// --- transpose ---

[<Fact>]
let ``transpose по перестановке осей`` () =
    Assert.Equal("((1 4) (2 5) (3 6))", ppl "(transpose '((1 2 3) (4 5 6)) '(1 0))")
    // T[i][j][k] → R[k][i][j]
    Assert.Equal("(((1 3) (5 7)) ((2 4) (6 8)))",
                 ppl "(transpose '(((1 2) (3 4)) ((5 6) (7 8))) '(2 0 1))")
    throws "(transpose '((1 2) (3 4)) '(0 0))"

// --- outer ---

[<Fact>]
let ``outer скаляр × скаляр → произведение`` () =
    isInt 12I (evalStr "(outer 3 4)")

[<Fact>]
let ``outer вектор × вектор → матрица`` () =
    Assert.Equal("((3 4) (6 8))", ppl "(outer '(1 2) '(3 4))")

[<Fact>]
let ``outer вектор × скаляр → вектор`` () =
    Assert.Equal("(4 8 12)", ppl "(outer '(1 2 3) 4)")

[<Fact>]
let ``outer скаляр × матрица → масштабированная матрица`` () =
    Assert.Equal("((3 6) (9 12))", ppl "(outer 3 '((1 2) (3 4)))")

[<Fact>]
let ``outer матрица × вектор → 3-тензор`` () =
    Assert.Equal("(((5 6) (10 12)) ((15 18) (20 24)))", ppl "(outer '((1 2) (3 4)) '(5 6))")
    Assert.Equal("(2 2 2)", pp "(shape (outer '((1 2) (3 4)) '(5 6)))")

// --- contract ---

[<Fact>]
let ``contract 2×2 по 0 1 → след`` () =
    isInt 5I (evalStr "(contract '((1 2) (3 4)) 0 1)")

[<Fact>]
let ``contract 3×3 identity по 0 1 → 3`` () =
    isInt 3I (evalStr "(contract '((1 0 0) (0 1 0) (0 0 1)) 0 1)")

[<Fact>]
let ``contract 3-тензор по 0 2 → вектор (7 11)`` () =
    // result[k] = Σ_m T[m, k, m]: 1+6 = 7, 3+8 = 11
    Assert.Equal("(7 11)", ppl "(contract '(((1 2) (3 4)) ((5 6) (7 8))) 0 2)")

[<Fact>]
let ``contract несогласованные размерности и одинаковые индексы → ошибка`` () =
    throws "(contract '((1 2 3) (4 5 6)) 0 1)"
    throws "(contract '((1 2) (3 4)) 0 0)"
    throws "(contract '((1 2) (3 4)) 0 5)"

[<Fact>]
let ``contract символьный след`` () =
    Assert.Equal("(+ a d)", pp "(contract '((a b) (c d)) 0 1)")

// --- арифметика и упрощатель ---

[<Fact>]
let ``символьный вектор: сложение`` () =
    Assert.Equal("((+ a d) (+ b e) (+ c f))", ppl "(+ (tensor '(a b c)) (tensor '(d e f)))")

[<Fact>]
let ``символьный вектор: скаляр на вектор (* 'k v)`` () =
    Assert.Equal("((* a k) (* b k) (* c k))", ppl "(* 'k (tensor '(a b c)))")
    // справа — тот же результат
    Assert.Equal("((* a k) (* b k) (* c k))", ppl "(* (tensor '(a b c)) 'k)")

[<Fact>]
let ``dot символьных векторов`` () =
    Assert.Equal("(+ (* a d) (* b e) (* c f))", pp "(dot '(a b c) '(d e f))")
    Assert.Equal("(+ (* a d) (* b e) (* c f))", pp "(* (tensor '(a b c)) (tensor '(d e f)))")

[<Fact>]
let ``некоммутативность: A*B не равно B*A, оба по Dot`` () =
    let ab = ppl "(* (tensor '((a b) (c d))) (tensor '((e f) (g h))))"
    let ba = ppl "(* (tensor '((e f) (g h))) (tensor '((a b) (c d))))"
    Assert.NotEqual<string>(ab, ba)
    Assert.Equal("(((+ (* a e) (* b g)) (+ (* a f) (* b h))) ((+ (* c e) (* d g)) (+ (* c f) (* d h))))", ab)
    Assert.Equal("(((+ (* a e) (* c f)) (+ (* b e) (* d f))) ((+ (* a g) (* c h)) (+ (* b g) (* d h))))", ba)

[<Fact>]
let ``матрица × вектор и вектор × матрица`` () =
    Assert.Equal("(17 39)", ppl "(* (tensor '((1 2) (3 4))) (tensor '(5 6)))")
    Assert.Equal("(23 34)", ppl "(* (tensor '(5 6)) (tensor '((1 2) (3 4))))")
    // вектор × вектор — скаляр
    isInt 32I (evalStr "(* (tensor '(1 2 3)) (tensor '(4 5 6)))")

[<Fact>]
let ``несовпадение размерностей при Dot → ошибка`` () =
    throws "(* (tensor '((1 2 3))) (tensor '((1 2) (3 4))))"
    throws "(* (tensor '(1 2 3)) (tensor '(1 2)))"

[<Fact>]
let ``несовпадение форм при сложении → ошибка`` () =
    throws "(+ (tensor '(1 2)) (tensor '(1 2 3)))"
    throws "(+ (tensor '((1 2) (3 4))) (tensor '(1 2)))"

[<Fact>]
let ``степень матрицы: ^2, ^0, ^-1, ^-2`` () =
    Assert.Equal("((7 10) (15 22))", ppl "(^ (tensor '((1 2) (3 4))) 2)")
    Assert.Equal("((1 0) (0 1))", ppl "(^ (tensor '((1 2) (3 4))) 0)")
    Assert.Equal("((-2 1) (3/2 -1/2))", ppl "(^ (tensor '((1 2) (3 4))) -1)")
    Assert.Equal("((11/2 -5/2) (-15/4 7/4))", ppl "(^ (tensor '((1 2) (3 4))) -2)")
    Assert.Equal("((37 54) (81 118))", ppl "(^ (tensor '((1 2) (3 4))) 3)")

[<Fact>]
let ``степень символьной матрицы и не квадратной → ошибка`` () =
    Assert.Equal("(((+ (^ a 2) (* b c)) (+ (* a b) (* b d))) ((+ (* a c) (* c d)) (+ (^ d 2) (* b c))))",
                 ppl "(^ (tensor '((a b) (c d))) 2)")
    throws "(^ (tensor '((1 2 3) (4 5 6))) 2)"

[<Fact>]
let ``(- A A) → нулевой тензор той же формы`` () =
    Assert.Equal("((0 0) (0 0))", ppl "(- (tensor '((a b) (c d))) (tensor '((a b) (c d))))")
    Assert.Equal("(2 2)", pp "(shape (- (tensor '((a b) (c d))) (tensor '((a b) (c d)))))")

[<Fact>]
let ``(+ A A) → 2A`` () =
    Assert.Equal("((* 2 a) (* 2 b))", ppl "(+ (tensor '(a b)) (tensor '(a b)))")

[<Fact>]
let ``simplify (list '+ t1 t2) совпадает с (+ t1 t2)`` () =
    let viaSimplify = pp "(simplify (list '+ (tensor '((a b) (c d))) (tensor '((1 2) (3 4)))))"
    let viaEval = pp "(+ (tensor '((a b) (c d))) (tensor '((1 2) (3 4))))"
    Assert.Equal(viaEval, viaSimplify)
    Assert.Equal("[[(+ 1 a), (+ 2 b)], [(+ 3 c), (+ 4 d)]]", viaEval)

[<Fact>]
let ``simplify тензора — покомпонентно`` () =
    Assert.Equal("((+ 3 x) (* 2 y))", ppl "(simplify (tensor-from-flat '(2) (list '(+ x 1 2) '(+ y y))))")

[<Fact>]
let ``скаляр-выражение на тензор: (* (+ a b) v)`` () =
    Assert.Equal("((* x (+ a b)))", ppl "(* (+ 'a 'b) (tensor '(x)))")

// --- печать ---

[<Fact>]
let ``печать [[1, 2], [3, 4]]`` () =
    Assert.Equal("[[1, 2], [3, 4]]", Printer.prettyPrint (evalStr "(tensor '((1 2) (3 4)))"))
    Assert.Equal("[a, b, c]", Printer.prettyPrint (evalStr "(tensor '(a b c))"))
    Assert.Equal("[[[1, 2], [3, 4]], [[5, 6], [7, 8]]]",
                 Printer.prettyPrint (evalStr "(tensor '(((1 2) (3 4)) ((5 6) (7 8))))"))

[<Fact>]
let ``math-print тензора — компоненты через math-print`` () =
    Assert.Equal("[x^2, x - y]", MathPrinter.mathPrint (evalStr "(tensor-from-flat '(2) (list '(^ x 2) '(- x y)))"))
    match evalStr "(math-print (tensor-from-flat '(2) (list '(^ x 2) '(- x y))))" with
    | LispStr s -> Assert.Equal("[x^2, x - y]", s)
    | other -> Assert.Fail($"Ожидалась строка, получено {other}")

// --- diff / integrate ---

[<Fact>]
let ``diff 2-тензор — покомпонентно`` () =
    // (( x^2  x ) ( x^3  2x ))
    let r = tl "(diff 'x (tensor-from-flat '(2 2) (list '(^ x 2) 'x '(^ x 3) '(* 2 x))))"
    match r with
    | LispList [LispList [a; b]; LispList [c; d]] ->
        match a with
        | LispList [LispSym "*"; LispInteger n; LispSym "x"] -> Assert.Equal(2I, n)
        | other -> Assert.Fail($"Ожидался (* 2 x), получено {other}")
        isInt 1I b
        match c with
        | LispList [LispSym "*"; LispInteger n; LispList [LispSym "^"; LispSym "x"; LispInteger p]] ->
            Assert.Equal(3I, n)
            Assert.Equal(2I, p)
        | other -> Assert.Fail($"Ожидался (* 3 (^ x 2)), получено {other}")
        isInt 2I d
    | other -> Assert.Fail($"Ожидалась матрица 2×2, получено {other}")

[<Fact>]
let ``diff тензора с символьными компонентами`` () =
    Assert.Equal("((* a (cos x)) (* -1 (sin x)) (* 2 x))",
                 ppl "(diff 'x (tensor-from-flat '(3) (list '(* a (sin x)) '(cos x) '(^ x 2))))")
    // константы по x → 0
    Assert.Equal("(0 0)", ppl "(diff 'x (tensor '(a b)))")

[<Fact>]
let ``integrate тензора — покомпонентно`` () =
    Assert.Equal("((* 1/2 (^ x 2)) (* a x))", ppl "(integrate 'x (tensor '(x a)))")

// --- обычные списки больше не векторы ---

[<Fact>]
let ``обычный список не складывается и не масштабируется`` () =
    match evalStr "(simplify '(+ (1 2) (3 4)))" with
    | LispList (LispSym "+" :: _) -> ()
    | other -> Assert.Fail($"Ожидалось (+ ...), получено {other}")
    match evalStr "(simplify '(* 3 (1 2 3)))" with
    | LispList (LispSym "*" :: LispInteger n :: _) -> Assert.Equal(3I, n)
    | other -> Assert.Fail($"Ожидалось (* 3 ...), получено {other}")

[<Fact>]
let ``diff списка с головой-не-символом → 0, '(a b c) — вызов функции a`` () =
    isInt 0I (evalStr "(diff 'x '(1 2 3))")
    isInt 0I (evalStr "(diff 'x '(a b c))")

// --- Шаг 15a: подсписки-выражения как компоненты ---

[<Fact>]
let ``tensor: подсписок-выражение с оператором — компонента`` () =
    Assert.Equal("(x (^ x 2))", ppl "(tensor (list 'x '(^ x 2)))")
    Assert.Equal("(2)", pp "(shape (tensor (list 'x '(^ x 2))))")

[<Fact>]
let ``tensor: diff вектора с компонентой-выражением`` () =
    Assert.Equal("(1 (* 2 x))", ppl "(diff 'x (tensor (list 'x '(^ x 2))))")

[<Fact>]
let ``tensor: подсписки с головой-функцией (sin, cos) — вектор, а не матрица`` () =
    Assert.Equal("(2)", pp "(shape (tensor '((sin x) (cos x))))")
    isInt 1I (evalStr "(rank-of (tensor '((sin x) (cos x))))")

[<Fact>]
let ``tensor: несвязанные символы — по-прежнему вектор и матрица`` () =
    Assert.Equal("(3)", pp "(shape (tensor '(a b c)))")
    Assert.Equal("(2 2)", pp "(shape (tensor '((a b) (c d))))")

[<Fact>]
let ``tensor: пользовательская функция в голове подсписка — компонента`` () =
    evalStr "(define (my-fn-15a u) u)" |> ignore
    Assert.Equal("(2)", pp "(shape (tensor '((my-fn-15a x) (my-fn-15a y))))")

[<Fact>]
let ``bound? и fbound?`` () =
    Assert.Equal("#t", pp "(fbound? 'sin)")
    Assert.Equal("#f", pp "(fbound? 'unbound-sym-15a)")
    evalStr "(define var-15a 5)" |> ignore
    Assert.Equal("#t", pp "(bound? 'var-15a)")
    Assert.Equal("#f", pp "(fbound? 'var-15a)")
