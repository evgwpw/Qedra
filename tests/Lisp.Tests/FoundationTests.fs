// Тесты фундамента Lisp (Шаг 15): символьная арифметика, неявный begin, &rest,
// новые builtins и функции prelude
module FoundationTests

open Xunit
open Types
open Reader
open Evaluator

let evalStr (s: string) : LispValue =
    readAll s |> List.head |> fun e -> eval e globalEnv

let pp (s: string) : string = Printer.prettyPrint (evalStr s)

let throws (s: string) =
    Assert.ThrowsAny<System.Exception>(fun () -> evalStr s |> ignore) |> ignore

// --- Символьная арифметика ---

[<Fact>]
let ``(+ 'a 1) → (+ 1 a)`` () = Assert.Equal("(+ 1 a)", pp "(+ 'a 1)")

[<Fact>]
let ``(* 2 'x 'x) → (* 2 (^ x 2))`` () = Assert.Equal("(* 2 (^ x 2))", pp "(* 2 'x 'x)")

[<Fact>]
let ``символьные - / ^`` () =
    Assert.Equal("(+ a (* -1 b))", pp "(- 'a 'b)")
    Assert.Equal("(* -1 x)", pp "(- 'x)")
    Assert.Equal("(* a (^ b -1))", pp "(/ 'a 'b)")
    Assert.Equal("(^ x 3)", pp "(^ 'x 3)")

[<Fact>]
let ``числовая арифметика без изменений`` () =
    Assert.Equal("7", pp "(+ 3 4)")
    Assert.Equal("1/3", pp "(/ 1 3)")
    Assert.Equal("1024", pp "(^ 2 10)")
    Assert.Equal("0", pp "(+)")
    Assert.Equal("1", pp "(*)")
    Assert.Equal("-5", pp "(- 5)")

[<Fact>]
let ``алгебраические числа по-прежнему считаются численно`` () =
    // (sqrt 2)*(sqrt 2) = 2 через override алгебраической арифметики
    Assert.Equal("2", pp "(* (sqrt 2) (sqrt 2))")

[<Fact>]
let ``сравнения на символах — ошибка`` () =
    throws "(< 'a 1)"
    throws "(= 'a 'b)"

// --- Неявный begin ---

[<Fact>]
let ``define с несколькими выражениями в теле`` () =
    evalStr "(define (two-steps x) (define tmp (* x 2)) (+ tmp 1))" |> ignore
    Assert.Equal("11", pp "(two-steps 5)")

[<Fact>]
let ``lambda, let, let*, letrec с несколькими выражениями`` () =
    Assert.Equal("3", pp "((lambda (x) (+ x 1) (+ x 2)) 1)")
    Assert.Equal("6", pp "(let ((a 1)) (define b 2) (+ a b 3))")
    Assert.Equal("5", pp "(let* ((a 1) (b (+ a 1))) (+ a 0) (+ a b 2))")
    Assert.Equal("120", pp "(letrec ((f (lambda (n) (if (= n 0) 1 (* n (f (- n 1))))))) (f 3) (f 5))")

[<Fact>]
let ``defmacro и defmethod с несколькими выражениями`` () =
    evalStr "(defmacro (twice-m x) (define y x) (list '* 2 y))" |> ignore
    Assert.Equal("14", pp "(twice-m 7)")
    evalStr "(deftype 'foo15 'any)" |> ignore
    evalStr "(defmethod print (foo15) (o) (define s \"foo\") (string-append s \"!\"))" |> ignore
    Assert.Equal("foo!", pp "(make-object 'foo15 1)")

[<Fact>]
let ``хвостовая позиция в многотельной функции — TCO`` () =
    evalStr "(define (count-down n acc) (define m (- n 1)) (if (< n 1) acc (count-down m (+ acc 1))))" |> ignore
    Assert.Equal("100000", pp "(count-down 100000 0)")

[<Fact>]
let ``пустое тело — ошибка синтаксиса`` () =
    throws "(define (g x))"
    throws "(lambda (x))"

// --- &rest ---

[<Fact>]
let ``&rest собирает остаток аргументов`` () =
    evalStr "(define (rest-test a &rest r) (list a r))" |> ignore
    Assert.Equal("(1 (2 3))", pp "(rest-test 1 2 3)")
    Assert.Equal("(1 ())", pp "(rest-test 1)")
    throws "(rest-test)"

// --- Новые builtins ---

[<Fact>]
let ``length`` () =
    Assert.Equal("3", pp "(length '(1 2 3))")
    Assert.Equal("0", pp "(length '())")
    Assert.Equal("2", pp "(length #(1 2))")
    throws "(length 5)"

[<Fact>]
let ``append n-арный`` () =
    Assert.Equal("(1 2 3 4 5)", pp "(append '(1 2) '(3) '() '(4 5))")
    Assert.Equal("nil", pp "(append)")
    Assert.Equal("(1)", pp "(append '(1))")
    throws "(append '(1) 2)"

[<Fact>]
let ``apply`` () =
    Assert.Equal("6", pp "(apply + '(1 2 3))")
    Assert.Equal("(+ 1 a)", pp "(apply + (list 1 'a))")
    Assert.Equal("9", pp "(apply (lambda (x y) (* x y)) '(3 3))")

[<Fact>]
let ``error бросает исключение с сообщением`` () =
    let ex = Assert.ThrowsAny<System.Exception>(fun () -> evalStr "(error \"плохо:\" 'x '(1 2))" |> ignore)
    Assert.Equal("плохо: x (1 2)", ex.Message)

[<Fact>]
let ``предикаты number? symbol? list? integer?`` () =
    Assert.Equal("(#t #f #f #t)", pp "(list (number? 1.5) (number? 'a) (symbol? 5) (symbol? 'a))")
    Assert.Equal("(#t #t #f #t #f)", pp "(list (list? '(1)) (list? '()) (list? 5) (integer? 3) (integer? 3.0))")

[<Fact>]
let ``cadr caddr nth`` () =
    Assert.Equal("2", pp "(cadr '(1 2 3))")
    Assert.Equal("3", pp "(caddr '(1 2 3))")
    Assert.Equal("c", pp "(nth '(a b c) 2)")
    Assert.Equal("a", pp "(nth '(a b c) 0)")
    throws "(nth '(a b c) 3)"
    throws "(nth '(a b c) -1)"

// --- prelude ---

[<Fact>]
let ``map filter foldl reverse range`` () =
    Assert.Equal("(1 4 9)", pp "(map (lambda (x) (* x x)) '(1 2 3))")
    Assert.Equal("(2 4)", pp "(filter (lambda (x) (= (mod x 2) 0)) '(1 2 3 4))")
    Assert.Equal("10", pp "(foldl + 0 '(1 2 3 4))")
    Assert.Equal("(3 2 1)", pp "(reverse '(1 2 3))")
    Assert.Equal("(0 1 2 3)", pp "(range 4)")
    Assert.Equal("()", pp "(range 0)")
    Assert.Equal("(10 20)", pp "(map2 + '(1 2) '(9 18))")

[<Fact>]
let ``every? any?`` () =
    Assert.Equal("#t", pp "(every? number? '(1 2 3))")
    Assert.Equal("#f", pp "(every? number? '(1 a 3))")
    Assert.Equal("#t", pp "(every? number? '())")
    Assert.Equal("#t", pp "(any? symbol? '(1 a 3))")
    Assert.Equal("#f", pp "(any? symbol? '(1 2))")

[<Fact>]
let ``map по большому списку не переполняет стек`` () =
    Assert.Equal("5000", pp "(length (map (lambda (x) x) (range 5000)))")

[<Fact>]
let ``lib-dir задан, prelude загружен`` () =
    Assert.Equal("#t", pp "prelude-loaded")
    Assert.Equal("#t", pp "(tensor? (tensor '(1)))")
