// Тесты предкомпиляции (Шаг 17b, Compiler.fs): лексическая адресация, замыкания, внутренние define,
// глобальные ячейки, макросы при компиляции, TCO, стек кадров, trace
module CompilerTests

open System.IO
open Xunit
open Types
open Reader
open Evaluator

// Выполнить все формы строки в окружении; результат последней
let run (env: Env) (s: string) : LispValue =
    readAll s |> List.fold (fun _ e -> eval e env) LispNil

let pp (env: Env) (s: string) : string = Printer.prettyPrint (run env s)

// Свежее окружение + выражение → печатное значение
let ev (s: string) : string = pp (newEnv ()) s

let failure (env: Env) (s: string) : string * Frame list =
    try
        run env s |> ignore
        failwith "ожидалась ошибка"
    with
    | LispError (m, st, _) -> (m, st)

let names (st: Frame list) = st |> List.map (fun f -> f.Name)

// --- Лексическая адресация и замыкания ---

[<Fact>]
let ``замыкание-счётчик: set! меняет захваченную переменную`` () =
    let env = newEnv ()
    run env "(define (make-counter) (let ((n 0)) (lambda () (set! n (+ n 1)) n)))" |> ignore
    run env "(define c1 (make-counter)) (define c2 (make-counter))" |> ignore
    Assert.Equal("1", pp env "(c1)")
    Assert.Equal("2", pp env "(c1)")
    Assert.Equal("3", pp env "(c1)")
    // второй счётчик независим
    Assert.Equal("1", pp env "(c2)")
    Assert.Equal("4", pp env "(c1)")

[<Fact>]
let ``замыкание захватывает параметр, глубина больше одного`` () =
    Assert.Equal("(8 9)", ev "(define (adder a) (lambda (b) (lambda (c) (+ a b c)))) (list (((adder 1) 3) 4) (((adder 2) 3) 4))")

[<Fact>]
let ``каждый вызов рекурсии получает свои привязки let`` () =
    // замыкания, созданные в разных вызовах, видят свои значения m
    Assert.Equal("(3 2 1)",
                 ev "(define (build n) (if (= n 0) '() (cons (let ((m n)) (lambda () m)) (build (- n 1)))))
                     (map (lambda (f) (f)) (build 3))")

[<Fact>]
let ``затенение: внутренний let и параметр`` () =
    Assert.Equal("(2 1 5)", ev "(define x 5) (define (f x) (let ((x (+ x 1))) (list x (- x 1) ))) (append (f 1) (list x))")

[<Fact>]
let ``let* видит предыдущие, let — нет (внешние значения)`` () =
    // let*: b = 2+1 = 3; let: b = внешнее a = 1, итого 2+1 = 3, а не 2+2
    Assert.Equal("(3 3)", ev "(define a 1) (list (let* ((a 2) (b (+ a 1))) b) (let ((a 2) (b a)) (+ a b)))")
    Assert.Equal("5", ev "(define a 1) (let ((a 2) (b a)) (+ a b a))")

[<Fact>]
let ``letrec: взаимная рекурсия`` () =
    Assert.Equal("(#t #f)",
                 ev "(letrec ((ev? (lambda (n) (if (= n 0) #t (od? (- n 1))))) (od? (lambda (n) (if (= n 0) #f (ev? (- n 1)))))) (list (ev? 10) (ev? 7)))")

[<Fact>]
let ``set! глобальной переменной из замыкания`` () =
    let env = newEnv ()
    run env "(define total 0) (define (add! k) (set! total (+ total k)))" |> ignore
    run env "(add! 5) (add! 7)" |> ignore
    Assert.Equal("12", pp env "total")

[<Fact>]
let ``set! несуществующей переменной — ошибка`` () =
    let env = newEnv ()
    let msg, _ = failure env "(set! no-such-var-xyz 1)"
    Assert.Contains("не определена", msg)

[<Fact>]
let ``неизвестный символ — ошибка при чтении`` () =
    let env = newEnv ()
    let msg, _ = failure env "(define (f) zzz-unknown) (f)"
    Assert.Equal("Неизвестный символ: zzz-unknown", msg)

// --- Внутренние define ---

[<Fact>]
let ``внутренние define: взаимная рекурсия (letrec*)`` () =
    Assert.Equal("(#t #f)",
                 ev "(define (parity n)
                       (define (ev? k) (if (= k 0) #t (od? (- k 1))))
                       (define (od? k) (if (= k 0) #f (ev? (- k 1))))
                       (list (ev? n) (od? n)))
                     (parity 10)")

[<Fact>]
let ``внутренний define не протекает в глобальную область`` () =
    let env = newEnv ()
    run env "(define (f) (define hidden-local 42) (+ hidden-local 1))" |> ignore
    Assert.Equal("43", pp env "(f)")
    Assert.Equal("#f", pp env "(bound? 'hidden-local)")

[<Fact>]
let ``define внутри let — локальный, define на верхнем уровне begin — глобальный`` () =
    let env = newEnv ()
    run env "(let ((a 1)) (define inner-only (+ a 1)) inner-only)" |> ignore
    Assert.Equal("#f", pp env "(bound? 'inner-only)")
    run env "(begin (define top-from-begin 7))" |> ignore
    Assert.Equal("7", pp env "top-from-begin")

[<Fact>]
let ``внутренний define: чтение до определения — неизвестный символ`` () =
    let env = newEnv ()
    let msg, _ = failure env "(define (f) (define a b) (define b 1) a) (f)"
    Assert.Equal("Неизвестный символ: b", msg)

// --- Глобальные ячейки ---

[<Fact>]
let ``переопределение глобальной функции после компиляции вызывающей`` () =
    let env = newEnv ()
    run env "(define (helper x) (* x 2)) (define (caller x) (+ 1 (helper x)))" |> ignore
    Assert.Equal("11", pp env "(caller 5)")
    run env "(define (helper x) (* x 100))" |> ignore
    Assert.Equal("501", pp env "(caller 5)")
    run env "(set! helper (lambda (x) 0))" |> ignore
    Assert.Equal("1", pp env "(caller 5)")

[<Fact>]
let ``функция вызывает ещё не определённую: ошибка, затем работает после define`` () =
    let env = newEnv ()
    run env "(define (early) (late-defined 3))" |> ignore
    let msg, st = failure env "(early)"
    Assert.Equal("Неизвестный символ: late-defined", msg)
    Assert.Equal<string list>([ "early" ], names st)
    run env "(define (late-defined x) (* x x))" |> ignore
    Assert.Equal("9", pp env "(early)")

[<Fact>]
let ``define значения-лямбды даёт ей имя`` () =
    let env = newEnv ()
    Assert.Equal("#<функция sq>", pp env "(define sq (lambda (x) (* x x))) sq")

[<Fact>]
let ``дочернее окружение: define не загрязняет глобальное, глобальные видны`` () =
    let child = globalEnv.Extend []
    run child "(define only-in-child 5)" |> ignore
    Assert.Equal("6", pp child "(+ only-in-child 1)")
    Assert.False(globalEnv.Lookup("only-in-child").IsSome)

// --- Макросы ---

[<Fact>]
let ``макрос определён после функции, но до её первого вызова`` () =
    let env = newEnv ()
    run env "(define (use-it x) (my-late-macro x))" |> ignore
    run env "(defmacro (my-late-macro e) `(+ ,e 100))" |> ignore
    Assert.Equal("105", pp env "(use-it 5)")

[<Fact>]
let ``переопределение макроса после компиляции использующей функции не перераскрывает её`` () =
    // задокументированное ограничение: тело функции раскрыто при первом вызове
    let env = newEnv ()
    run env "(defmacro (mm e) `(+ ,e 1)) (define (u x) (mm x))" |> ignore
    Assert.Equal("6", pp env "(u 5)")
    run env "(defmacro (mm e) `(+ ,e 1000))" |> ignore
    Assert.Equal("6", pp env "(u 5)")
    Assert.Equal("1005", pp env "(mm 5)")

[<Fact>]
let ``макрос, определённый внутри той же формы, раскрывается на лету`` () =
    Assert.Equal("(11 12)", ev "(begin (defmacro (inc2 e) `(+ ,e 2)) (list (inc2 9) (inc2 10)))")

[<Fact>]
let ``локальный макрос и макрос-значение переменной`` () =
    Assert.Equal("7", ev "(define (f) (defmacro (twice e) `(* 2 ,e)) (+ (twice 3) 1)) (f)")

[<Fact>]
let ``макрос с &rest и квазицитированием со вклейкой`` () =
    Assert.Equal("(1 2 3)", ev "(defmacro (mk-list &rest xs) `(list ,@xs)) (mk-list 1 2 3)")

[<Fact>]
let ``макрос в хвостовой позиции сохраняет TCO`` () =
    Assert.Equal("done", ev "(defmacro (my-if c a b) `(cond (,c ,a) (else ,b)))
                              (define (loop n) (my-if (= n 0) 'done (loop (- n 1))))
                              (loop 300000)")

// --- TCO ---

[<Fact>]
let ``TCO: if, 10^6 итераций`` () =
    Assert.Equal("done", ev "(define (loop n) (if (= n 0) 'done (loop (- n 1)))) (loop 1000000)")

[<Fact; Trait("Category", "Slow")>]
let ``TCO: cond, case, and, or, let, begin в хвостовой позиции`` () =
    let env = newEnv ()
    run env "(define (c n) (cond ((= n 0) 'ok) (else (c (- n 1)))))" |> ignore
    run env "(define (k n) (case n ((0) 'ok) (else (k (- n 1)))))" |> ignore
    run env "(define (a n) (and #t (if (= n 0) 'ok (a (- n 1)))))" |> ignore
    run env "(define (o n) (or #f (if (= n 0) 'ok (o (- n 1)))))" |> ignore
    run env "(define (l n) (let ((m (- n 1))) (if (< n 1) 'ok (l m))))" |> ignore
    run env "(define (b n) (begin 1 (if (= n 0) 'ok (b (- n 1)))))" |> ignore
    for f in [ "c"; "k"; "a"; "o"; "l"; "b" ] do
        Assert.Equal("ok", pp env (sprintf "(%s 1000000)" f))

[<Fact>]
let ``TCO: взаимная хвостовая рекурсия`` () =
    Assert.Equal("#t", ev "(define (ev? n) (if (= n 0) #t (od? (- n 1)))) (define (od? n) (if (= n 0) #f (ev? (- n 1)))) (ev? 1000000)")

[<Fact>]
let ``нехвостовая рекурсия по-прежнему работает`` () =
    Assert.Equal("5050", ev "(define (s n) (if (= n 0) 0 (+ n (s (- n 1))))) (s 100)")

// --- Стек кадров после компиляции ---

[<Fact>]
let ``стек ошибки: имена и аргументы кадров как раньше`` () =
    let env = newEnv ()
    run env "(define (a x) (+ 1 (b x))) (define (b x) (+ 1 (c x))) (define (c x) (car x))" |> ignore
    let msg, st = failure env "(a 5)"
    Assert.Equal("car: ожидается список, получено 5", msg)
    Assert.Equal<string list>([ "car"; "c"; "b"; "a" ], names st)
    Assert.Equal<string list>([ "5" ], st.Head.Args |> List.map Printer.prettyPrint)

[<Fact>]
let ``стек ошибки: хвостовой вызов заменяет кадр`` () =
    let env = newEnv ()
    run env "(define (a x) (b x)) (define (b x) (c x)) (define (c x) (car x))" |> ignore
    let _, st = failure env "(a 5)"
    Assert.Equal<string list>([ "car"; "c" ], names st)

[<Fact>]
let ``стек ошибки: &rest показывает исходные аргументы`` () =
    let env = newEnv ()
    run env "(define (f a &rest r) (car a))" |> ignore
    let _, st = failure env "(f 1 2 3)"
    Assert.Equal<string list>([ "car"; "f" ], names st)
    Assert.Equal<string list>([ "1"; "2"; "3" ], st.[1].Args |> List.map Printer.prettyPrint)

[<Fact>]
let ``неверное число аргументов — ошибка со стеком вызванной функции`` () =
    let env = newEnv ()
    run env "(define (two a b) a)" |> ignore
    let msg, st = failure env "(two 1)"
    Assert.Equal("Функция ожидает 2 аргументов, получено 1", msg)
    Assert.Equal<string list>([ "two" ], names st)

[<Fact>]
let ``&rest собирает остаток; пустой остаток`` () =
    Assert.Equal("(1 (2 3) 4 ())", ev "(define (f a &rest r) r) (list (car (list 1)) (f 0 2 3) 4 (f 0))")

[<Fact>]
let ``ошибка внутри хвостового вызова: глубина стека не теряется`` () =
    let env = newEnv ()
    run env "(define (f n) (if (= n 0) (car 7) (f (- n 1))))" |> ignore
    let _, st = failure env "(f 1000)"
    Assert.Equal<string list>([ "car"; "f" ], names st)

// --- trace и профилирование на скомпилированных функциях ---

let withOutput (f: unit -> unit) : string =
    let w = new StringWriter()
    Debug.writer <- w
    try f ()
    finally
        Debug.untraceAll ()
        Debug.writer <- null
    w.ToString().Replace("\r\n", "\n")

[<Fact>]
let ``trace скомпилированной функции: вызов без TCO, результат показан`` () =
    let env = newEnv ()
    run env "(define (fact n) (if (= n 0) 1 (* n (fact (- n 1)))))" |> ignore
    let out = withOutput (fun () -> run env "(trace 'fact) (fact 2)" |> ignore)
    Assert.Equal("→ (fact 2)\n  → (fact 1)\n    → (fact 0)\n    ← fact = 1\n  ← fact = 1\n← fact = 2\n", out)

[<Fact>]
let ``trace функции, вызванной в хвостовой позиции`` () =
    let env = newEnv ()
    run env "(define (g x) (* x 3)) (define (f x) (g x))" |> ignore
    let out = withOutput (fun () -> run env "(trace 'g) (f 2)" |> ignore)
    Assert.Equal("→ (g 2)\n← g = 6\n", out)

[<Fact>]
let ``trace-methods на методах`` () =
    let env = newEnv ()
    // уникальные имена: таблица типов и методов глобальна
    run env "(deftype 'cmpAnimal 'any) (deftype 'cmpDog 'cmpAnimal) (defmethod cmpSpeak (cmpAnimal) (a) 'generic) (defmethod cmpSpeak (cmpDog) (d) 'woof)" |> ignore
    let out = withOutput (fun () -> run env "(trace-methods 'cmpSpeak) (apply (find-method 'cmpSpeak '(cmpDog)) (list (make-object 'cmpDog)))" |> ignore)
    Assert.StartsWith("→ (cmpSpeak(cmpDog)", out)
    Assert.Contains("← cmpSpeak(cmpDog) = woof", out)

[<Fact>]
let ``untrace возвращает TCO`` () =
    let env = newEnv ()
    run env "(define (loop n) (if (= n 0) 'done (loop (- n 1))))" |> ignore
    withOutput (fun () -> run env "(trace 'loop) (untrace 'loop)" |> ignore) |> ignore
    Assert.Equal("done", pp env "(loop 500000)")

// --- try / unwind-protect / quasiquote / defrule на компиляторе ---

[<Fact>]
let ``try и unwind-protect: ошибка, очистка, значение`` () =
    let env = newEnv ()
    run env "(define ulog '())" |> ignore
    Assert.Equal("caught", pp env "(try (unwind-protect (car 5) (set! ulog (cons 'cleanup ulog))) (lambda (e) 'caught))")
    Assert.Equal("(cleanup)", pp env "ulog")

[<Fact>]
let ``квазицитирование: вложенное и вклейка`` () =
    Assert.Equal("(a 3 4 5 b)", ev "(define xs '(3 4 5)) `(a ,@xs b)")
    Assert.Equal("(1 (quasiquote (x (unquote y) (unquote 2))))", ev "(define y 'q) `(1 `(x ,y ,,(+ 1 1)))" |> fun s -> if s.Contains "unquote" then s else s)

[<Fact>]
let ``условие defrule видит переменные образца и глобальные`` () =
    let env = newEnv ()
    run env "(define limit-for-rule 10)" |> ignore
    run env "(defrule cmp-big-rule (cmp-big ?x) (big ?x) (> ?x limit-for-rule))" |> ignore
    try
        Assert.Equal("(big 50)", pp env "(simplify '(cmp-big 50))")
        Assert.Equal("(cmp-big 3)", pp env "(simplify '(cmp-big 3))")
        run env "(set! limit-for-rule 1)" |> ignore
        Assert.Equal("(big 3)", pp env "(simplify '(cmp-big 3))")
    finally
        Rules.remove "cmp-big-rule" |> ignore

[<Fact>]
let ``apply и map вызывают скомпилированные функции`` () =
    Assert.Equal("(6 10)", ev "(define (add3 a b c) (+ a b c)) (list (apply add3 '(1 2 3)) (apply add3 (map (lambda (x) (* x 2)) '(1 1 3))))")

[<Fact>]
let ``эталонный пример: fib 20`` () =
    Assert.Equal("6765", ev "(define (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))))) (fib 20)")

// --- Шаг 21e: быстрые входы builtin с 1–2 аргументами ---

[<Fact>]
let ``быстрые builtin: результаты как у обычного вызова`` () =
    let env = newEnv ()
    let cases =
        [ "(car '(1 2))", "1"; "(cdr '(1 2))", "(2)"; "(cdr '(1))", "()"; "(cons 1 '(2))", "(1 2)"; "(cons 1 2)", "(1 . 2)"
          "(cadr '(1 2 3))", "2"; "(list 1)", "(1)"; "(list 1 2)", "(1 2)"; "(null? '())", "#t"; "(not 5)", "#f"
          "(pair? '(1))", "#t"; "(+ 1 2)", "3"; "(+ 1.5 2)", "3.5"; "(+ 1/2 1/3)", "5/6"; "(+ 'a 1)", "(+ 1 a)"
          "(- 5 8)", "-3"; "(* 4 5)", "20"; "(< 1 2)", "#t"; "(< 1 2.5)", "#t"; "(<= 2 2)", "#t"; "(>= 1 2)", "#f"
          "(= 3 3)", "#t"; "(mod 7 3)", "1"; "(equal? '(1 2) '(1 2))", "#t"; "(vref (vector 1 2 3) 1)", "2" ]
    for (src, expected) in cases do
        Assert.Equal(expected, pp env src)
    // ошибки и сообщения — как раньше (идут через обычный builtin)
    let (m1, st1) = failure env "(car 5)"
    Assert.Contains("car", m1)
    Assert.Equal<string list>(["car"], names st1)
    let (m2, _) = failure env "(mod 5 0)"
    Assert.Contains("деление на ноль", m2)
    let (m3, _) = failure env "(vref (vector 1 2) 5)"
    Assert.Contains("вне границ", m3)
    let (m4, _) = failure env "(< 'a 1)"
    Assert.NotEmpty(m4)

[<Fact>]
let ``быстрые builtin: поздняя привязка — переопределение car и + видно сразу`` () =
    let env = newEnv ()
    run env "(define (f x) (car x))" |> ignore
    Assert.Equal("1", pp env "(f '(1 2))")
    // LANG.1: define поверх builtin — ошибка; явный путь переопределения — set! (поздняя привязка та же)
    run env "(set! car (lambda (x) 'mine))" |> ignore
    Assert.Equal("mine", pp env "(f '(1 2))")
    run env "(define (g a b) (+ a b))" |> ignore
    Assert.Equal("5", pp env "(g 2 3)")
    run env "(set! + (lambda (a b) 'plus))" |> ignore
    Assert.Equal("plus", pp env "(g 2 3)")
    // другое окружение не затронуто
    Assert.Equal("1", pp (newEnv ()) "(car '(1 2))")

[<Fact>]
let ``быстрые builtin: кадр стека при ошибке и trace`` () =
    let env = newEnv ()
    run env "(define (f x) (car x))" |> ignore
    let (_, st) = failure env "(f 5)"
    Assert.Equal<string list>(["car"; "f"], names st)
    // trace builtin: вызов идёт через хук, а не быстрый путь
    let out = withOutput (fun () -> run env "(trace 'car) (car '(1 2))" |> ignore)
    Assert.Contains("→ (car (1 2))", out)
    Assert.Contains("← car = 1", out)

// Шаг 21i' (c): малые целые — арифметика на int64 для значений int32, переход через границы int32/int64 в обе стороны
[<Fact>]
let ``малые целые: границы int32 и int64, + - * сравнения`` () =
    FastBuiltins.checkBigIntegerLayout ()
    let env = newEnv ()
    run env "(define (ad a b) (+ a b)) (define (sb a b) (- a b)) (define (ml a b) (* a b)) (define (lt a b) (< a b)) (define (eq a b) (= a b)) (define (gt a b) (> a b)) (define (le a b) (<= a b)) (define (mx a b) (max a b))" |> ignore
    let vals =
        [ 0L; 1L; -1L; 2L; 65536L; 2147483646L; 2147483647L; 2147483648L; 4294967296L; 3037000500L
          -2147483647L; -2147483648L; -2147483649L; -4294967296L
          System.Int64.MaxValue; System.Int64.MinValue; System.Int64.MaxValue - 1L ]
        |> List.map bigint
    let big = [ bigint.Pow(bigint 10, 30); -(bigint.Pow(bigint 10, 30)) ]
    let all = vals @ big @ (vals |> List.map (fun v -> v * bigint 4)) @ (vals |> List.map (fun v -> v * v))
    for a in all do
        for b in all do
            let sa, sb = a.ToString(), b.ToString()
            let chk name (expected: string) = Assert.Equal(expected, pp env (sprintf "(%s %s %s)" name sa sb))
            chk "ad" ((a + b).ToString())
            chk "sb" ((a - b).ToString())
            chk "ml" ((a * b).ToString())
            chk "lt" (if a < b then "#t" else "#f")
            chk "gt" (if a > b then "#t" else "#f")
            chk "le" (if a <= b then "#t" else "#f")
            chk "eq" (if a = b then "#t" else "#f")
            chk "mx" ((if a >= b then a else b).ToString())
    // явные границы
    Assert.Equal("2147483648", pp env "(ad 2147483647 1)")
    Assert.Equal("-2147483649", pp env "(sb -2147483648 1)")
    Assert.Equal("9223372036854775808", pp env "(ad 9223372036854775807 1)")
    Assert.Equal("-9223372036854775809", pp env "(sb -9223372036854775808 1)")
    Assert.Equal("9223372037000250000", pp env "(ml 3037000500 3037000500)")
    Assert.Equal("#t", pp env "(eq (ad 2147483647 1) 2147483648)")
    // результат, вернувшийся в малый диапазон из большого, равен малому
    Assert.Equal("#t", pp env "(eq (sb (ad 2147483647 5) 5) 2147483647)")

// Шаг 21i' (a): узлы-примитивы (Prim1Node / Prim2Node) — операция берётся по builtin в ячейке, а не по имени
[<Fact>]
let ``узлы-примитивы: псевдоним builtin, локальное имя, несвязанное имя`` () =
    let env = newEnv ()
    run env "(set! car cdr) (define (f x) (car x))" |> ignore
    Assert.Equal("(2 3)", pp env "(f '(1 2 3))")
    Assert.Equal("(2)", ev "(let ((car cdr)) (car '(1 2)))")
    Assert.Equal("(#t #t #f #f)", ev "(list (null? '()) (null? (cdr '(1))) (null? '(1 . 2)) (null? 0))")
    Assert.Equal("(1 2)", ev "(list (car '(1 . 2)) (cdr '(1 . 2)))")
    let (m0, st0) = failure env "(cdr '())"
    Assert.Contains("cdr", m0)
    Assert.Equal<string list>(["cdr"], names st0)
    let env2 = newEnv ()
    run env2 "(define (g x) (later x))" |> ignore
    let (m, _) = failure env2 "(g 1)"
    Assert.Contains("later", m)
    run env2 "(define later car)" |> ignore
    Assert.Equal("1", pp env2 "(g '(1 2))")

// Шаг 21i' (d): equal? (structEqual) на целых (малых/больших), рациональных и смешанных значениях — прямое BigInteger.Equals
[<Fact>]
let ``equal?: малые, большие, рациональные и смешанные значения`` () =
    let env = newEnv ()
    let ev s = pp env s
    Assert.Equal("#t", ev "(equal? '(3 1 4 1 5 9) (list 3 1 4 1 5 9))")
    Assert.Equal("#f", ev "(equal? '(3 1 4 1 5 9) (list 3 1 4 1 5 8))")
    Assert.Equal("#t", ev "(equal? 2147483648 (+ 2147483647 1))")
    Assert.Equal("#f", ev "(equal? 2147483648 2147483647)")
    Assert.Equal("#t", ev "(equal? (* 100000000000000000000 3) 300000000000000000000)")
    Assert.Equal("#f", ev "(equal? 100000000000000000000 -100000000000000000000)")
    Assert.Equal("#t", ev "(equal? (/ 1 3) (/ 2 6))")
    Assert.Equal("#f", ev "(equal? (/ 1 3) (/ 1 2))")
    Assert.Equal("#f", ev "(equal? (/ 1 3) (/ 2 3))")
    Assert.Equal("#f", ev "(equal? 1 (/ 1 2))")
    Assert.Equal("#f", ev "(equal? 1 1.0)")
    Assert.Equal("#t", ev "(equal? (list 1 (/ 1 2) 100000000000000000000 \"s\" 'a) (list 1 (/ 1 2) 100000000000000000000 \"s\" 'a))")
    Assert.Equal("#t", ev "(equal? (vector 1 2 (/ 3 4)) (vector 1 2 (/ 3 4)))")
    // индексы вектора и nth: границы
    Assert.Equal("#f", ev "(equal? (nth '(1 2 3) 2) 2)")
    Assert.Equal("30", ev "(vref (vector 10 20 30) 2)")
    Assert.Contains("вне границ", fst (failure env "(vref (vector 1 2) 2)"))
    Assert.Contains("вне границ", fst (failure env "(nth '(1 2) -1)"))

// Шаг 21i' (d): профилирование не выключает глубину хвостовой рекурсии для bench-режима (лимит поднят) — здесь проверяем,
// что глубокая хвостовая рекурсия под (profile ...) проходит при поднятом maxDepth
[<Fact>]
let ``profile: глубокая хвостовая рекурсия при поднятом лимите глубины`` () =
    let env = newEnv ()
    let saved = Debug.maxDepth
    try
        Debug.maxDepth <- 2000000
        run env "(define (cnt n) (if (= n 0) 0 (cnt (- n 1))))" |> ignore
        // при обычном лимите (20000) под профилем 40000 вложенных вызовов — ошибка глубины; при поднятом — проходит
        Debug.maxDepth <- 20000
        Assert.Contains("глубина", fst (failure env "(profile (cnt 40000))"))
        Debug.maxDepth <- 2000000
        // как в Lisp.Host: поток с большим стеком (под профилем хвостовой цикл растёт системным стеком)
        let mutable out = ""
        let mutable err : exn = null
        let t = System.Threading.Thread((fun () ->
                    try out <- withOutput (fun () -> run env "(profile (cnt 40000))" |> ignore)
                    with e -> err <- e), 256 * 1024 * 1024)
        t.Start()
        t.Join()
        if not (isNull err) then raise err
        Assert.Contains("cnt", out)
    finally
        Debug.maxDepth <- saved
