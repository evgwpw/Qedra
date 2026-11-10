// Тесты статического проверщика (Checker.fs, Lisp.exe --check): CHK.1 — чтение и скобки
module CheckerTests

open System.IO
open Xunit
open Checker

let private errorsOf (text: string) : Diag list =
    parseSource "t.lisp" text |> snd |> List.filter (fun d -> d.Severity = SevError)

let private codes (ds: Diag list) = ds |> List.map (fun d -> d.Code)

[<Fact>]
let ``CHK.1: корректный файл — без диагностики`` () =
    let ds = parseSource "t.lisp" "(define (f x) (if (> x 0) '(a . b) `(1 ,x ,@(list 2))))\n; комментарий (\n(display \"a ) b\")\n#(1 2)\n" |> snd
    Assert.Empty ds

[<Fact>]
let ``CHK.1: незакрытая скобка — внутренняя позиция и вероятное место )`` () =
    let text =
        "(define (f x)\n  (let ((a 1))\n    (display a)\n    (if (> x 0)\n        (+ x 1)\n        (- x 1))\n\n(define (g y)\n  (* y 2))\n"
    let ds = errorsOf text
    Assert.Equal<string list>([ "unclosed-paren"; "missing-paren" ], codes ds)
    // самая внутренняя незакрытая — let на 2:3, форма начинается на 1:1
    Assert.Equal((2, 3), (ds.[0].Line, ds.[0].Col))
    Assert.Contains("2 незакрытых", ds.[0].Message)
    // вероятное место — конец строки 6 (перед строкой 8), не хватает двух «)»
    Assert.Equal(6, ds.[1].Line)
    Assert.Contains("2 «)»", ds.[1].Message)
    Assert.Contains("1:1", ds.[1].Message)

[<Fact>]
let ``CHK.1: лишняя закрывающая скобка с позицией, чтение продолжается`` () =
    let ds = errorsOf "(a b))\n(c d\n"
    Assert.Equal<string list>([ "extra-paren"; "unclosed-paren"; "missing-paren" ], codes ds)
    Assert.Equal((1, 6), (ds.[0].Line, ds.[0].Col))
    Assert.Equal((2, 1), (ds.[1].Line, ds.[1].Col))

[<Fact>]
let ``CHK.1: незакрытая строка`` () =
    let ds = errorsOf "(display \"abc)\n(f 1)\n"
    Assert.Contains("unterminated-string", codes ds)
    let d = ds |> List.find (fun d -> d.Code = "unterminated-string")
    Assert.Equal((1, 10), (d.Line, d.Col))

[<Fact>]
let ``CHK.1: несколько проблем — синхронизация на «(» в первом столбце`` () =
    let text = "(define (a x)\n  (+ x 1)\n\n(define (b x)\n  (* x 2)))\n\n(define (c x)\n  (- x 1)\n"
    let ds = errorsOf text
    // a не закрыта (до строки 4), у b лишняя «)», c не закрыта до конца файла
    let lines = ds |> List.map (fun d -> d.Code, d.Line)
    Assert.Contains(("unclosed-paren", 1), lines)
    Assert.Contains(("extra-paren", 5), lines)
    Assert.Contains(("unclosed-paren", 7), lines)

[<Fact>]
let ``CHK.1: неверный синтаксис — # и точка`` () =
    let ds = errorsOf "(f #\\a)\n(g (. a))\n(h (a . b c))\n"
    Assert.Equal<string list>([ "bad-syntax"; "bad-dot"; "bad-dot" ], codes ds)

[<Fact>]
let ``CHK.1: кавычка без выражения`` () =
    Assert.Contains("dangling-quote", codes (errorsOf "(f 'x ')\n"))
    Assert.Contains("dangling-quote", codes (errorsOf "(f 1) '"))

[<Fact>]
let ``CHK.1: формат вывода и JSON`` () =
    let d = (errorsOf "(a))").Head
    Assert.Equal("t.lisp:1:4: ошибка: лишняя «)»", formatDiag d)
    let j = formatJson [ d ]
    Assert.Equal("[{\"file\":\"t.lisp\",\"line\":1,\"col\":4,\"severity\":\"error\",\"code\":\"extra-paren\",\"message\":\"лишняя «)»\"}]", j)
    Assert.Equal("[]", formatJson [])

let private libFiles () =
    let dir = Path.Combine(System.AppContext.BaseDirectory, "lib")
    Directory.GetFiles(dir, "*.lisp", SearchOption.AllDirectories) |> Array.sort

let private testFiles () =
    Directory.GetFiles(Path.Combine(System.AppContext.BaseDirectory, "lisp"), "*.lisp") |> Array.sort

[<Fact>]
let ``CHK.1: все lib и tests lisp читаются без ошибок`` () =
    let files = Array.append (libFiles ()) (testFiles ())
    Assert.True(files.Length > 40)
    let bad =
        files |> Array.collect (fun f -> (parseSource f (File.ReadAllText f) |> snd) |> List.filter (fun d -> d.Severity = SevError) |> Array.ofList)
    Assert.True(bad.Length = 0, String.concat "\n" (bad |> Array.map formatDiag))

// ---------- CHK.2: статические проверки ----------

let private diagsOf (text: string) : Diag list = checkText "t.lisp" text

let private has (code: string) (ds: Diag list) = ds |> List.exists (fun d -> d.Code = code)

[<Fact>]
let ``CHK.2: неизвестные имена с подсказками, цитаты и локальные имена не трогаются`` () =
    let ds = diagsOf "(print 1)\n(expt 2 3)\n(lenght '(1))\n(display zork)\n"
    Assert.Equal(4, ds.Length)
    Assert.True(ds |> List.forall (fun d -> d.Severity = SevWarning && d.Code = "unknown-name"))
    Assert.Contains("display и newline", ds.[0].Message)
    Assert.Contains("степень — ^", ds.[1].Message)
    Assert.Contains("length", ds.[2].Message)
    let ok =
        "(define (f n) (let loop ((i 0) (acc '())) (if (< i n) (loop (+ i 1) (cons i acc)) acc)))\n" +
        "(define (g x) (define h (lambda (y) (+ y x))) (h 1))\n" +
        "(display '(no such names here))\n(display `(a ,(f 1) ,@(f 2)))\n(display :kw)\n" +
        "(display (do ((i 0 (+ i 1))) ((= i 3) i)))\n(let* ((a 1) (b (+ a 1))) b)\n(letrec ((ev? (lambda (n) (od? n))) (od? (lambda (n) n))) (ev? 1))\n" +
        "(case 3 ((1 2) 'low) (else 'hi))\n(when #t (display 1))\n(define later (lambda () (defined-below)))\n(define (defined-below) 1)\n"
    Assert.Empty(diagsOf ok)

[<Fact>]
let ``CHK.2: арность функций файла и builtin`` () =
    let ds = diagsOf "(define (sq x) (* x x))\n(define (v a &rest r) a)\n(sq 1 2)\n(sq)\n(v)\n(v 1 2 3)\n(car 1 2)\n(foldl + 0 '(1) 3)\n(map car)\n"
    let errs = ds |> List.filter (fun d -> d.Code = "arity") |> List.map (fun d -> d.Line)
    Assert.Equal<int list>([ 3; 4; 5; 7; 8; 9 ], errs)

[<Fact>]
let ``CHK.2: форма специальных форм`` () =
    let ds =
        diagsOf "(let x 5)\n(let ((a 1) (b)) a)\n(if 1 2 3 4)\n(lambda x x)\n(cond (1))\n(define car 5)\n(define (cdr x) x)\n(case 1 ((1)))\n(let ((a 1)))\n"
    let lines = ds |> List.filter (fun d -> d.Severity = SevError) |> List.map (fun d -> d.Line)
    Assert.Equal<int list>([ 1; 2; 3; 4; 5; 6; 7; 8; 9 ], lines)
    Assert.True(has "define-builtin" ds)

[<Fact>]
let ``CHK.2: ожидаемая ошибка в assert-error не диагностируется`` () =
    Assert.Empty(diagsOf "(deftest \"t\" (assert-error (case 1 ((1)))) (assert-error (nonexistent 1)))\n")

[<Fact>]
let ``CHK.2: модуль — экспорт, приватные и квалифицированные имена`` () =
    let ok = "(module mm (export pub))\n(define (priv x) (* x 2))\n(define (pub x) (priv x))\n(display (dp::lcs '(1) '(1)))\n(display (mm::priv 2))\n"
    Assert.Empty(diagsOf ok)
    let bad = diagsOf "(module mm2 (export pub nopub))\n(define (pub x) x)\n"
    Assert.True(has "export-undefined" bad)

[<Fact>]
let ``CHK.2: макросы prelude — тела проверяются, локальные имена do/while видны`` () =
    let ds = diagsOf "(define (f l) (for-each (lambda (x) (display x)) l) (while (< 1 0) (bad-name 1)) (unless #f (display 2)))\n"
    Assert.Equal(1, ds.Length)
    Assert.Contains("bad-name", ds.[0].Message)

[<Fact>]
let ``CHK.2: lib и tests lisp — без ошибок и предупреждений (ложных срабатываний нет)`` () =
    let files = Array.append (libFiles ()) (testFiles ())
    let all = files |> Array.collect (fun f -> checkText f (File.ReadAllText f) |> Array.ofList)
    Assert.True(all.Length = 0, String.concat "\n" (all |> Array.map formatDiag))
