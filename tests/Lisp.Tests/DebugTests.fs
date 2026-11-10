// Тесты инструментов отладки (Шаг 15b): имена функций, стек вызовов, защита от переполнения,
// try, trace, интроспекция диспетчеризации, describe, поле stack в AgentApi
module DebugTests

open System.IO
open System.Text.Json
open Xunit
open Types
open Reader
open Evaluator

// Выполнить все формы строки в окружении; результат последней
let run (env: Env) (s: string) : LispValue =
    readAll s |> List.fold (fun _ e -> eval e env) LispNil

let pp (env: Env) (s: string) : string = Printer.prettyPrint (run env s)

// Выполнить и вернуть пойманную LispError (тест падает, если ошибки не было)
let failure (env: Env) (s: string) : string * Frame list * LispValue =
    try
        run env s |> ignore
        failwith "ожидалась ошибка"
    with
    | LispError (m, st, d) -> (m, st, d)

let names (st: Frame list) = st |> List.map (fun f -> f.Name)

// Перехват вывода отладчика; trace/maxDepth возвращаются в исходное состояние
let withDebugOutput (f: unit -> unit) : string =
    let w = new StringWriter()
    Debug.writer <- w
    try f ()
    finally
        Debug.untraceAll ()
        Debug.writer <- null
        Debug.maxDepth <- 100000
    w.ToString().Replace("\r\n", "\n")

// --- Имена функций и печать ---

[<Fact>]
let ``define, лямбда и макрос получают имена`` () =
    let env = newEnv ()
    Assert.Equal("#<функция f>", pp env "(define (f x) x) f")
    Assert.Equal("#<функция g>", pp env "(define g (lambda (x) x)) g")
    Assert.Equal("#<функция lambda>", pp env "(lambda (x) x)")
    Assert.Equal("#<макрос m>", pp env "(defmacro (m x) x) m")

[<Fact>]
let ``define с уже именованной функцией не переименовывает`` () =
    let env = newEnv ()
    Assert.Equal("#<функция f>", pp env "(define (f x) x) (define h f) h")

[<Fact>]
let ``defmethod и add-method дают имя op(типы)`` () =
    let env = newEnv ()
    run env "(deftype 'dbgA 'any) (defmethod dbgop (dbgA dbgA) (a b) 1)" |> ignore
    Assert.Equal("#<функция dbgop(dbgA dbgA)>", pp env "(find-method 'dbgop '(dbgA dbgA))")
    run env "(add-method 'dbgop2 '(dbgA) (lambda (a) 2))" |> ignore
    Assert.Equal("#<функция dbgop2(dbgA)>", pp env "(find-method 'dbgop2 '(dbgA))")

// --- Стек вызовов ---

[<Fact>]
let ``стек ошибки из вложенных вызовов: имена и порядок`` () =
    let env = newEnv ()
    run env "(define (a x) (+ 1 (b x))) (define (b x) (+ 1 (c x))) (define (c x) (car x))" |> ignore
    let _, st, _ = failure env "(a 5)"
    Assert.Equal<string list>([ "car"; "c"; "b"; "a" ], names st)
    Assert.Equal("(5)", Printer.prettyPrint (LispList st.Head.Args))

[<Fact>]
let ``хвостовой вызов заменяет кадр`` () =
    let env = newEnv ()
    run env "(define (lp n) (if (= n 0) (car 1) (lp (- n 1))))" |> ignore
    let _, st, _ = failure env "(lp 1000)"
    Assert.Equal<string list>([ "car"; "lp" ], names st)
    Assert.Equal("(0)", Printer.prettyPrint (LispList st.Tail.Head.Args))

// Шаг 21i' (b): имя кадра берётся из функции в последнем элементе фрейма (не пишется в кадр) — замыкание,
// переименованное define, &rest, аргументы кадров; доступ замыкания к фреймам-родителям глубины 1 и 2
[<Fact>]
let ``стек: имена и аргументы кадров замыкания, &rest; переменные родительских фреймов`` () =
    let env = newEnv ()
    run env "(define (mk k) (lambda (x) (list (g x k)))) (define (g a b) (car a)) (define h (mk 7)) (define (r &rest xs) (list (h (car xs))))" |> ignore
    let _, st, _ = failure env "(r 5 6)"
    Assert.Equal<string list>([ "car"; "g"; "h"; "r" ], names st)
    Assert.Equal<string list>([ "(5)"; "(5 7)"; "(5)"; "(5 6)" ], st |> List.map (fun f -> Printer.prettyPrint (LispList f.Args)))
    Assert.Equal("6", pp env "(define (mk3 k) (lambda (x) (lambda (y) (+ x y k)))) (((mk3 1) 2) 3)")
    Assert.Equal("(3 . 4)", pp env "(define (cl a) (let ((b (+ a 1))) (lambda () (cons a b)))) ((cl 3))")
    Assert.Equal(0, Debug.depth)

[<Fact>]
let ``стек кадров пуст после ошибки и после нормального выхода`` () =
    let env = newEnv ()
    run env "(define (f x) (+ 1 (g x))) (define (g x) (car x))" |> ignore
    Assert.Equal(0, Debug.depth)
    failure env "(f 5)" |> ignore
    Assert.Equal(0, Debug.depth)
    Assert.Equal("3", pp env "(+ 1 2)")
    Assert.Equal(0, Debug.depth)
    // ошибка в методе (apply из applyHook)
    run env "(deftype 'dbgB 'any) (defmethod dbgm (dbgB) (x) (car 1))" |> ignore
    failure env "(find-method 'dbgm '(dbgB)) (apply (find-method 'dbgm '(dbgB)) (list (make-object 'dbgB)))" |> ignore
    Assert.Equal(0, Debug.depth)

[<Fact>]
let ``formatError: сообщение и строки «в f (арг)»`` () =
    let env = newEnv ()
    run env "(define (f x) (error \"сломалось\" x))" |> ignore
    try
        run env "(f 5)" |> ignore
    with ex ->
        let lines = (Debug.formatError ex).Split('\n')
        Assert.Equal("сломалось 5", lines.[0])
        Assert.Equal("  в error (\"сломалось\" 5)", lines.[1])
        Assert.Equal("  в f (5)", lines.[2])

[<Fact>]
let ``formatError усекает аргументы и число кадров`` () =
    let env = newEnv ()
    run env "(define (d n) (if (= n 0) (car 1) (+ 1 (d (- n 1)))))" |> ignore
    let _, st, _ = failure env "(d 40)"
    let lines = Debug.frameLines st
    Assert.Equal(21, lines.Length)
    Assert.Contains("... ещё", List.last lines)
    let long = LispList [ for i in 1 .. 100 -> LispInteger (bigint i) ]
    let line = Debug.formatFrame { Name = "f"; Args = [ long ]; Pos = null }
    Assert.True(line.Length < 80)
    Assert.Contains("...", line)

// --- Защита от переполнения ---

[<Fact>]
let ``бесконечная нехвостовая рекурсия — ловимая ошибка, интерпретатор жив`` () =
    let env = newEnv ()
    run env "(define (f n) (+ 1 (f n)))" |> ignore
    let msg, st, _ = failure env "(f 1)"
    Assert.True(msg.StartsWith "Переполнение стека" || msg.StartsWith "Превышена глубина рекурсии", msg)
    Assert.True(st.Length > 10)
    Assert.Equal(0, Debug.depth)
    Assert.Equal("3", pp env "(+ 1 2)")

[<Fact>]
let ``хвостовая рекурсия на 100000 итераций работает`` () =
    let env = newEnv ()
    Assert.Equal("100000", pp env "(define (c n acc) (if (= n 0) acc (c (- n 1) (+ acc 1)))) (c 100000 0)")

[<Fact>]
let ``set-max-depth ограничивает глубину`` () =
    let env = newEnv ()
    run env "(define (d n) (if (= n 0) 0 (+ 1 (d (- n 1)))))" |> ignore
    withDebugOutput (fun () ->
        run env "(set-max-depth 50)" |> ignore
        Assert.Equal("20", pp env "(d 20)")
        let msg, _, _ = failure env "(d 100)"
        Assert.Equal("Превышена глубина рекурсии 50", msg)
        Assert.Equal(0, Debug.depth)) |> ignore
    Assert.Equal("200", pp env "(d 200)")

[<Fact>]
let ``глубоко вложенное выражение в simplify не роняет процесс`` () =
    let env = newEnv ()
    run env "(define (nest n e) (if (= n 0) e (nest (- n 1) (list '+ 'x e))))" |> ignore
    let r =
        try
            run env "(simplify (nest 200000 'y))" |> ignore
            "ok"
        with LispError (m, _, _) -> m
    Assert.True(r = "ok" || r.StartsWith "Переполнение стека" || r.StartsWith "Превышена", r)
    Assert.Equal(0, Debug.depth)

// --- try ---

[<Fact>]
let ``try: значение без ошибки и обработчик`` () =
    let env = newEnv ()
    Assert.Equal("3", pp env "(try (+ 1 2) (lambda (e) 'oops))")
    Assert.Equal("oops", pp env "(try (car 5) (lambda (e) 'oops))")
    Assert.Equal("#t", pp env "(try (error \"x\") error?)")

[<Fact>]
let ``error-message, error-data, error-stack, печать`` () =
    let env = newEnv ()
    Assert.Equal("\"плохо 42\"", pp env "(try (error \"плохо\" 42) error-message)")
    Assert.Equal("nil", pp env "(try (error \"x\") error-data)")
    Assert.Equal("(код 7)", pp env "(try (raise '(код 7)) error-data)")
    Assert.Equal("\"boom\"", pp env "(try (raise \"boom\") error-message)")
    run env "(define (f x) (car x))" |> ignore
    Assert.Equal("(\"  в car (5)\" \"  в f (5)\")", pp env "(try (f 5) error-stack)")
    Assert.Equal("#<error boom>", pp env "(try (error \"boom\") (lambda (e) e))")

[<Fact>]
let ``try восстанавливает стек до глубины на входе`` () =
    let env = newEnv ()
    run env "(define (f n) (if (= n 0) (car 1) (+ 1 (f (- n 1)))))" |> ignore
    // ошибка в обработчике: в её стеке нет кадров f (иначе стек не восстановлен)
    let stack = pp env "(try (try (f 10) (lambda (e) (car 2))) (lambda (e2) (error-stack e2)))"
    Assert.DoesNotContain("в f", stack)
    Assert.Contains("в car (2)", stack)
    Assert.Equal(0, Debug.depth)
    run env "(try (f 10) (lambda (e) 0))" |> ignore
    Assert.Equal(0, Debug.depth)

[<Fact>]
let ``вложенные try`` () =
    let env = newEnv ()
    Assert.Equal("\"внутри\"", pp env "(try (try (error \"внутри\") (lambda (e) (raise e))) (lambda (e) (error-message (error-data e))))")
    Assert.Equal("1", pp env "(try (try (error \"a\") (lambda (e) 1)) (lambda (e) 99))")
    Assert.Equal("99", pp env "(try (try (error \"a\") (lambda (e) (error \"b\"))) (lambda (e) 99))")

[<Fact>]
let ``try ловит переполнение стека`` () =
    let env = newEnv ()
    run env "(define (f n) (+ 1 (f n)))" |> ignore
    Assert.Equal("#t", pp env "(try (f 1) (lambda (e) #t))")
    Assert.Equal(0, Debug.depth)

// --- trace ---

[<Fact>]
let ``trace: вход и выход с отступами`` () =
    let env = newEnv ()
    run env "(define (fact n) (if (= n 0) 1 (* n (fact (- n 1)))))" |> ignore
    let out =
        withDebugOutput (fun () ->
            Assert.Equal("(fact)", pp env "(trace 'fact)")
            Assert.Equal("2", pp env "(fact 2)"))
    let expected =
        "→ (fact 2)\n  → (fact 1)\n    → (fact 0)\n    ← fact = 1\n  ← fact = 1\n← fact = 2\n"
    Assert.Equal(expected, out)

[<Fact>]
let ``untrace снимает трассировку`` () =
    let env = newEnv ()
    run env "(define (f x) x) (define (g x) x)" |> ignore
    let out =
        withDebugOutput (fun () ->
            run env "(trace 'f 'g)" |> ignore
            Assert.Equal("(f g)", pp env "(trace)")
            run env "(untrace 'f)" |> ignore
            run env "(f 1) (g 2)" |> ignore
            run env "(untrace)" |> ignore
            Assert.Equal("nil", pp env "(trace)")
            run env "(f 1) (g 2)" |> ignore)
    Assert.Equal("→ (g 2)\n← g = 2\n", out)

[<Fact>]
let ``trace builtin`` () =
    let env = newEnv ()
    let out = withDebugOutput (fun () -> run env "(trace '+) (+ 1 2)" |> ignore)
    Assert.Equal("→ (+ 1 2)\n← + = 3\n", out)

[<Fact>]
let ``trace по имени метода`` () =
    let env = newEnv ()
    run env "(deftype 'dbgC 'any) (defmethod dbgop (dbgC) (x) 7) (define o (make-object 'dbgC))" |> ignore
    // имя метода «op(t1 t2)» — строкой (символом со скобками его не записать)
    let out1 =
        withDebugOutput (fun () ->
            run env "(trace \"dbgop(dbgC)\")" |> ignore
            run env "(apply (find-method 'dbgop '(dbgC)) (list o))" |> ignore)
    Assert.Equal("→ (dbgop(dbgC) #<dbgC>)\n← dbgop(dbgC) = 7\n", out1)
    let out2 =
        withDebugOutput (fun () ->
            run env "(trace-methods 'dbgop)" |> ignore
            run env "(apply (find-method 'dbgop '(dbgC)) (list o))" |> ignore)
    Assert.Contains("→ (dbgop(dbgC) #<dbgC>)", out2)
    Assert.Contains("← dbgop(dbgC) = 7", out2)

[<Fact>]
let ``trace: метод, вызванный диспетчеризацией из упрощателя`` () =
    let env = newEnv ()
    run env "(deftype 'dbgF 'any) (defmethod print (dbgF) (x) \"F!\") (define o (make-object 'dbgF))" |> ignore
    let out =
        withDebugOutput (fun () ->
            run env "(trace-methods 'print)" |> ignore
            run env "(to-string o)" |> ignore)
    Assert.Contains("→ (print(dbgF) F!)", out)
    Assert.Contains("← print(dbgF) = \"F!\"", out)

// --- Интроспекция ---

[<Fact>]
let ``explain-dispatch: метод найден по предку`` () =
    let env = newEnv ()
    run env "(deftype 'animal 'any) (deftype 'dog 'animal) (defmethod speak (animal) (a) 'rrr)" |> ignore
    let mutable result = ""
    let out = withDebugOutput (fun () -> result <- pp env "(explain-dispatch 'speak (make-object 'dog))")
    Assert.Equal("#<функция speak(animal)>", result)
    Assert.Contains("типы аргументов (dog)", out)
    Assert.Contains("dog -> animal -> any", out)
    Assert.Contains("speak(dog) — нет", out)
    Assert.Contains("speak(animal) — найден", out)
    Assert.Contains("выбран: #<функция speak(animal)>", out)

[<Fact>]
let ``explain-dispatch: метода нет`` () =
    let env = newEnv ()
    let mutable result = ""
    let out = withDebugOutput (fun () -> result <- pp env "(explain-dispatch 'nosuchop 1 \"s\")")
    Assert.Equal("nil", result)
    Assert.Contains("nosuchop(integer string) — нет", out)
    Assert.Contains("метод не найден", out)

[<Fact>]
let ``methods и methods-of`` () =
    let env = newEnv ()
    run env "(deftype 'dbgD 'any) (defmethod dbgop3 (dbgD dbgD) (a b) 1) (defmethod dbgop3 (dbgD integer) (a b) 2) (defmethod dbgop4 (dbgD) (a) 3)" |> ignore
    Assert.Equal("((dbgD dbgD) (dbgD integer))", pp env "(methods 'dbgop3)")
    Assert.Equal("nil", pp env "(methods 'nosuchop)")
    Assert.Equal("((dbgop3 (dbgD dbgD)) (dbgop3 (dbgD integer)) (dbgop4 (dbgD)))", pp env "(methods-of 'dbgD)")

[<Fact>]
let ``describe: число, объект, символ, тип`` () =
    let env = newEnv ()
    run env "(deftype 'dbgE 'any) (defmethod dbgop5 (dbgE) (a) 1) (define dbgv 10) (put 'dbgv 'color 'red)" |> ignore
    let out =
        withDebugOutput (fun () ->
            Assert.Equal("5", pp env "(describe 5)")
            Assert.Equal("#<dbgE 1 x>", pp env "(describe (make-object 'dbgE 1 'x))")
            Assert.Equal("dbgv", pp env "(describe 'dbgv)")
            run env "(describe 'dbgE)" |> ignore)
    Assert.Contains("значение: 5", out)
    Assert.Contains("тип: integer", out)
    Assert.Contains("integer -> rational -> real -> number -> scalar -> any", out)
    Assert.Contains("поле 0: 1", out)
    Assert.Contains("поле 1: x", out)
    Assert.Contains("в окружении: 10", out)
    Assert.Contains("свойство color: red", out)
    Assert.Contains("методы типа:", out)
    Assert.Contains("dbgop5(dbgE)", out)

// --- last-error и backtrace ---

[<Fact>]
let ``recordError сохраняет *last-error*, backtrace печатает стек`` () =
    let env = newEnv ()
    run env "(define (f x) (car x))" |> ignore
    try run env "(f 5)" |> ignore
    with ex -> recordError env ex
    Assert.Equal("#t", pp env "(error? *last-error*)")
    let out = withDebugOutput (fun () -> run env "(backtrace)" |> ignore)
    Assert.Contains("  в f (5)", out)

// --- AgentApi ---

[<Fact>]
let ``AgentApi: ответ об ошибке содержит stack`` () =
    let session = AgentApi.makeSession ()
    let r = AgentApi.handleJsonRequest session "{\"op\":\"eval\",\"code\":\"(define (f x) (car x)) (f 5)\"}"
    let root = JsonDocument.Parse(r).RootElement
    Assert.False(root.GetProperty("ok").GetBoolean())
    let stack = root.GetProperty("stack").EnumerateArray() |> Seq.map (fun e -> e.GetString()) |> List.ofSeq
    // Шаг 21d: кадры с известной позицией дополнены « — <json>:строка» (код пришёл из JSON)
    Assert.Equal<string list>([ "в car (5) — <json>:1"; "в f (5) — <json>:1" ], stack)

[<Fact>]
let ``AgentApi: ошибка без Lisp-стека — пустой stack`` () =
    let session = AgentApi.makeSession ()
    let r = AgentApi.handleJsonRequest session "{\"op\":\"zzz\",\"code\":\"1\"}"
    let root = JsonDocument.Parse(r).RootElement
    Assert.Equal(0, root.GetProperty("stack").GetArrayLength())

// --- Шаг 17b: time и profile ---

[<Fact>]
let ``time: печатает время и возвращает значение`` () =
    let env = newEnv ()
    let mutable v = ""
    let out = withDebugOutput (fun () -> v <- pp env "(time (+ 1 2))")
    Assert.Equal("3", v)
    Assert.StartsWith("время: ", out)
    Assert.Contains(" мс", out)

[<Fact>]
let ``profile: таблица вызовов, доля builtins, значение возвращается`` () =
    let env = newEnv ()
    run env "(define (fib n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))" |> ignore
    let mutable v = ""
    let out = withDebugOutput (fun () -> v <- pp env "(profile (fib 10))")
    Assert.Equal("55", v)
    Assert.Contains("fib", out)
    Assert.Contains("[builtin] +", out)
    Assert.Contains("чистая интерпретация", out)
    // fib(10): 177 вызовов
    Assert.Matches(@"fib\s+177\s", out)
    Assert.False(Debug.profiling)

[<Fact>]
let ``profile выключен по умолчанию и после ошибки`` () =
    let env = newEnv ()
    Assert.False(Debug.profiling)
    withDebugOutput (fun () -> failure env "(profile (car 5))" |> ignore) |> ignore
    Assert.False(Debug.profiling)
    Assert.False(Debug.hooked)

// --- Шаг 21d: позиции в исходнике ---

// Временный файл с заданным текстом (имя уникально для теста)
let private withTempFile (ext: string) (text: string) (f: string -> unit) : unit =
    let path = Path.Combine(Path.GetTempPath(), "lisp21d_" + System.Guid.NewGuid().ToString("N") + ext)
    File.WriteAllText(path, text)
    try f path
    finally File.Delete path

[<Fact>]
let ``позиции: ошибка в загруженном файле — строка и файл в кадре`` () =
    let env = newEnv ()
    withTempFile ".lisp" "; комментарий\n(define (foo x)\n  (car x))\n\n(define (bar y)\n  (+ 1\n     (foo y)))\n" (fun path ->
        loadIntoEnv path env |> ignore
        let name = Path.GetFileName path
        let _, st, _ = failure env "(bar 7)"
        // самый глубокий кадр — car: форма (car x) в строке 3; затем foo — вызов в строке 7; затем bar — <repl> нет (readAll без позиций)
        Assert.Equal<string list>([ "car"; "foo"; "bar" ], names st)
        Assert.Equal(3, st.[0].Pos.Line)
        Assert.Equal(7, st.[1].Pos.Line)
        Assert.Equal(path, st.[0].Pos.File)
        Assert.True(isNull st.[2].Pos)
        let text = Debug.formatError (LispError ("m", st, LispNil))
        Assert.Contains(name + ":3", text)
        Assert.Contains(name + ":7", text))

[<Fact>]
let ``позиции: вложенный вызов из REPL — две строки с позициями`` () =
    let env = newEnv ()
    run env "(define (foo x) (car x))" |> ignore
    let exprs = readAllFrom "<repl>" "(define (bar y) (+ 1 (foo y)))\n(bar 1)"
    let err =
        try
            exprs |> List.iter (fun e -> eval e env |> ignore)
            ""
        with LispError _ as ex -> Debug.formatError ex
    let lines = err.Split('\n')
    Assert.Equal("car: ожидается список, получено 1", lines.[0])
    Assert.Equal<string list>([ "  в car (1)"; "  в foo (1) — <repl>:1"; "  в bar (1) — <repl>:2" ], lines |> Array.skip 1 |> List.ofArray)

[<Fact>]
let ``позиции: кадры из REPL с именем и строкой`` () =
    let env = newEnv ()
    let exprs = readAllFrom "<repl>" "(define (f x)\n  (car x))\n(f 5)"
    let err =
        try
            exprs |> List.iter (fun e -> eval e env |> ignore)
            ""
        with LispError _ as ex -> Debug.formatError ex
    Assert.Contains("  в car (5) — <repl>:2", err)
    Assert.Contains("  в f (5) — <repl>:3", err)

[<Fact>]
let ``позиции: describe показывает, где определена функция`` () =
    let env = newEnv ()
    withTempFile ".lisp" "\n\n(define (g x) x)\n" (fun path ->
        loadIntoEnv path env |> ignore
        let out = withDebugOutput (fun () -> run env "(describe 'g)" |> ignore)
        Assert.Contains("определена: " + path + ":3", out))

[<Fact>]
let ``позиции: readAll без имени позиций не пишет, quote-формы отмечены`` () =
    let plain = readAll "(f x)" |> List.head
    Assert.True(isNull (posOf plain))
    let marked = readAllFrom "<json>" "\n  (f x)" |> List.head
    Assert.Equal("<json>:2", (posOf marked).ToString())
    Assert.Equal(3, (posOf marked).Col)

[<Fact>]
let ``позиции: JSON — кадры содержат <json>`` () =
    let session = AgentApi.makeSession ()
    let r = AgentApi.handleJsonRequest session "{\"op\":\"eval\",\"code\":\"(define (f x)\\n (car x))\\n(f 5)\"}"
    let root = JsonDocument.Parse(r).RootElement
    let stack = root.GetProperty("stack").EnumerateArray() |> Seq.map (fun e -> e.GetString()) |> List.ofSeq
    Assert.Equal<string list>([ "в car (5) — <json>:2"; "в f (5) — <json>:3" ], stack)

[<Fact>]
let ``позиции: язык — ошибка в .mth показывает строки файла`` () =
    let session = AgentApi.makeSession ()
    withTempFile ".mth" "f(x) := 1 +\n   [1, 2][5] + x\ng(y) := 2 *\n   f(y)\ng(3)\n" (fun path ->
        let code = JsonSerializer.Serialize({| op = "eval"; code = "(load-math " + JsonSerializer.Serialize(path) + ")" |})
        let r = AgentApi.handleJsonRequest session code
        let root = JsonDocument.Parse(r).RootElement
        Assert.False(root.GetProperty("ok").GetBoolean())
        let stack = root.GetProperty("stack").EnumerateArray() |> Seq.map (fun e -> e.GetString()) |> List.ofSeq
        let name = Path.GetFileName path
        Assert.Contains(stack, fun l -> l.StartsWith "в m-ix" && l.EndsWith(name + ":2"))
        Assert.Contains(stack, fun l -> l.EndsWith(name + ":4"))
        Assert.Contains(stack, fun l -> l.EndsWith(name + ":5")))

// --- Шаг 21d: trace-simplify / simplify-steps ---

// Имена преобразований, сработавших при упрощении выражения (в порядке выполнения)
let private stepNames (env: Env) (expr: string) : string list =
    match run env (sprintf "(map car (simplify-steps '%s))" expr) with
    | LispList l -> l |> List.map (function LispSym s -> s | other -> Printer.prettyPrint other)
    | _ -> []

[<Theory>]
[<InlineData("exact-value", "(sin (* 1/2 pi))")>]
[<InlineData("collect-terms", "(+ (* 2 x) (* 3 x))")>]
[<InlineData("pythagorean", "(+ (^ (sin x) 2) (^ (cos x) 2))")>]
[<InlineData("merge-powers", "(* (^ x 2) x)")>]
[<InlineData("exp-merge", "(* (exp x) (exp y))")>]
[<InlineData("extract-root", "(sqrt 8)")>]
[<InlineData("exact-root", "(^ 4 1/2)")>]
[<InlineData("sqrt-rational", "(sqrt 8)")>]
[<InlineData("sqrt-negative", "(sqrt -4)")>]
[<InlineData("power-of-product", "(^ (* a b) -1)")>]
[<InlineData("exp-power", "(^ (exp x) 2)")>]
[<InlineData("power-of-power", "(^ (^ x 2) 3)")>]
[<InlineData("imaginary-power", "(^ %i 3)")>]
[<InlineData("distribute-minus", "(* -1 (+ a b))")>]
[<InlineData("trig-rules", "(tan x)")>]
[<InlineData("ln-to-log", "(ln x)")>]
let ``simplify-steps: преобразование видно в журнале`` (name: string, expr: string) =
    let env = newEnv ()
    Assert.Contains(name, stepNames env expr)

[<Fact>]
let ``simplify-steps: правило defrule и метод диспетчеризации`` () =
    let env = newEnv ()
    run env "(defrule st-dbl (st-dbl ?x) (* 2 ?x))" |> ignore
    try
        Assert.Contains("rule:st-dbl", stepNames env "(st-dbl a)")
        run env "(defmethod + (st21o st21o) (a b) (make-object 'st21o (+ (object-ref a 0) (object-ref b 0))))" |> ignore
        match run env "(map car (simplify-steps (list '+ (make-object 'st21o 1) (make-object 'st21o 2))))" with
        | LispList (LispSym "method:+" :: _) -> ()
        | other -> failwithf "ожидался шаг method:+, получено %s" (Printer.prettyPrint other)
    finally
        run env "(remove-rule 'st-dbl)" |> ignore

[<Fact>]
let ``simplify-steps: шаг — список (имя до после)`` () =
    let env = newEnv ()
    Assert.Equal("((exact-value (sin (* 1/2 pi)) 1))", pp env "(simplify-steps '(sin (* 1/2 pi)))")
    Assert.Equal("()", pp env "(simplify-steps '(+ x 1))")

[<Fact>]
let ``trace-simplify: строки в синтаксисе math-print, результат — упрощённое выражение`` () =
    let env = newEnv ()
    let mutable v = ""
    let out = withDebugOutput (fun () -> v <- pp env "(trace-simplify '(sin (* 1/2 pi)))")
    Assert.Equal("1", v)
    Assert.Equal("[exact-value] sin(1/2*pi) → 1\n", out)
    let out2 = withDebugOutput (fun () -> pp env "(trace-simplify '(+ (* 2 x) (* 3 x)))" |> ignore)
    Assert.Equal("[collect-terms] 2x + 3x → 5x\n", out2)

[<Fact>]
let ``trace-simplify: выключенная трассировка не меняет результаты, флаг сбрасывается`` () =
    let env = newEnv ()
    let exprs = [ "(+ (* 2 x) (* 3 x) (sin (* 1/2 pi)))"; "(* (exp x) (exp y) (^ x 2) x)"; "(sqrt 8)"; "(tan x)"
                  "(+ (^ (sin x) 2) (^ (cos x) 2) y)" ]
    for e in exprs do
        let plain = pp env (sprintf "(simplify '%s)" e)
        // трассировка включена: результат тот же; после неё — снова тот же и флаг сброшен
        let mutable traced = ""
        withDebugOutput (fun () -> traced <- pp env (sprintf "(trace-simplify '%s)" e)) |> ignore
        Assert.Equal(plain, traced)
        Assert.Equal(plain, pp env (sprintf "(simplify '%s)" e))
        Assert.False(Debug.simpTracing)

[<Fact>]
let ``trace-simplify: ограничение длины журнала — отметка усечено`` () =
    let env = newEnv ()
    // сумма из 600 пар подобных: больше 500 шагов collect-terms не получить одним вызовом, поэтому берём
    // вложенные суммы — каждая вложенная сумма даёт свой шаг
    let nested = String.concat "" [ for i in 1 .. 600 -> sprintf "(+ (* 2 x%d) (* 3 x%d)) " i i ]
    let steps = run env (sprintf "(simplify-steps '(list %s))" nested)
    match steps with
    | LispList l ->
        Assert.Equal(501, l.Length)
        Assert.Equal("(…усечено)", Printer.prettyPrint (List.last l))
    | other -> failwithf "ожидался список, получено %A" other
    Assert.False(Debug.simpTracing)

[<Fact>]
let ``trace_simplify и simplify_steps в языке: вывод в output`` () =
    let session = AgentApi.makeSession ()
    let call (code: string) =
        JsonDocument.Parse(AgentApi.handleJsonRequest session (JsonSerializer.Serialize({| op = "math"; code = code |}))).RootElement
    let r = call "trace_simplify(sin(pi/2) + 2*x + 3*x)"
    Assert.True(r.GetProperty("ok").GetBoolean())
    Assert.Equal("[exact-value] sin(1/2*pi) → 1\n[collect-terms] 1 + 2x + 3x → 1 + 5x", r.GetProperty("output").GetString())
    Assert.Equal("1 + 5x", r.GetProperty("pretty").GetString())
    let r2 = call "simplify_steps(sqrt(8))"
    Assert.Equal("[[\"extract-root\", 8^(1/2), 2*2^(1/2)], [\"sqrt-rational\", sqrt(8), 2*2^(1/2)]]", r2.GetProperty("pretty").GetString())

// --- Шаг 21i' (e): map/map2/filter/foldl/reverse/any?/every? — builtin на F# ---

[<Fact>]
let ``списочные builtin: порядок вызовов, порядок результата, пустой список, обрыв any?/every?`` () =
    let env = newEnv ()
    run env "(define lg '()) (define (note x) (set! lg (cons x lg)) x) (define (oddp? x) (= 1 (remainder x 2)))" |> ignore
    Assert.Equal("(10 20 30)", pp env "(map (lambda (x) (* 10 (note x))) '(1 2 3))")
    Assert.Equal("(3 2 1)", pp env "lg")
    run env "(set! lg '())" |> ignore
    Assert.Equal("(1 3)", pp env "(filter (lambda (x) (note x) (= 1 (remainder x 2))) '(1 2 3))")
    Assert.Equal("(3 2 1)", pp env "lg")
    run env "(set! lg '())" |> ignore
    Assert.Equal("(((0 1) 2) 3)", pp env "(foldl (lambda (a x) (note x) (list a x)) 0 '(1 2 3))")
    Assert.Equal("(3 2 1)", pp env "lg")
    Assert.Equal("(11 22)", pp env "(map2 + '(1 2 3) '(10 20))")
    Assert.Equal("(11 22)", pp env "(map2 (lambda (x y) (+ x y)) '(1 2) '(10 20 30))")
    Assert.Equal("(3 2 1)", pp env "(reverse '(1 2 3))")
    Assert.Equal("(() () () ())", pp env "(list (map car '()) (map2 car '() '(1)) (filter oddp? '()) (reverse '()))")
    Assert.Equal("5", pp env "(foldl + 5 '())")
    Assert.Equal("#f", pp env "(any? oddp? '())")
    Assert.Equal("#t", pp env "(every? oddp? '())")
    run env "(set! lg '())" |> ignore
    Assert.Equal("#t", pp env "(any? (lambda (x) (note x) (> x 1)) '(1 2 3 4))")
    Assert.Equal("(2 1)", pp env "lg")
    run env "(set! lg '())" |> ignore
    Assert.Equal("#f", pp env "(every? (lambda (x) (note x) (< x 2)) '(1 2 3 4))")
    Assert.Equal("(2 1)", pp env "lg")
    // builtin и макро-свободные значения как функции, замыкания, функция с &rest
    Assert.Equal("(2 3 4)", pp env "(map (let ((k 1)) (lambda (x) (+ x k))) '(1 2 3))")
    Assert.Equal("((1) (2))", pp env "(map (lambda (&rest r) r) '(1 2))")
    Assert.Equal("(1 2)", pp env "(map car '((1) (2)))")
    Assert.Equal(0, Debug.depth)

[<Fact>]
let ``списочные builtin: ошибки — кадр builtin и кадр лямбды, не-список, арность`` () =
    let env = newEnv ()
    let _, st, _ = failure env "(map (lambda (x) (car x)) '((1) 2))"
    Assert.Equal<string list>([ "car"; "lambda"; "map" ], names st)
    Assert.Equal("(2)", Printer.prettyPrint (LispList st.Tail.Head.Args))
    run env "(define (sq x) (+ x (car x)))" |> ignore
    let _, st2, _ = failure env "(foldl (lambda (a x) (sq x)) 0 '(1))"
    Assert.Equal<string list>([ "car"; "sq"; "foldl" ], names st2)
    let msg, _, _ = failure env "(map car 5)"
    Assert.Contains("map: ожидается список", msg)
    let msg2, _, _ = failure env "(filter car)"
    Assert.Contains("filter", msg2)
    let msg3, _, _ = failure env "(map (lambda (x y) x) '(1 2))"
    Assert.Contains("ожидает 2 аргументов, получено 1", msg3)
    Assert.Equal(0, Debug.depth)

[<Fact>]
let ``списочные builtin: длинный список 10^5, вложенные map, trace лямбды`` () =
    let env = newEnv ()
    Assert.Equal("100000", pp env "(length (map (lambda (x) (+ x 1)) (range 100000)))")
    Assert.Equal("4999950000", pp env "(foldl + 0 (filter (lambda (x) (>= x 0)) (map (lambda (x) x) (range 100000))))")
    Assert.Equal("99999", pp env "(car (reverse (range 100000)))")
    Assert.Equal("((1 2) (2 4))", pp env "(map (lambda (x) (map (lambda (y) (* x y)) '(1 2))) '(1 2))")
    // глубокая рекурсия через map не роняет процесс (ошибка глубины/стека ловится)
    run env "(define (deep n) (if (= n 0) 0 (car (map (lambda (x) (+ 1 (deep (- n 1)))) '(1)))))" |> ignore
    Assert.Equal("100", pp env "(deep 100)")
    let msg, _, _ = failure env "(deep 10000000)"
    Assert.True(msg.StartsWith "Переполнение стека" || msg.StartsWith "Превышена глубина рекурсии", msg)
    Assert.Equal("100", pp env "(deep 100)")
    // trace видит вызовы лямбды (применение через общий путь)
    run env "(define (tw x) (* 2 x))" |> ignore
    let out =
        withDebugOutput (fun () ->
            run env "(trace 'tw)" |> ignore
            Assert.Equal("(2 4)", pp env "(map tw '(1 2))"))
    Assert.Equal("→ (tw 1)\n← tw = 2\n→ (tw 2)\n← tw = 4\n", out)
