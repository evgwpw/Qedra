// Тесты модулей библиотеки Lisp (шаг 21h', бывший шаг 23): (module имя (export ...)), приватные имена, конфликты
module ModuleTests

open System
open System.IO
open Xunit
open Types
open Reader
open Evaluator
open Printer

let private evalIn (env: Env) (src: string) : LispValue =
    readAll src |> List.fold (fun _ e -> eval e env) LispNil

let private show (v: LispValue) = prettyPrint v

// Выполнить Lisp-файл с заданным содержимым в окружении
let private loadText (env: Env) (name: string) (text: string) : LispValue =
    let path = Path.Combine(Path.GetTempPath(), "modtest_" + Guid.NewGuid().ToString("N") + "_" + name + ".lisp")
    File.WriteAllText(path, text)
    try loadIntoEnv path env
    finally File.Delete path

// Текст ошибки загрузки
let private loadError (env: Env) (name: string) (text: string) : string =
    try
        loadText env name text |> ignore
        failwith "ожидалась ошибка загрузки"
    with ex -> ex.Message

[<Fact>]
let ``библиотека: ни одно имя не определено в двух модулях (раньше такие определения молча перезаписывали друг друга)`` () =
    let env = newEnv ()
    let dups = duplicateDefinitions env
    Assert.True(dups.IsEmpty, "имена в нескольких модулях:\n" + String.Join("\n", dups))

[<Fact>]
let ``библиотека: список модулей и экспорт`` () =
    let env = newEnv ()
    let names = env.Modules.Keys |> Seq.sort |> List.ofSeq
    Assert.Equal<string list>([ "algnum"; "cfinite"; "complex-analysis"; "constzero"; "curves"; "definite"; "denest"; "diffgeom"; "domain"; "dp"; "elliptic"; "field"; "forms"; "fourier"; "galois"; "gf"; "groebner"; "group"; "gruntz"; "homology"; "integrate"; "interval"; "laplace"; "limit"; "linalg"; "logic"; "lp"; "match"; "mathlang"; "multiint"; "numtheory"; "ode"; "optimize"; "plot"; "poly"; "prelude"; "prob"; "puiseux"; "risch"; "rules"; "series"; "set"; "solve"; "sos"; "specfun"; "stats"; "steps"; "summation"; "tensor"; "test"; "transforms"; "trigsimp"; "units"; "variational" ], names)
    // экспортированное — глобальное; приватное — только «модуль::имя»
    Assert.True((env.Lookup "integrate").IsSome)
    Assert.True((env.Lookup "int-check").IsSome)
    Assert.True((env.Lookup "int-size").IsNone)
    Assert.True((env.Lookup "integrate::int-size").IsSome)
    Assert.True((env.Lookup "trigsimp").IsSome)
    Assert.True((env.Lookup "trigsimp-half-angle").IsSome)
    Assert.True((env.Lookup "trigsimp-pow4-diff").IsNone)
    Assert.True((env.Lookup "find-pivot").IsNone)
    Assert.True((env.Lookup "tensor::find-pivot").IsSome)
    Assert.True((env.Lookup "gruntz-limitinf").IsSome)
    Assert.True((env.Lookup "gr-mrv").IsNone)
    Assert.True((env.Lookup "gruntz::gr-mrv").IsSome)

[<Fact>]
let ``библиотека: все ссылки модулей на глобальные имена разрешаются (экспорт достаточен)`` () =
    let env = newEnv ()
    let missing = checkModules env
    Assert.True(missing.IsEmpty, "неразрешённые ссылки (модуль: имена):\n" + String.Join("\n", missing))

[<Fact>]
let ``математический язык видит только глобальные имена: функции из docs/math-language.md экспортированы`` () =
    let env = newEnv ()
    // Lisp-функции библиотеки, которые документированы как доступные из языка (имена с «_» — переименования m-renames)
    let names =
        [ "det"; "inv"; "rank"; "dot"; "cross"; "norm"; "transpose"; "integrate"; "limit"; "series"; "taylor"; "solve"
          "union"; "intersection"; "set-difference"; "power-set"; "list->set"; "set->list"; "empty-set?"; "card"
          "in?"; "subset?"; "declare"; "undeclare"; "real?"; "positive?"; "negative?"; "nonnegative?"; "nonpositive?"
          "poly-gcd"; "poly-lcm"; "poly-quotient"; "poly-remainder"; "real-roots"; "coefficients"; "leading-coefficient"
          "interval"; "naturals"; "integers"; "rationals"; "reals"; "complexes"; "positive"; "nonnegative"; "negative"; "nonpositive"
          "groebner"; "normal-form"; "eliminate"; "m-groebner"; "m-normal-form"; "m-eliminate"
          "math-eval"; "math-eval-tree"; "load-math"; "math-reset"; "factorial"
          // шаг LP.3: линейное программирование из математического языка
          "lp-maximize"; "lp-minimize"; "math-lp-solve"; "math-ilp-solve"; "math-lp-check"; "math-ilp-check" ]
    let missing = names |> List.filter (fun n -> (env.Lookup n).IsNone)
    Assert.True(missing.IsEmpty, "не экспортированы: " + String.Join(" ", missing))

// --- механизм модулей на синтетических файлах ---

let private modA = "(module ma (export f))\n(define (helper x) (* x 10))\n(define (f x) (helper x))\n"

[<Fact>]
let ``модуль: экспорт — глобальное имя, приватное — только квалифицированно`` () =
    let env = newEnv ()
    loadText env "a" modA |> ignore
    Assert.Equal("20", show (evalIn env "(f 2)"))
    Assert.True((env.Lookup "helper").IsNone)
    Assert.Equal("30", show (evalIn env "(ma::helper 3)"))
    // неэкспортированное имя из глобальной области — неизвестный символ
    Assert.ThrowsAny<exn>(fun () -> evalIn env "(helper 3)" |> ignore) |> ignore

[<Fact>]
let ``модуль: пользовательский define с тем же именем не перекрывает приватное имя модуля`` () =
    let env = newEnv ()
    loadText env "a" modA |> ignore
    evalIn env "(define (helper x) 999)" |> ignore
    Assert.Equal("20", show (evalIn env "(f 2)"))          // f по-прежнему зовёт ma::helper
    Assert.Equal("999", show (evalIn env "(helper 1)"))
    // а приватное имя можно переопределить квалифицированно (пользователь может всё)
    evalIn env "(define (ma::helper x) 1)" |> ignore
    Assert.Equal("1", show (evalIn env "(f 2)"))

[<Fact>]
let ``модуль: позднее связывание экспорта сохранено — переопределение f видно вызывающим`` () =
    let env = newEnv ()
    loadText env "b" "(module mb (export f g))\n(define (f x) x)\n(define (g x) (+ 1 (f x)))\n" |> ignore
    Assert.Equal("6", show (evalIn env "(g 5)"))
    evalIn env "(define (f x) 100)" |> ignore
    Assert.Equal("101", show (evalIn env "(g 5)"))

[<Fact>]
let ``модуль: два модуля не экспортируют одно имя`` () =
    let env = newEnv ()
    loadText env "a" modA |> ignore
    let msg = loadError env "x" "(module mx (export f))\n(define (f x) 1)\n"
    Assert.Contains("модуль mx экспортирует имя f", msg)
    Assert.Contains("уже экспортирует модуль ma", msg)

[<Fact>]
let ``модуль: экспорт неопределённого имени — ошибка при загрузке`` () =
    let env = newEnv ()
    let msg = loadError env "x" "(module mx (export nope))\n(define (f x) 1)\n"
    Assert.Contains("экспортирует имя nope, но не определяет его", msg)

[<Fact>]
let ``модуль: определение имени, которое экспортирует другой модуль, — ошибка (чужой экспорт не переопределяют)`` () =
    let env = newEnv ()
    loadText env "a" modA |> ignore
    let msg = loadError env "x" "(module mx (export))\n(define (f x) 1)\n"
    Assert.Contains("определяет имя f, которое экспортирует модуль ma", msg)

[<Fact>]
let ``модуль: имя встроенной функции нельзя ни экспортировать, ни определить приватно`` () =
    let env = newEnv ()
    Assert.Contains("совпадающее со встроенной функцией", loadError env "x" "(module mx (export car))\n(define (car x) x)\n")
    Assert.Contains("совпадающее со встроенной функцией", loadError env "y" "(module my (export))\n(define (car x) x)\n")

[<Fact>]
let ``модуль: один и тот же метод (defmethod) из двух модулей — ошибка; пользователь переопределяет свободно`` () =
    let env = newEnv ()
    loadText env "a" "(module m1 (export))\n(defmethod zop (any) (x) 1)\n" |> ignore
    let msg = loadError env "b" "(module m2 (export))\n(defmethod zop (any) (x) 2)\n"
    Assert.Contains("уже определён модулем m1", msg)
    evalIn env "(defmethod zop (any) (x) 3)" |> ignore          // пользовательский код — без ограничений
    loadText env "c" "(module m3 (export))\n(defmethod zop (any) (x) 4)\n" |> ignore   // владение снято пользователем

[<Fact>]
let ``модуль: условие правила (defrule) видит приватные имена модуля`` () =
    let env = newEnv ()
    loadText env "r" "(module mr (export))\n(define (my-pred x) (equal? x 1))\n(defrule zz-rule (zz ?x) 7 (my-pred ?x))\n" |> ignore
    Assert.Equal("7", show (evalIn env "(simplify '(zz 1))"))
    Assert.Equal("(zz 2)", show (evalIn env "(simplify '(zz 2))"))

[<Fact>]
let ``модуль: в стеке ошибки и в имени функции — модуль::имя для приватных`` () =
    let env = newEnv ()
    loadText env "t" "(module mt (export run))\n(define (boom x) (error \"бум\"))\n(define (run) (boom 1))\n" |> ignore
    let ex = Assert.ThrowsAny<exn>(fun () -> evalIn env "(run)" |> ignore)
    let text = Debug.formatError (Debug.wrap ex)
    // (хвостовой вызов boom заменил кадр run — как и для любой функции)
    Assert.Contains("mt::boom", text)
    Assert.Contains("mt::boom", show (evalIn env "mt::boom"))

[<Fact>]
let ``модуль: (module ...) допустим только первой формой загружаемого файла`` () =
    let env = newEnv ()
    let msg = loadError env "x" "(define a 1)\n(module mx (export a))\n"
    Assert.Contains("только первой формой", msg)
    Assert.Contains("только первой формой", (Assert.ThrowsAny<exn>(fun () -> evalIn env "(module foo)" |> ignore)).Message)

[<Fact>]
let ``модуль: из нескольких файлов — общие приватные имена и накопление экспорта`` () =
    let env = newEnv ()
    loadText env "p1" "(module mm (export f))\n(define (f x) (h2 x))\n" |> ignore
    loadText env "p2" "(module mm (export g))\n(define (h2 x) (* 3 x))\n(define (g x) (f x))\n" |> ignore
    Assert.Equal("6", show (evalIn env "(f 2)"))
    Assert.Equal("9", show (evalIn env "(g 3)"))
    Assert.True((env.Lookup "h2").IsNone)
    Assert.Equal(2, env.Modules.["mm"].Files.Count)

[<Fact>]
let ``модуль: set! приватной и экспортированной переменной, приватный макрос`` () =
    let env = newEnv ()
    loadText env "s" ("(module ms (export get-n n bump!))\n(define n 0)\n(define counter 100)\n(define (get-n) n)\n"
                      + "(defmacro (inc! v) `(set! ,v (+ ,v 1)))\n(define (bump!) (begin (inc! n) (inc! counter) counter))\n") |> ignore
    Assert.Equal("101", show (evalIn env "(bump!)"))
    Assert.Equal("1", show (evalIn env "(get-n)"))
    Assert.Equal("1", show (evalIn env "n"))                 // экспортированная переменная — глобальная
    Assert.True((env.Lookup "counter").IsNone)
    Assert.Equal("101", show (evalIn env "ms::counter"))
    Assert.True((env.Lookup "inc!").IsNone)

[<Fact>]
let ``модуль: файл без (module) — как раньше, имена глобальные; повторная загрузка модуля допустима`` () =
    let env = newEnv ()
    loadText env "u" "(define (u-fn) 42)\n" |> ignore
    Assert.Equal("42", show (evalIn env "(u-fn)"))
    loadText env "a1" modA |> ignore
    loadText env "a2" modA |> ignore
    Assert.Equal("20", show (evalIn env "(f 2)"))

[<Fact>]
let ``модуль: макрос из модуля раскрывается в вызывающем коде через экспортированные имена`` () =
    let env = newEnv ()
    loadText env "m" ("(module mq (export twice twice-helper))\n(define (twice-helper e) (* 2 e))\n"
                      + "(defmacro (twice e) `(twice-helper ,e))\n") |> ignore
    Assert.Equal("14", show (evalIn env "(twice 7)"))
