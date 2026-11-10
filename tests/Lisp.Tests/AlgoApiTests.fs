// Тесты builtins единого контракта алгоритмов (шаг 21h'): счётчики, переключатель алгоритмов, журнал шагов (AlgoBuiltins.fs)
module AlgoApiTests

open System
open Xunit
open Types
open Reader
open Evaluator
open Printer

let private run (env: Env) (src: string) : string =
    readAll src |> List.fold (fun _ e -> eval e env) LispNil |> prettyPrint

// Программа входного математического языка; результат — s-выражение значения последнего оператора
let private runMath (env: Env) (src: string) : string =
    prettyPrint (eval (LispList [ LispSym "math-eval"; LispStr src ]) env)

let private gcdCall =
    "(poly-gcd '(* (+ (^ x 2) y z 1) (+ x y) (+ x z 2)) '(* (+ (^ x 2) y z 1) (+ x y) (+ (* x y) (* -3 z) 5)))"

[<Fact>]
let ``algo-stats: группы счётчиков с именами; сброс`` () =
    let env = newEnv ()
    run env "(algo-stats-reset)" |> ignore
    let all = run env "(algo-stats)"
    Assert.Contains("(factor.wang (full-lift 0) (subset-recombination 0) (fallback 0))", all)
    Assert.Contains("(gcd.probe (calls 0) (coprime-proved 0) (bound-found 0))", all)
    Assert.Contains("gcd.zippel (calls 0) (ok 0)", all)
    // одна группа
    Assert.Equal("((gcd.probe (calls 0) (coprime-proved 0) (bound-found 0)))", run env "(algo-stats 'gcd.probe)")
    // счётчики растут: НОД многочленов от трёх переменных (модулярный путь с пробой одной точкой)
    run env gcdCall |> ignore
    Assert.DoesNotContain("(gcd.probe (calls 0)", run env "(algo-stats 'gcd.probe)")
    Assert.Equal("#t", run env "(algo-stats-reset 'gcd.probe)")
    Assert.Equal("((gcd.probe (calls 0) (coprime-proved 0) (bound-found 0)))", run env "(algo-stats 'gcd.probe)")
    Assert.Contains("неизвестная группа nope", (Assert.ThrowsAny<exn>(fun () -> run env "(algo-stats 'nope)" |> ignore)).Message)
    Assert.Contains("неизвестная группа nope", (Assert.ThrowsAny<exn>(fun () -> run env "(algo-stats-reset 'nope)" |> ignore)).Message)

[<Fact>]
let ``set-algorithm: gcd — переключатель, прежнее значение, ошибки со списком допустимых`` () =
    let env = newEnv ()
    run env "(set-algorithm 'gcd 'auto)" |> ignore
    try
        Assert.Equal("auto", run env "(algorithm 'gcd)")
        Assert.Equal("auto", run env "(set-algorithm 'gcd 'zippel)")          // возвращает прежнее значение
        Assert.Equal("zippel", run env "(algorithm 'gcd)")
        Assert.Equal("(gcd zippel (auto zippel brown))", run env "(car (algorithms))")
        // режим действует: при zippel счётчик Зиппеля растёт, при brown — нет
        run env "(algo-stats-reset)" |> ignore
        run env gcdCall |> ignore
        Assert.DoesNotContain("(gcd.zippel (calls 0)", run env "(algo-stats 'gcd.zippel)")
        run env "(set-algorithm 'gcd 'brown)" |> ignore
        run env "(algo-stats-reset)" |> ignore
        run env gcdCall |> ignore
        Assert.Contains("(gcd.zippel (calls 0)", run env "(algo-stats 'gcd.zippel)")
        let e1 = Assert.ThrowsAny<exn>(fun () -> run env "(set-algorithm 'gcd 'magic)" |> ignore)
        Assert.Contains("допустимо: auto, zippel, brown", e1.Message)
        let e2 = Assert.ThrowsAny<exn>(fun () -> run env "(set-algorithm 'nope 'x)" |> ignore)
        Assert.Contains("неизвестный алгоритм nope (есть: gcd, groebner", e2.Message)
        Assert.Contains("неизвестный алгоритм nope", (Assert.ThrowsAny<exn>(fun () -> run env "(algorithm 'nope)" |> ignore)).Message)
    finally
        run env "(set-algorithm 'gcd 'auto)" |> ignore

[<Fact>]
let ``математический язык: algo_stats, set_algorithm`` () =
    let env = newEnv ()
    try
        Assert.Equal("auto", runMath env "set_algorithm(gcd, brown)")
        Assert.Equal("brown", runMath env "set_algorithm(gcd, auto)")
        Assert.Contains("gcd.probe", runMath env "algo_stats()")
        Assert.Equal("#t", runMath env "algo_stats_reset()")
    finally
        run env "(set-algorithm 'gcd 'auto)" |> ignore

[<Fact>]
let ``журнал шагов: step-log-on/off, record-step, step-log, capture-step-log`` () =
    let env = newEnv ()
    try
        run env "(step-log-off) (step-log-clear)" |> ignore
        Assert.Equal("#f", run env "(step-log-enabled?)")
        // выключен — record-step ничего не пишет
        Assert.Equal("#f", run env "(record-step \"раскрыть\" \"раскрываем скобки\" '(^ (+ x 1) 2) '(+ 1 (* 2 x) (^ x 2)))")
        Assert.Equal("()", run env "(step-log)")
        // включён — пишет по порядку
        Assert.Equal("#t", run env "(step-log-on)")
        Assert.Equal("#t", run env "(step-log-enabled?)")
        // старая форма (4 аргумента): приём-текст → заголовок, rule step; шаг S.1 — новая форма с rule и уровнем
        run env "(record-step \"раскрыть\" \"раскрываем скобки\" '(^ (+ x 1) 2) '(+ 1 (* 2 x) (^ x 2)))" |> ignore
        run env "(record-step 'collect-terms \"Приведение подобных\" \"x + x = 2x\" '(+ x x) '(* 2 x) 'detail)" |> ignore
        Assert.Equal("((step \"раскрыть\" \"раскрываем скобки\" (^ (+ x 1) 2) (+ 1 (* 2 x) (^ x 2)) main () 0) (collect-terms \"Приведение подобных\" \"x + x = 2x\" (+ x x) (* 2 x) detail () 0))",
                     run env "(step-log)")
        run env "(step-log-clear)" |> ignore
        Assert.Equal("()", run env "(step-log)")
        run env "(step-log-off)" |> ignore
        // capture-step-log: чистый журнал на время вычисления, результат и шаги; состояние восстанавливается
        let captured = run env "(capture-step-log (lambda () (begin (record-step \"п\" \"к\" 1 2) 'готово)))"
        Assert.Equal("(готово ((step \"п\" \"к\" 1 2 main () 0)))", captured)
        Assert.Contains("уровень шага main | detail", (Assert.ThrowsAny<exn>(fun () -> run env "(capture-step-log (lambda () (record-step 'a \"t\" \"c\" 1 2 'zzz)))" |> ignore)).Message)
        Assert.Equal("#f", run env "(step-log-enabled?)")
        Assert.Equal("()", run env "(step-log)")
        // язык: step_log_on(), record_step(...), step_log()
        Assert.Equal("#t", runMath env "step_log_on()")
        runMath env "record_step(\"п\", \"к\", x, y)" |> ignore
        Assert.Contains("\"п\"", runMath env "step_log()")
    finally
        run env "(step-log-off) (step-log-clear)" |> ignore

[<Fact>]
let ``канал условий: record-condition, conditions, дубликаты, conditions-clear, capture-conditions`` () =
    let env = newEnv ()
    try
        run env "(conditions-clear)" |> ignore
        Assert.Equal("()", run env "(conditions)")
        // всегда включён; #t — новое условие, #f — дубликат (первая причина остаётся)
        Assert.Equal("#t", run env "(record-condition '(/= a 0) \"делим на a\")")
        Assert.Equal("#f", run env "(record-condition '(/= a 0) \"другая причина\")")
        Assert.Equal("#t", run env "(record-condition '(> b 0) \"b положительно\")")
        Assert.Equal("(((/= a 0) \"делим на a\") ((> b 0) \"b положительно\"))", run env "(conditions)")
        // capture-conditions: чистый канал на время вычисления; внешний не меняется
        Assert.Equal("(готово (((/= c 0) \"п\")))", run env "(capture-conditions (lambda () (begin (record-condition '(/= c 0) \"п\") 'готово)))")
        Assert.Equal("(((/= a 0) \"делим на a\") ((> b 0) \"b положительно\"))", run env "(conditions)")
        // ошибка аргументов
        Assert.ThrowsAny<exn>(fun () -> run env "(record-condition '(/= a 0) 5)" |> ignore) |> ignore
        run env "(conditions-clear)" |> ignore
        Assert.Equal("()", run env "(conditions)")
    finally
        run env "(conditions-clear)" |> ignore
