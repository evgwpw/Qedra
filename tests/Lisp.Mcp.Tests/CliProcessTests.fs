// Шаг D1: процессные тесты командной строки — -e, --math -e, --help, неизвестный ключ, файл + -e
module CliProcessTests

open System
open System.IO
open Xunit
open CliProcess

[<Fact>]
let ``CLI: -e — значение последнего выражения, код 0`` () =
    let code, out, _ = runLisp [ "-e"; "(+ 1 2)" ]
    Assert.Equal(0, code)
    Assert.Equal("3", out)

[<Fact>]
let ``CLI: несколько -e — одно окружение, печатается последнее`` () =
    let code, out, _ = runLisp [ "-e"; "(define (f x) (* x x))"; "-e"; "(f 7)" ]
    Assert.Equal(0, code)
    Assert.Equal("49", out)

[<Fact>]
let ``CLI: --math -e — входной язык, mathPrintLang`` () =
    let code, out, _ = runLisp [ "--math"; "-e"; "simplify((x+y)^2)" ]
    Assert.Equal(0, code)
    Assert.Equal("(x + y)^2", out)

[<Fact>]
let ``CLI: -e с ошибкой — сообщение со стеком, код 1`` () =
    let code, out, _ = runLisp [ "-e"; "(car 'x)" ]
    Assert.Equal(1, code)
    Assert.Contains("car", out)

[<Fact>]
let ``CLI: --help / -h — справка, код 0`` () =
    for key in [ "--help"; "-h" ] do
        let code, out, _ = runLisp [ key ]
        Assert.Equal(0, code)
        Assert.Contains("--mcp", out)
        Assert.Contains("-e", out)

[<Fact>]
let ``CLI: неизвестный ключ — код 2, подсказка --help`` () =
    let code, out, _ = runLisp [ "--no-such-key" ]
    Assert.Equal(2, code)
    Assert.Contains("--help", out)

[<Fact>]
let ``CLI: файл + -e — файл загружен тихо, выражение видит определения`` () =
    let tmp = Path.Combine(Path.GetTempPath(), "d1-test-" + Guid.NewGuid().ToString("N").Substring(0, 8) + ".lisp")
    File.WriteAllText(tmp, "(define (g x) (+ x 100))")
    try
        let code, out, _ = runLisp [ tmp; "-e"; "(g 5)" ]
        Assert.Equal(0, code)
        Assert.Equal("105", out)       // без печати результата файла (тихая загрузка)
    finally
        File.Delete tmp

[<Fact>]
let ``CLI: -e и ограничение печати — обрезка с хвостом, set-print-limit 0 снимает`` () =
    let code, out, _ = runLisp [ "-e"; "(set-print-limit 50)"; "-e"; "(expand '(^ (+ x 1) 30))" ]
    Assert.Equal(0, code)
    Assert.Contains("обрезано:", out)
    let code2, out2, _ = runLisp [ "-e"; "(set-print-limit 0)"; "-e"; "(expand '(^ (+ x 1) 30))" ]
    Assert.Equal(0, code2)
    Assert.False(out2.Contains "обрезано:")

[<Fact>]
let ``CLI: show — печатает математическую запись, возвращает аргумент`` () =
    let code, out, _ = runLisp [ "-e"; "(show '(* 2 (+ x 1)))" ]
    Assert.Equal(0, code)
    Assert.Contains("2(x + 1)", out)       // печать show (mathPrint)
    Assert.Contains("(* 2 (+ x 1))", out)  // печать результата хостом (prettyPrint)

// --- Шаг D0: падения при битом prelude / битом синтаксисе (из отчёта о прогоне 21l.3) ---
// Раньше: ошибка в любом файле prelude → TypeInitializationException статического конструктора Evaluator
// → крах любого запуска Lisp.exe с необработанным исключением (exit -1)

[<Fact>]
let ``D0: битый prelude (кривой defrule) — сообщение с файлом/причиной в stderr, код 1, не крах`` () =
    let code, out, err =
        runLispInCopy (fun prelude -> File.AppendAllText(prelude, "\n(defrule d0-broken 0 x)\n")) [ "-e"; "(+ 1 2)" ]
    Assert.Equal(1, code)
    Assert.Contains("ОШИБКА ЗАГРУЗКИ БИБЛИОТЕКИ", err)
    Assert.Contains("prelude.lisp", err)
    Assert.Contains("d0-broken", err)      // причина ошибки (имя правила)
    Assert.DoesNotContain("TypeInitializationException", out + err)

[<Fact>]
let ``D0: битый prelude (незакрытая скобка) — сообщение со строкой, код 1, не крах`` () =
    let code, _, err =
        runLispInCopy (fun prelude -> File.AppendAllText(prelude, "\n(define (d0-broken x) (+ x 1\n")) [ "-e"; "1" ]
    Assert.Equal(1, code)
    Assert.Contains("ОШИБКА ЗАГРУЗКИ БИБЛИОТЕКИ", err)
    Assert.Contains("не закрыта скобка", err)

[<Fact>]
let ``D0: битый prelude — не ломает normal lib: runLispInCopy без мутаций работает`` () =
    let code, out, _ = runLispInCopy ignore [ "-e"; "(+ 1 2)" ]
    Assert.Equal(0, code)
    Assert.Equal("3", out)

[<Fact>]
let ``D0: битый .lisp-файл (незакрытая скобка) — сообщение, код 1 (раньше был 0)`` () =
    let tmp = Path.Combine(Path.GetTempPath(), "d0-bad-" + Guid.NewGuid().ToString("N").Substring(0, 8) + ".lisp")
    File.WriteAllText(tmp, "(define (f x) (+ x 1)")
    try
        let code, out, _ = runLisp [ tmp ]
        Assert.Equal(1, code)
        Assert.Contains("не закрыта скобка", out)
    finally
        File.Delete tmp

[<Fact>]
let ``D0: битый синтаксис в --math -e — сообщение, код 1 (раньше необработанное исключение, крах)`` () =
    let code, out, _ = runLisp [ "--math"; "-e"; "simplify((x+y" ]
    Assert.Equal(1, code)
    Assert.Contains("ОШИБКА", out)
    Assert.Contains("строка 1", out)

[<Fact>]
let ``D0: битый .mth-файл — сообщение, код 1`` () =
    let tmp = Path.Combine(Path.GetTempPath(), "d0-bad-" + Guid.NewGuid().ToString("N").Substring(0, 8) + ".mth")
    File.WriteAllText(tmp, "f(x) := sin(x")
    try
        let code, out, _ = runLisp [ tmp ]
        Assert.Equal(1, code)
        Assert.Contains("ОШИБКА", out)
    finally
        File.Delete tmp

[<Fact>]
let ``D0: корректные файлы — коды возврата не изменились (0)`` () =
    // регресс: обычные режимы после правок D0 работают как раньше
    let code1, out1, _ = runLisp [ "-e"; "(define (f x) (* x x))"; "-e"; "(f 7)" ]
    Assert.Equal(0, code1)
    Assert.Equal("49", out1)
    let code2, out2, _ = runLisp [ "--math"; "-e"; "simplify((x+y)^2)" ]
    Assert.Equal(0, code2)
    Assert.Equal("(x + y)^2", out2)
