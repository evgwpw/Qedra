// Шаг D1: ограничение печати результата (Printer.PrintLimit / limitPrint) и builtin show
module PrintLimitTests

open Xunit
open Types
open Reader
open Evaluator
open Printer
open MathPrinter

let ev (code: string) : LispValue = readAll code |> List.head |> fun e -> eval e (newEnv ())

[<Fact>]
let ``лимит: 0 (по умолчанию) — строка не меняется`` () =
    Printer.PrintLimit <- 0
    let v = ev "(expand '(^ (+ x 1) 10))"
    let s = prettyPrint v
    Assert.True((s = limitPrint v s))

[<Fact>]
let ``лимит: короткая строка — без изменений`` () =
    Printer.PrintLimit <- 2000
    let v = ev "'(* 2 (+ x 1))"
    let s = prettyPrint v
    Assert.True((s = limitPrint v s))

[<Fact>]
let ``лимит: длинная — обрезана, итог не длиннее лимита, хвост с числом символов и узлов`` () =
    Printer.PrintLimit <- 100
    try
        let v = ev "(expand '(^ (+ x 1) 20))"
        let s = prettyPrint v
        let r = limitPrint v s
        Assert.True(r.Length <= 100, sprintf "длина %d" r.Length)
        Assert.Contains("обрезано: ", r)
        Assert.Contains(" узлов]", r)
        Assert.True(r.StartsWith s.[0..9], "начало сохранено")
    finally
        Printer.PrintLimit <- 0

[<Fact>]
let ``лимит: countNodes — атом 1, список 1 + все элементы (включая голову)`` () =
    Assert.Equal(1, countNodes (LispSym "x"))
    // (* 2 x): 1 (список) + * + 2 + x = 4; (f (* 2 x)) — 1 + f + 4 = 6
    Assert.Equal(4, countNodes (readAll "(* 2 x)" |> List.head))
    Assert.Equal(6, countNodes (readAll "(f (* 2 x))" |> List.head))

[<Fact>]
let ``show: печатает математическую запись и возвращает аргумент`` () =
    Printer.PrintLimit <- 0
    let v = ev "(show '(* 2 (+ x 1)))"   // вывод в stdout — проверяется процессными тестами
    Assert.Equal("(* 2 (+ x 1))", prettyPrint v)

[<Fact>]
let ``set-print-limit: устанавливает лимит`` () =
    try
        ev "(set-print-limit 77)" |> ignore
        Assert.Equal(77, Printer.PrintLimit)
        ev "(set-print-limit 0)" |> ignore
        Assert.Equal(0, Printer.PrintLimit)
    finally
        Printer.PrintLimit <- 0

