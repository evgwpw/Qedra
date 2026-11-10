// Шаг D3a: контекст в ошибках builtins — имя функции, номер аргумента, ожидание и печать значения
module ErrorContextTests

open Xunit
open Types
open Reader
open Evaluator
open Builtins

let evalStr (s: string) : LispValue = readAll s |> List.head |> fun e -> eval e globalEnv

// Ошибка вычисления строки; возвращает текст исключения (уже Debug.wrap-нут охраной eval)
let errorText (s: string) : string =
    try
        evalStr s |> ignore
        failwith "ожидалась ошибка"
    with
    | :? System.Exception as ex -> ex.Message

// --- D3a: сообщения с именем функции, аргументом и значением ---

[<Fact>]
let ``D3a: object-type — имя функции, аргумент 1, ожидание, значение`` () =
    Assert.Equal("object-type: аргумент 1 — ожидался объект, получено: 5", errorText "(object-type 5)")

[<Fact>]
let ``D3a: vlength — вектор, получен список`` () =
    Assert.Equal("vlength: аргумент 1 — ожидался вектор, получено: (1 2)", errorText "(vlength '(1 2))")

[<Fact>]
let ``D3a: vector->list / list->vector`` () =
    Assert.Equal("vector->list: аргумент 1 — ожидался вектор, получено: sym", errorText "(vector->list 'sym)")
    // list->vector с вектором: сообщение из общего помощника listOf (с печатью значения)
    Assert.Equal("list->vector: ожидается список, получено #(1 2)", errorText "(list->vector #(1 2))")

[<Fact>]
let ``D3a: error-message / set-max-depth`` () =
    Assert.Equal("error-message: аргумент 1 — ожидался объект ошибки, получено: 7", errorText "(error-message 7)")
    Assert.Equal("set-max-depth: аргумент 1 — ожидалось положительное целое, получено: \"n\"", errorText "(set-max-depth \"n\")")

[<Fact>]
let ``D3a: diff — первый аргумент символ`` () =
    Assert.Equal("diff: аргумент 1 — ожидался символ (имя переменной), получено: 5", errorText "(diff 5 '(+ x 1))")

[<Fact>]
let ``D3a: string->symbol — строка`` () =
    Assert.Equal("string->symbol: аргумент 1 — ожидалась строка, получено: abc", errorText "(string->symbol 'abc)")

[<Fact>]
let ``D3a: set-print-limit — целое число`` () =
    Assert.Equal("set-print-limit: аргумент 1 — ожидалось целое число, получено: (1 2)", errorText "(set-print-limit '(1 2))")

[<Fact>]
let ``D3a: длинное значение обрезается до 200 символов`` () =
    // большое выражение — печать в сообщении обрезается, но не влияет на нормальную печать
    // выражение с длинной печатью (> 200 символов) — в сообщении обрезается с хвостом «… [обрезано]»
    let big2 = "(* " + (String.replicate 150 "x ") + "1)"
    let msg = errorText ("(object-type (quote " + big2 + "))")
    ignore big2
    Assert.Contains("… [обрезано]", msg)

[<Fact>]
let ``D3a: число аргументов по-прежнему ошибка без значения`` () =
    // арность — не значение: сообщение без «получено» (как раньше)
    Assert.Equal("object-type: один аргумент", errorText "(object-type)")
