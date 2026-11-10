// Тесты парсера (Reader.fs)
module ReaderTests

open System.Numerics
open Xunit
open Types
open Reader

// --- Парсинг чисел ---

[<Fact>]
let ``Парсинг целого числа`` () =
    let result = readAll "42"
    Assert.Equal(1, result.Length)
    match result.[0] with
    | LispInteger n -> Assert.Equal(42I, n)
    | other -> Assert.Fail($"Ожидался LispInteger, получено {other}")

[<Fact>]
let ``Парсинг большого целого (BigInteger)`` () =
    let result = readAll "100000000000000000000"
    match result.[0] with
    | LispInteger n -> Assert.Equal(100000000000000000000I, n)
    | other -> Assert.Fail($"Ожидался LispInteger, получено {other}")

[<Fact>]
let ``Парсинг отрицательного целого`` () =
    let result = readAll "-7"
    match result.[0] with
    | LispInteger n -> Assert.Equal(-7I, n)
    | other -> Assert.Fail($"Ожидался LispInteger, получено {other}")

[<Fact>]
let ``Парсинг рационального числа`` () =
    let result = readAll "3/4"
    match result.[0] with
    | LispRational (p, q) ->
        Assert.Equal(3I, p)
        Assert.Equal(4I, q)
    | other -> Assert.Fail($"Ожидался LispRational, получено {other}")

[<Fact>]
let ``Парсинг вещественного числа`` () =
    let result = readAll "3.14"
    match result.[0] with
    | LispFloat f -> Assert.Equal(3.14, f, 2)
    | other -> Assert.Fail($"Ожидался LispFloat, получено {other}")

[<Fact>]
let ``Парсинг булева true`` () =
    let result = readAll "#t"
    match result.[0] with
    | LispBool true -> ()
    | other -> Assert.Fail($"Ожидался LispBool true, получено {other}")

[<Fact>]
let ``Парсинг булева false`` () =
    let result = readAll "#f"
    match result.[0] with
    | LispBool false -> ()
    | other -> Assert.Fail($"Ожидался LispBool false, получено {other}")

// --- Парсинг строк и символов ---

[<Fact>]
let ``Парсинг строки`` () =
    let result = readAll "\"hello\""
    match result.[0] with
    | LispStr s -> Assert.Equal("hello", s)
    | other -> Assert.Fail($"Ожидался LispStr, получено {other}")

[<Fact>]
let ``Парсинг символа`` () =
    let result = readAll "foo"
    match result.[0] with
    | LispSym s -> Assert.Equal("foo", s)
    | other -> Assert.Fail($"Ожидался LispSym, получено {other}")

// --- Парсинг списков ---

[<Fact>]
let ``Парсинг пустого списка`` () =
    let result = readAll "()"
    match result.[0] with
    | LispList [] -> ()
    | other -> Assert.Fail($"Ожидался пустой LispList, получено {other}")

[<Fact>]
let ``Парсинг списка чисел`` () =
    let result = readAll "(1 2 3)"
    match result.[0] with
    | LispList items ->
        Assert.Equal(3, items.Length)
        match items.[0], items.[1], items.[2] with
        | LispInteger a, LispInteger b, LispInteger c ->
            Assert.Equal(1I, a)
            Assert.Equal(2I, b)
            Assert.Equal(3I, c)
        | other -> Assert.Fail($"Элементы не LispInteger: {other}")
    | other -> Assert.Fail($"Ожидался LispList, получено {other}")

[<Fact>]
let ``Парсинг вложенного списка`` () =
    let result = readAll "(+ 1 (* 2 3))"
    match result.[0] with
    | LispList [a; b; c] ->
        match a with LispSym s -> Assert.Equal("+", s) | other -> Assert.Fail($"a = {other}")
        match b with
        | LispInteger n -> Assert.Equal(1I, n)
        | other -> Assert.Fail($"b = {other}")
        match c with
        | LispList [x; y; z] ->
            match x with LispSym s -> Assert.Equal("*", s) | other -> Assert.Fail($"x = {other}")
            match y with
            | LispInteger n -> Assert.Equal(2I, n)
            | other -> Assert.Fail($"y = {other}")
            match z with
            | LispInteger n -> Assert.Equal(3I, n)
            | other -> Assert.Fail($"z = {other}")
        | other -> Assert.Fail($"c = {other}")
    | other -> Assert.Fail($"Ожидался LispList из 3 элементов, получено {other}")

// --- Quote ---

[<Fact>]
let ``Парсинг quote`` () =
    let result = readAll "'foo"
    match result.[0] with
    | LispList [LispSym "quote"; LispSym "foo"] -> ()
    | other -> Assert.Fail($"Ожидался (quote foo), получено {other}")

[<Fact>]
let ``Парсинг quote списка`` () =
    let result = readAll "'(1 2 3)"
    match result.[0] with
    | LispList [LispSym "quote"; inner] ->
        match inner with
        | LispList items ->
            Assert.Equal(3, items.Length)
            items |> List.iter (fun item ->
                match item with
                | LispInteger _ -> ()
                | other -> Assert.Fail($"Элемент не LispInteger: {other}"))
        | other -> Assert.Fail($"Внутренний список: {other}")
    | other -> Assert.Fail($"Ожидался (quote (1 2 3)), получено {other}")

// --- Множественные выражения ---

[<Fact>]
let ``Парсинг нескольких выражений`` () =
    let result = readAll "1 2 3"
    Assert.Equal(3, result.Length)

// --- Комментарии ---

[<Fact>]
let ``Пропуск комментариев`` () =
    let result = readAll "; это комментарий\n42"
    Assert.Equal(1, result.Length)
    match result.[0] with
    | LispInteger n -> Assert.Equal(42I, n)
    | other -> Assert.Fail($"Ожидался 42, получено {other}")

// --- Шаг 20: несбалансированные скобки — ошибка, а не молчаливая потеря остатка ---

[<Fact>]
let ``Лишняя закрывающая скобка — ошибка со строкой`` () =
    let ex = Assert.ThrowsAny<exn>(fun () -> readAll "(+ 1 2)\n(define x 1))\n(define y 2)" |> ignore)
    Assert.Contains("строка 2", ex.Message)
    Assert.Contains("лишняя", ex.Message)

[<Fact>]
let ``Незакрытая форма в конце — ошибка с номером строки начала формы`` () =
    let ex = Assert.ThrowsAny<exn>(fun () -> readAll "(define a 1)\n\n(define (f x)\n  (+ x 1)\n" |> ignore)
    Assert.Contains("строка 3", ex.Message)

[<Fact>]
let ``Незакрытая строка — ошибка`` () =
    let ex = Assert.ThrowsAny<exn>(fun () -> readAll "(define a 1)\n(display \"abc)" |> ignore)
    Assert.Contains("строка 2", ex.Message)

[<Fact>]
let ``Скобки внутри строк и комментариев не считаются`` () =
    Assert.Equal(1, (readAll "(f \"(\" ) ; )))").Length)

[<Fact>]
let ``load: ошибка баланса содержит имя файла`` () =
    let tmp = System.IO.Path.Combine(System.IO.Path.GetTempPath(), "lisp_test_unbalanced.lisp")
    System.IO.File.WriteAllText(tmp, "(define a 1)\n(define b 2))\n(define c 3)")
    try
        let ex = Assert.ThrowsAny<exn>(fun () -> Evaluator.loadIntoEnv tmp Evaluator.globalEnv |> ignore)
        Assert.Contains("lisp_test_unbalanced.lisp", ex.Message)
        Assert.Contains("строка 2", ex.Message)
    finally
        System.IO.File.Delete tmp

// --- Шаг 21d: точечные пары ---

[<Fact>]
let ``Точечная пара: (a . b), цепочка, хвост-список сливается`` () =
    match readAll "(1 . 2)" with
    | [ LispPair (LispInteger a, LispInteger b) ] -> Assert.Equal((1I, 2I), (a, b))
    | other -> failwithf "ожидалась пара, получено %A" other
    Assert.Equal("(1 2 . 3)", Printer.prettyPrint (readAll "(1 2 . 3)").Head)
    Assert.Equal("(a b c)", Printer.prettyPrint (readAll "(a . (b c))").Head)
    Assert.Equal("(a)", Printer.prettyPrint (readAll "(a . ())").Head)

[<Fact>]
let ``Точечная пара: ошибки записи и позиции форм рядом с парой`` () =
    Assert.Throws<exn>(fun () -> readAll "(1 . )" |> ignore) |> ignore
    Assert.Throws<exn>(fun () -> readAll "(1 . 2 3)" |> ignore) |> ignore
    // форма с парой внутри не мешает вычислению и позициям других форм файла
    let forms = readAllFrom "<repl>" "(define (f x) (car (cons x 1)))\n(quote (a . b))\n(f 5)"
    let env = Evaluator.newEnv ()
    let last = forms |> List.fold (fun _ e -> Evaluator.eval e env) LispNil
    Assert.Equal("5", Printer.prettyPrint last)
