// Тесты условных правил переписывания (defrule) и unwind-protect (Шаг 16, коммит 1).
// Правила глобальные: в тестах — уникальные имена правил (rt-...) и операторов (rt...), после теста все правила rt-* удаляются.
module RuleTests

open System.IO
open Xunit
open Types
open Reader
open Evaluator

let run (env: Env) (s: string) : LispValue =
    readAll s |> List.fold (fun _ e -> eval e env) LispNil

let pp (env: Env) (s: string) : string = Printer.prettyPrint (run env s)

// Выполнить тело с чисткой правил теста
let withRules (f: Env -> unit) : unit =
    let env = newEnv ()
    try f env
    finally
        for n in Rules.names () do
            if n.StartsWith "rt-" then Rules.remove n |> ignore
        Rules.tracing <- false

let failure (env: Env) (s: string) : string * Frame list =
    try
        run env s |> ignore
        failwith "ожидалась ошибка"
    with LispError (m, st, _) -> (m, st)

[<Fact>]
let ``безусловное правило`` () =
    withRules (fun env ->
        run env "(defrule rt-dbl (rtdbl ?x) (* 2 ?x))" |> ignore
        Assert.Equal("6", pp env "(simplify '(rtdbl 3))")
        Assert.Equal("(* 2 y)", pp env "(simplify '(rtdbl y))"))

[<Fact>]
let ``defrule возвращает имя; без правила выражение не меняется`` () =
    withRules (fun env ->
        Assert.Equal("(rtnone 3)", pp env "(simplify '(rtnone 3))")
        Assert.Equal("rt-r1", pp env "(defrule rt-r1 (rtnone ?x) ?x)")
        Assert.Equal("3", pp env "(simplify '(rtnone 3))"))

[<Fact>]
let ``условное правило: #t срабатывает, #f нет, unknown нет`` () =
    withRules (fun env ->
        run env "(defrule rt-c (rtcond ?x) (* 10 ?x) (if (number? ?x) #t (if (symbol? ?x) 'unknown #f)))" |> ignore
        Assert.Equal("30", pp env "(simplify '(rtcond 3))")                    // #t
        Assert.Equal("(rtcond u)", pp env "(simplify '(rtcond u))")             // unknown — не срабатывает
        Assert.Equal("(rtcond (f 1))", pp env "(simplify '(rtcond (f 1)))"))    // #f

[<Fact>]
let ``условие: другое истинное значение — не #t`` () =
    withRules (fun env ->
        run env "(defrule rt-t (rttruthy ?x) 1 42)" |> ignore
        Assert.Equal("(rttruthy 5)", pp env "(simplify '(rttruthy 5))")
        run env "(defrule rt-t (rttruthy ?x) 1 (number? ?x))" |> ignore
        Assert.Equal("1", pp env "(simplify '(rttruthy 5))"))

[<Fact>]
let ``условие видит окружение определения и связи образца`` () =
    withRules (fun env ->
        run env "(define rt-limit 10)" |> ignore
        run env "(defrule rt-lim (rtlim ?x) small (< ?x rt-limit))" |> ignore
        Assert.Equal("small", pp env "(simplify '(rtlim 3))")
        Assert.Equal("(rtlim 30)", pp env "(simplify '(rtlim 30))")
        run env "(set! rt-limit 100)" |> ignore
        Assert.Equal("small", pp env "(simplify '(rtlim 30))"))

[<Fact>]
let ``повторная переменная связывается согласованно`` () =
    withRules (fun env ->
        run env "(defrule rt-same (rtsame ?x ?x) 1)" |> ignore
        Assert.Equal("1", pp env "(simplify '(rtsame a a))")
        Assert.Equal("1", pp env "(simplify '(rtsame (+ a b) (+ b a)))")
        Assert.Equal("(rtsame a b)", pp env "(simplify '(rtsame a b))"))

[<Fact>]
let ``образец канонизируется при регистрации`` () =
    withRules (fun env ->
        // (- ?x ?y) хранится как (+ ?x (* -1 ?y)) — так выглядит упрощённый аргумент
        run env "(defrule rt-canon (rtcanon (- ?x ?y)) (rtpair ?x ?y))" |> ignore
        Assert.Equal("(rtpair a b)", pp env "(simplify '(rtcanon (- a b)))")
        // порядок слагаемых канонический: (+ ?b ?a) → (+ ?a ?b)
        run env "(defrule rt-canon2 (rtcanon2 (+ ?b ?a)) (rtpair ?a ?b))" |> ignore
        Assert.Equal("(rtpair x y)", pp env "(simplify '(rtcanon2 (+ y x)))"))

[<Fact>]
let ``порядок правил: первое сработавшее побеждает`` () =
    withRules (fun env ->
        run env "(defrule rt-o1 (rtord ?x) 1)" |> ignore
        run env "(defrule rt-o2 (rtord ?x) 2)" |> ignore
        Assert.Equal("(rt-o1 rt-o2)", pp env "(rules 'rtord)")
        Assert.Equal("1", pp env "(simplify '(rtord a))")
        // первое с невыполненным условием пропускается
        run env "(defrule rt-o1 (rtord ?x) 1 #f)" |> ignore
        Assert.Equal("2", pp env "(simplify '(rtord a))"))

[<Fact>]
let ``повторный defrule с тем же именем заменяет правило на месте`` () =
    withRules (fun env ->
        run env "(defrule rt-p1 (rtrep ?x) 1)" |> ignore
        run env "(defrule rt-p2 (rtrep ?x) 2)" |> ignore
        run env "(defrule rt-p1 (rtrep ?x) 11)" |> ignore
        Assert.Equal("(rt-p1 rt-p2)", pp env "(rules 'rtrep)")
        Assert.Equal("11", pp env "(simplify '(rtrep a))")
        // смена оператора: правило уходит из старого списка
        run env "(defrule rt-p1 (rtrep2 ?x) 5)" |> ignore
        Assert.Equal("(rt-p2)", pp env "(rules 'rtrep)")
        Assert.Equal("(rt-p1)", pp env "(rules 'rtrep2)"))

[<Fact>]
let ``remove-rule и rule-names`` () =
    withRules (fun env ->
        run env "(defrule rt-rm (rtrm ?x) 1)" |> ignore
        Assert.Equal("1", pp env "(simplify '(rtrm a))")
        Assert.Equal("#t", pp env "(remove-rule 'rt-rm)")
        Assert.Equal("(rtrm a)", pp env "(simplify '(rtrm a))")
        Assert.Equal("#f", pp env "(remove-rule 'rt-rm)")
        Assert.Equal("()", pp env "(rules 'rtrm)")
        run env "(defrule rt-nm (rtrm ?x) 1)" |> ignore
        Assert.True((pp env "(rule-names)").Contains "rt-nm"))

[<Fact>]
let ``правило срабатывает во вложенном подвыражении`` () =
    withRules (fun env ->
        run env "(defrule rt-sub (rtsub ?x) (* ?x ?x))" |> ignore
        Assert.Equal("(+ 1 (^ y 2))", pp env "(simplify '(+ 1 (rtsub y)))")
        Assert.Equal("(sin (^ y 2))", pp env "(simplify '(sin (rtsub y)))")
        // результат замены снова упрощается и подпадает под другие правила
        run env "(defrule rt-sub2 (rtsub2 ?x) (rtsub ?x))" |> ignore
        Assert.Equal("(^ z 2)", pp env "(simplify '(rtsub2 z))"))

[<Fact>]
let ``бесконечное переписывание даёт ловимую ошибку`` () =
    withRules (fun env ->
        run env "(defrule rt-ia (rta ?x) (rtb ?x))" |> ignore
        run env "(defrule rt-ib (rtb ?x) (rta ?x))" |> ignore
        let msg, _ = failure env "(simplify '(rta 1))"
        Assert.Contains("правило rt-i", msg)
        Assert.Contains("лимит", msg)
        // ловится try, интерпретатор остаётся рабочим
        Assert.Equal("#t", pp env "(try (simplify '(rta 1)) (lambda (e) #t))")
        run env "(remove-rule 'rt-ib)" |> ignore
        Assert.Equal("(rtb 1)", pp env "(simplify '(rta 1))"))

[<Fact>]
let ``образец без оператора-символа — ошибка`` () =
    withRules (fun env ->
        let msg, _ = failure env "(defrule rt-bad ?x 1)"
        Assert.Contains("defrule", msg)
        let msg2, _ = failure env "(defrule rt-bad2 5 1)"
        Assert.Contains("defrule", msg2))

[<Fact>]
let ``ошибка в условии пробрасывается`` () =
    withRules (fun env ->
        run env "(defrule rt-err (rterr ?x) 1 (error \"плохое условие\"))" |> ignore
        let msg, _ = failure env "(simplify '(rterr 1))"
        Assert.Contains("плохое условие", msg))

[<Fact>]
let ``trace-rules печатает срабатывания`` () =
    let w = new StringWriter()
    withRules (fun env ->
        Debug.writer <- w
        try
            run env "(defrule rt-tr (rttr ?x) (* 2 ?x))" |> ignore
            run env "(simplify '(rttr 1))" |> ignore   // до trace — тишина
            Assert.Equal("", w.ToString())
            run env "(trace-rules)" |> ignore
            run env "(simplify '(rttr y))" |> ignore
            run env "(untrace-rules)" |> ignore
            run env "(simplify '(rttr z))" |> ignore
        finally Debug.writer <- null)
    Assert.Equal("правило rt-tr: (rttr y) → (* 2 y)\n", w.ToString().Replace("\r\n", "\n"))

// --- unwind-protect ---

[<Fact>]
let ``unwind-protect: нормальный выход — значение тела, очистка выполнена по порядку`` () =
    let env = newEnv ()
    run env "(define ulog '())" |> ignore
    Assert.Equal("7", pp env "(unwind-protect (+ 3 4) (set! ulog (cons 1 ulog)) (set! ulog (cons 2 ulog)))")
    Assert.Equal("(2 1)", pp env "ulog")

[<Fact>]
let ``unwind-protect: ошибка — очистка выполняется, ошибка пробрасывается с сообщением и стеком`` () =
    let env = newEnv ()
    run env "(define cleaned 0) (define (uw-fail x) (error \"сбой\" x)) (define (uw-outer x) (unwind-protect (uw-fail x) (set! cleaned (+ cleaned 1))))" |> ignore
    let msg, stack = failure env "(uw-outer 5)"
    Assert.Contains("сбой", msg)
    Assert.Equal("1", pp env "cleaned")
    let names = stack |> List.map (fun f -> f.Name)
    Assert.Contains("uw-fail", names)
    Assert.Contains("uw-outer", names)

[<Fact>]
let ``unwind-protect: try снаружи ловит, глубина стека цела`` () =
    let env = newEnv ()
    run env "(define cleaned 0)" |> ignore
    Assert.Equal("\"поймано\"", pp env "(try (unwind-protect (error \"x\") (set! cleaned 1)) (lambda (e) \"поймано\"))")
    Assert.Equal("1", pp env "cleaned")
    Assert.Equal(0, Debug.depth)
    // вложенные unwind-protect: очистка изнутри наружу
    run env "(define ulog '())" |> ignore
    Assert.Equal("#t", pp env "(try (unwind-protect (unwind-protect (error \"x\") (set! ulog (cons 'inner ulog))) (set! ulog (cons 'outer ulog))) (lambda (e) #t))")
    Assert.Equal("(outer inner)", pp env "ulog")

[<Fact>]
let ``unwind-protect: ошибка в очистке заменяет исходную`` () =
    let env = newEnv ()
    let msg, _ = failure env "(unwind-protect (error \"первая\") (error \"вторая\"))"
    Assert.Contains("вторая", msg)

// --- Домены: комплексные числа (в Lisp их не построить — проверяем на F#-уровне) ---

[<Fact>]
let ``in? и sign-of для комплексного числа`` () =
    let env = newEnv ()
    let call (f: string) (args: LispValue list) = Printer.prettyPrint (apply (env.Lookup f).Value args)
    let z = LispComplex (LispInteger 3I, LispInteger 2I)
    Assert.Equal("#t", call "in?" [ z; env.Lookup("complexes").Value ])
    Assert.Equal("#f", call "in?" [ z; env.Lookup("reals").Value ])
    Assert.Equal("#f", call "in?" [ z; env.Lookup("naturals").Value ])
    Assert.Equal("#f", call "in?" [ z; env.Lookup("positive").Value ])
    Assert.Equal("unknown", call "sign-of" [ z ])

[<Fact>]
let ``Rules: правила prelude зарегистрированы и видны через rule-names`` () =
    let env = newEnv ()
    let names = pp env "(rule-names)"
    for n in [ "abs-nonnegative"; "sqrt-square-real"; "pow-pow"; "cos-integer-pi"; "exp-log" ] do
        Assert.Contains(n, names)
