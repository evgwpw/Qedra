// Тесты шага 21h, мост выражений для интегрирования рациональных функций (RatIntExpr.fs, Lisp.Core): builtin rat-integrate,
// печать и чтение root-sum. Чистая алгебра ЛРТ/Эрмита (RatInt.fs) — в Cas.Algebra.Tests (RatIntTests.fs)
module RatIntExprTests

open Xunit
open Types
open Numeric

[<Fact>]
let ``rat-integrate (builtin): полином, рациональная часть, логарифмическая часть`` () =
    let v = Evaluator.eval (Reader.readAll "(rat-integrate '(/ (+ (^ x 6) 1) (* x (+ x 1) (^ (+ x 2) 2))) 'x 't)" |> List.head) Evaluator.globalEnv
    match v with
    | LispList [ p; g; LispList terms; _scale ] ->
        Assert.NotEqual(LispInteger 0I, p)
        Assert.NotEqual(LispInteger 0I, g)
        Assert.NotEmpty terms
    | _ -> failwithf "неожиданный результат %s" (Printer.prettyPrint v)

// ---------- root-sum: печать и чтение в обоих режимах ----------

[<Fact>]
let ``root-sum: rootsum(E, t, Q) ↔ (root-sum t Q E), round-trip mathPrint и mathPrintLang`` () =
    let src = "rootsum(t*log(x + 5*t), t, 625*t^4 + 5*t + 1)"
    let e = MathReader.mathParse src
    match e with
    | LispList [ LispSym "root-sum"; LispSym "t"; q; body ] ->
        Assert.Equal("(+ (* 625 (^ t 4)) (* 5 t) 1)", Printer.prettyPrint q)
        Assert.Equal("(* t (log (+ x (* 5 t))))", Printer.prettyPrint body)
    | _ -> failwithf "неожиданный разбор %s" (Printer.prettyPrint e)
    let shown = MathPrinter.mathPrint e
    Assert.Equal("rootsum(t*log(x + 5t), t, 625t^4 + 5t + 1)", shown)
    Assert.True(structEqual (MathReader.mathParse shown) e)
    let lang = MathPrinter.mathPrintLang e
    Assert.Equal(shown, lang)
    Assert.True(structEqual (List.head (MathReader.mathParseProgram lang)) e)

[<Fact>]
let ``root-sum: вложенные суммы и отрицательные коэффициенты читаются обратно`` () =
    let src = "rootsum(rootsum(s - t, s, s^2 + 2) * log(x - t), t, t^3 - t - 1)"
    let e = MathReader.mathParse src
    Assert.True(structEqual (MathReader.mathParse (MathPrinter.mathPrint e)) e)
    Assert.True(structEqual (List.head (MathReader.mathParseProgram (MathPrinter.mathPrintLang e))) e)
