// Тесты канонической формы упрощателя (Шаг 13): порядок orderp, сбор подобных и степеней,
// некоммутативные множители, идемпотентность, diff/integrate/печать в канонической форме
module CanonicalTests

open Xunit
open Types
open Reader
open Numeric
open Simplify
open Order
open Expand
open Factor
open Evaluator
open Printer

let parse (s: string) : LispValue = readAll s |> List.head

// simplify строки → s-выражение строкой
let simp (s: string) : string = parse s |> simplify |> prettyPrint

let evalStr (s: string) : LispValue =
    readAll s |> List.head |> fun e -> eval e globalEnv

let eq (expected: string) (actual: string) = Assert.Equal(expected, actual)

// --- Примеры из постановки ---

[<Fact>]
let ``(- (+ x y) (+ y x)) → 0`` () =
    eq "0" (simp "(- (+ x y) (+ y x))")

[<Fact>]
let ``(* x x) → (^ x 2)`` () =
    eq "(^ x 2)" (simp "(* x x)")

[<Fact>]
let ``(+ x (- 0 x)) → 0`` () =
    eq "0" (simp "(+ x (- 0 x))")

[<Fact>]
let ``diff sin(x*x) упрощён: 2x cos(x^2)`` () =
    eq "(* 2 x (cos (^ x 2)))" (prettyPrint (evalStr "(diff 'x '(sin (* x x)))"))

// --- Форма: вычитание, деление, сплющивание ---

[<Fact>]
let ``вычитание и унарный минус → (* -1 ...)`` () =
    eq "(+ x (* -1 y))" (simp "(- x y)")
    eq "(* -1 x)" (simp "(- x)")
    eq "(* -1 x)" (simp "(- 0 x)")
    eq "-3" (simp "(- 3)")

[<Fact>]
let ``деление → степень -1, числовое — рациональное`` () =
    eq "(* x (^ y -1))" (simp "(/ x y)")
    eq "(^ x -1)" (simp "(/ 1 x)")
    eq "1/3" (simp "(/ 1 3)")
    eq "2" (simp "(/ 6 3)")
    eq "(* 1/2 x)" (simp "(/ x 2)")

[<Fact>]
let ``вложенные суммы и произведения сплющиваются, числа первыми`` () =
    eq "(+ 3 x y z)" (simp "(+ x (+ y (+ 1 z)) 2)")
    eq "(* 6 x y)" (simp "(* y (* 2 x) 3)")

[<Fact>]
let ``(- (* 2 (+ x y)) (* 2 (+ y x))) → 0 и -(a+b) раскрывается`` () =
    eq "0" (simp "(- (* 2 (+ x y)) (* 2 (+ y x)))")
    eq "(+ (* -1 x) (* -1 y))" (simp "(- (+ x y))")

// --- orderp ---

[<Fact>]
let ``orderp: числа < символы < составные`` () =
    Assert.True(orderp (LispInteger 5I) (LispSym "a"))
    Assert.False(orderp (LispSym "a") (LispInteger 5I))
    Assert.True(orderp (LispSym "z") (parse "(sin a)"))
    Assert.True(orderp (LispInteger 1I) (LispRational (3I, 2I)))
    Assert.True(orderp (LispFloat 1.5) (LispInteger 2I))

[<Fact>]
let ``orderp: символы по алфавиту, составные по оператору и аргументам`` () =
    Assert.True(orderp (LispSym "a") (LispSym "b"))
    Assert.False(orderp (LispSym "b") (LispSym "a"))
    Assert.True(orderp (parse "(cos x)") (parse "(sin x)"))
    Assert.True(orderp (parse "(sin a)") (parse "(sin b)"))
    Assert.True(orderp (parse "(sin x)") (parse "(sin x)"))      // равные — true (<=)
    Assert.True(orderp (parse "(f x)") (parse "(f x y)"))        // короткий раньше

[<Fact>]
let ``orderp: степени по основанию, затем по показателю`` () =
    Assert.True(orderp (LispSym "x") (parse "(^ x 2)"))
    Assert.True(orderp (parse "(^ x 2)") (parse "(^ x 3)"))
    Assert.True(orderp (parse "(^ x 3)") (LispSym "y"))

[<Fact>]
let ``orderp: builtin`` () =
    eq "#t" (prettyPrint (evalStr "(orderp 1 'x)"))
    eq "#f" (prettyPrint (evalStr "(orderp 'x 1)"))
    eq "#t" (prettyPrint (evalStr "(orderp 'x '(sin x))"))

[<Fact>]
let ``порядок термов: многочлен по возрастанию степени, константа первой`` () =
    eq "(+ 1 (* 3 x) (^ x 2) (* 2 (^ x 3)))" (simp "(+ (^ x 2) (* 3 x) 1 (* 2 (^ x 3)))")
    eq "(+ x y)" (simp "(+ y x)")
    eq "(* x y z)" (simp "(* z x y)")

// --- Сбор подобных и степеней ---

[<Fact>]
let ``сбор подобных в сумме`` () =
    eq "(* 3 x)" (simp "(+ x x x)")
    eq "(* 5 x)" (simp "(+ (* 2 x) (* 3 x))")
    eq "0" (simp "(- (* 2 x y) (* 2 y x))")
    eq "(+ (* 3 x) (* 2 y))" (simp "(+ x (* 2 y) (* 2 x))")

[<Fact>]
let ``сбор степеней в произведении`` () =
    eq "(^ x 5)" (simp "(* (^ x 2) (^ x 3))")
    eq "1" (simp "(* x (^ x -1))")
    eq "1" (simp "(/ x x)")
    eq "(^ x (+ a b))" (simp "(* (^ x a) (^ x b))")
    eq "(* (^ x 2) y)" (simp "(* x y x)")
    eq "1" (simp "(/ (+ x 1) (+ 1 x))")

[<Fact>]
let ``нулевые коэффициенты и степени убираются`` () =
    eq "y" (simp "(+ (* 2 x) y (* -2 x))")
    eq "0" (simp "(* 0 x y)")
    eq "1" (simp "(^ x 0)")
    eq "x" (simp "(* 1 x 1)")

// --- Степени ---

[<Fact>]
let ``степень степени и степень произведения`` () =
    eq "(^ x 6)" (simp "(^ (^ x 2) 3)")
    eq "(^ x 2)" (simp "(^ (^ x 1/2) 4)")
    eq "(* 4 (^ x 2))" (simp "(^ (* 2 x) 2)")
    eq "(* (^ x -1) (^ y -1))" (simp "(^ (* x y) -1)")

[<Fact>]
let ``степень степени с нецелым показателем не трогаем`` () =
    eq "(^ (^ x 2) 1/2)" (simp "(^ (^ x 2) 1/2)")
    eq "(^ (^ x a) b)" (simp "(^ (^ x a) b)")

[<Fact>]
let ``числа в рациональных степенях: точные корни`` () =
    eq "2" (simp "(^ 4 1/2)")
    eq "4" (simp "(^ 8 2/3)")
    eq "1/2" (simp "(^ 4 -1/2)")
    eq "3/2" (simp "(^ 9/4 1/2)")
    eq "(^ 2 1/2)" (simp "(^ 2 1/2)")
    // Шаг 18: корень из отрицательного рационального — мнимая единица %i (раньше оставался как есть)
    eq "(* 2 %i)" (simp "(^ -4 1/2)")
    eq "(^ -4 1/3)" (simp "(^ -4 1/3)")
    eq "1/8" (simp "(^ 2 -3)")
    eq "2" (simp "(* (^ 2 1/2) (^ 2 1/2))")

// --- Некоммутативность ---

// Шаг 15: plain-list векторов больше нет — некоммутативность проверяется на объектах-тензорах и векторах-массивах
let ev (s: string) : string = evalStr s |> prettyPrint

[<Fact>]
let ``isCommutative: тензоры и векторы-массивы — нет, остальное — да`` () =
    Assert.False(isCommutative (evalStr "(tensor '(1 2 3))"))
    Assert.False(isCommutative (evalStr "(vector 1 2 3)"))
    Assert.True(isCommutative (LispSym "x"))
    Assert.True(isCommutative (parse "(sin x)"))
    Assert.True(isCommutative (LispInteger 2I))
    // обычный список — просто выражение
    Assert.True(isCommutative (parse "(1 2 3)"))

[<Fact>]
let ``некоммутативные множители не переставляются`` () =
    // обычные векторы-массивы не имеют метода (* vector vector) — остаются в исходном порядке
    eq "(* #(1 2) #(3 4))" (ev "(simplify (list '* (vector 1 2) (vector 3 4)))")
    eq "(* #(3 4) #(1 2))" (ev "(simplify (list '* (vector 3 4) (vector 1 2)))")
    // коммутативные выносятся вперёд и сортируются
    eq "(* 2 a #(3 4) #(1 2))" (ev "(simplify (list '* (vector 3 4) 'a 2 (vector 1 2)))")

[<Fact>]
let ``тензорные правила работают через методы`` () =
    eq "[4, 6]" (ev "(simplify (list '+ (tensor '(1 2)) (tensor '(3 4))))")
    eq "[-2, -2]" (ev "(simplify (list '- (tensor '(1 2)) (tensor '(3 4))))")
    eq "[2, 4, 6]" (ev "(simplify (list '* 2 (tensor '(1 2 3))))")
    eq "[2, 4, 6]" (ev "(simplify (list '* (tensor '(1 2 3)) 2))")
    eq "[[2, 4], [6, 8]]" (ev "(simplify (list '* 2 (tensor '((1 2) (3 4)))))")
    eq "[(* 2 x), (* 4 x)]" (ev "(simplify (list '* 2 'x (tensor '(1 2))))")

[<Fact>]
let ``обычные списки не векторы: (+ (1 2) (3 4)) остаётся выражением`` () =
    eq "(+ (1 2) (3 4))" (simp "(+ (1 2) (3 4))")
    eq "(* 2 (1 2 3))" (simp "(* 2 (1 2 3))")

// --- Тригонометрия в n-арных суммах ---

[<Fact>]
let ``Пифагор в n-арной сумме с коэффициентами`` () =
    eq "1" (simp "(+ (^ (sin x) 2) (^ (cos x) 2))")
    eq "(+ 2 y)" (simp "(+ (* 2 (^ (sin x) 2)) y (* 2 (^ (cos x) 2)))")
    eq "(+ 4 y)" (simp "(+ 3 (^ (sin x) 2) y (^ (cos x) 2) 1 -1)")

[<Fact>]
let ``1 - cos^2 → sin^2 и 1 - sin^2 → cos^2`` () =
    eq "(^ (sin x) 2)" (simp "(- 1 (^ (cos x) 2))")
    eq "(^ (cos x) 2)" (simp "(- 1 (^ (sin x) 2))")
    eq "(+ y (^ (sin x) 2))" (simp "(+ y 1 (- 0 (^ (cos x) 2)))")
    eq "(* 2 (^ (sin x) 2))" (simp "(- 2 (* 2 (^ (cos x) 2)))")

[<Fact>]
let ``tan/sec в канонической форме`` () =
    eq "(* (^ (cos x) -1) (sin x))" (simp "(tan x)")
    eq "(^ (cos x) -1)" (simp "(sec x)")

// --- Идемпотентность ---

let private idempotentSet = [
    "(- (+ x y) (+ y x))"; "(* x x)"; "(+ x (- 0 x))"; "(/ x y)"; "(- x y z)"
    "(/ (* 6 x) (* 3 y))"; "(^ (* 2 x) 3)"; "(^ (+ x 1) -2)"; "(* (+ x 1) (+ x -1))"
    "(+ (* 2 (^ x 2)) (* 3 x) 1 (- 0 (* 5 x)))"; "(sin (* x x))"; "(tan x)"
    "(/ (+ x 1) (- x 1))"; "(- (/ 1 x) (/ 1 (* 2 x)))"; "(+ (^ (sin x) 2) (^ (cos x) 2) y)"
    "(* 2 x (1 2 3))"; "(+ (1 2) (3 4))"; "(* (3 4) b (1 2))"; "(^ 2 1/2)"; "(* (^ 2 1/2) x)"
    "(- (+ x y))"; "(* -1 (+ a (* -1 b)))"; "(^ (^ x a) 2)"; "(+ 1.5 x 2)"; "(exp (+ x x))"
    "(* (^ x a) (^ x b) y)"; "(+ (* a x) (* b x) c)"; "(/ 1 (+ x (* 2 y)))"
    "(- 2 (* 2 (^ (cos x) 2)))"; "(log (* x x))"; "(ln x)"
]

[<Fact>]
let ``simplify идемпотентен на наборе выражений`` () =
    for s in idempotentSet do
        let once = parse s |> simplify
        let twice = simplify once
        Assert.True(structEqual once twice, $"{s}: {prettyPrint once} ≠ {prettyPrint twice}")

[<Fact>]
let ``simplify идемпотентен на результатах diff и integrate`` () =
    for s in [ "(sin (* x x))"; "(/ 1 (+ x 1))"; "(* x (exp x))"; "(^ x (+ x 1))"; "(tan x)"; "(sqrt (+ 1 (^ x 2)))" ] do
        let d = Differentiate.diff "x" (parse s)
        Assert.True(structEqual d (simplify d), $"diff {s}: {prettyPrint d}")
    for s in [ "(+ (^ x 2) (* 3 x) 5)"; "(sin (* 2 x))"; "(log x)"; "(/ 1 (+ (* 2 x) 1))" ] do
        let i = IntegrateTests.integrate "x" (parse s)
        Assert.True(structEqual i (simplify i), $"integrate {s}: {prettyPrint i}")

// --- diff / integrate / expand / factor ---

[<Fact>]
let ``diff возвращает упрощённый результат`` () =
    eq "(* 2 x)" (prettyPrint (Differentiate.diff "x" (parse "(* x x)")))
    eq "(* -1 (^ x -2))" (prettyPrint (Differentiate.diff "x" (parse "(/ 1 x)")))
    eq "(^ (cos x) -2)" (prettyPrint (Differentiate.diff "x" (parse "(tan x)")))
    eq "(* a (^ x (+ -1 a)))" (prettyPrint (Differentiate.diff "x" (parse "(^ x a)")))

[<Fact>]
let ``diff многочлена: 3x^2 + 2x + 1 → 2 + 6x`` () =
    eq "(+ 2 (* 6 x))" (prettyPrint (Differentiate.diff "x" (parse "(+ (* 3 (^ x 2)) (* 2 x) 1)")))

[<Fact>]
let ``integrate: канонические формы входа (деление, вычитание, унарный минус)`` () =
    eq "(log x)" (prettyPrint (IntegrateTests.integrate "x" (parse "(/ 1 x)")))
    eq "(* 1/2 (log (+ 1 (* 2 x))))" (prettyPrint (IntegrateTests.integrate "x" (parse "(/ 1 (+ (* 2 x) 1))")))
    eq "(+ (* 3/2 (^ x 2)) (* -2 (log x)))" (prettyPrint (IntegrateTests.integrate "x" (parse "(- (* 3 x) (/ 2 x))")))
    eq "(* -1 (cos x))" (prettyPrint (IntegrateTests.integrate "x" (parse "(sin x)")))
    eq "(* a x)" (prettyPrint (IntegrateTests.integrate "x" (parse "a")))
    eq "(* 1/2 (^ x 2))" (prettyPrint (IntegrateTests.integrate "x" (parse "x")))

[<Fact>]
let ``expand и factor работают на канонической форме`` () =
    eq "(+ -1 (^ x 2))" (prettyPrint (expand (parse "(* (+ x 1) (- x 1))")))
    eq "(+ 1 (* 2 x) (^ x 2))" (prettyPrint (expand (parse "(^ (+ x 1) 2)")))
    eq "(+ (* 2 x) (* 2 y))" (prettyPrint (expand (parse "(* 2 (+ x y))")))
    eq "(* 2 (+ x y))" (prettyPrint (factor (parse "(+ (* 2 x) (* 2 y))")))
    eq "(* x (+ 1 x))" (prettyPrint (factor (parse "(+ x (^ x 2))")))
    eq "(* 3 x (+ 3 (* 2 x)))" (prettyPrint (factor (parse "(+ (* 6 (^ x 2)) (* 9 x))")))

// --- Печать канонической формы ---

let private mp (s: string) : string = MathPrinter.mathPrint (parse s)

[<Fact>]
let ``MathPrinter: вычитание, минус, деление`` () =
    eq "x - y" (mp "(+ x (* -1 y))")
    eq "-x" (mp "(* -1 x)")
    eq "x/y" (mp "(* x (^ y -1))")
    eq "1/x" (mp "(^ x -1)")
    eq "1/x^2" (mp "(^ x -2)")
    eq "x - 2y" (mp "(+ x (* -2 y))")
    eq "2x/y" (mp "(* 2 x (^ y -1))")
    eq "x/(1 + y)" (mp "(* x (^ (+ 1 y) -1))")
    eq "1/(y*z)" (mp "(* (^ y -1) (^ z -1))")
    eq "-x/y" (mp "(* -1 x (^ y -1))")

[<Fact>]
let ``MathPrinter: рациональный коэффициент`` () =
    eq "1/2*x" (mp "(* 1/2 x)")
    eq "x/(2y)" (mp "(* 1/2 x (^ y -1))")
    eq "1 - 1/2*x" (mp "(+ 1 (* -1/2 x))")

[<Fact>]
let ``math (parse+simplify) даёт каноническую форму`` () =
    eq "(+ (* 5/3 x) (* -1 y))" (prettyPrint (evalStr "(math \"x - y + 2x/3\")"))
    eq "(+ x (* -1 y))" (prettyPrint (evalStr "(math \"x - y\")"))
    eq "(^ x 2)" (prettyPrint (evalStr "(math \"x*x\")"))
    eq "x - y" (MathPrinter.mathPrint (evalStr "(math \"y*0 + x - y\")"))

// --- expand степени суммы: повторное умножение с собиранием подобных ---

let private expandStr (s: string) = prettyPrint (expand (parse s))

[<Fact>]
let ``expand степени суммы: эталоны малых n`` () =
    eq "(+ 1 (* 6 x) (* 15 (^ x 2)) (* 20 (^ x 3)) (* 15 (^ x 4)) (* 6 (^ x 5)) (^ x 6))" (expandStr "(^ (+ x 1) 6)")
    eq "(+ (^ x 4) (^ y 4) (^ z 4) (* 12 x y (^ z 2)) (* 12 x (^ y 2) z) (* 4 x (^ y 3)) (* 4 x (^ z 3)) (* 12 (^ x 2) y z) (* 6 (^ x 2) (^ y 2)) (* 6 (^ x 2) (^ z 2)) (* 4 (^ x 3) y) (* 4 (^ x 3) z) (* 4 y (^ z 3)) (* 6 (^ y 2) (^ z 2)) (* 4 (^ y 3) z))" (expandStr "(^ (+ x y z) 4)")
    eq "(+ (^ a 5) (* 32 (^ b 5)) (* 80 a (^ b 4)) (* 80 (^ a 2) (^ b 3)) (* 40 (^ a 3) (^ b 2)) (* 10 (^ a 4) b))" (expandStr "(^ (+ a (* 2 b)) 5)")
    eq "(+ 1 (* 3 (^ x 2)) (* 3 (^ x 4)) (^ x 6) (* 6 (^ x 2) (sin x)) (* 3 (^ x 2) (^ (sin x) 2)) (* 3 (^ x 4) (sin x)) (* 3 (sin x)) (* 3 (^ (sin x) 2)) (^ (sin x) 3))" (expandStr "(^ (+ (^ x 2) (sin x) 1) 3)")
    // нецелые и отрицательные степени не раскрываются
    eq "(^ (+ 1 x) 1/2)" (expandStr "(^ (+ x 1) 1/2)")
    eq "(^ (+ 1 x) -2)" (expandStr "(^ (+ x 1) -2)")

[<Fact>]
let ``expand (x+1)^40 быстро и с биномиальными коэффициентами`` () =
    let sw = System.Diagnostics.Stopwatch.StartNew()
    let r = expand (parse "(^ (+ x 1) 40)")
    sw.Stop()
    Assert.True(sw.Elapsed.TotalSeconds < 10.0, sprintf "слишком долго: %A" sw.Elapsed)
    match r with
    | LispList (LispSym "+" :: terms) ->
        Assert.Equal(41, terms.Length)
        let coef20 =
            terms |> List.pick (function
                | LispList [LispSym "*"; LispInteger c; LispList [LispSym "^"; LispSym "x"; LispInteger k]] when k = 20I -> Some c
                | _ -> None)
        // C(40,20)
        Assert.Equal(137846528820I, coef20)
    | _ -> failwith "ожидалась сумма"

[<Fact>]
let ``expand (x+y+z)^12 быстро, 91 моном, сумма коэффициентов 3^12`` () =
    let sw = System.Diagnostics.Stopwatch.StartNew()
    let r = expand (parse "(^ (+ x y z) 12)")
    sw.Stop()
    Assert.True(sw.Elapsed.TotalSeconds < 10.0, sprintf "слишком долго: %A" sw.Elapsed)
    match r with
    | LispList (LispSym "+" :: terms) ->
        Assert.Equal(91, terms.Length)
        let coef t =
            match t with
            | LispList (LispSym "*" :: LispInteger c :: _) -> c
            | _ -> 1I
        Assert.Equal(531441I, terms |> List.sumBy coef)
    | _ -> failwith "ожидалась сумма"
