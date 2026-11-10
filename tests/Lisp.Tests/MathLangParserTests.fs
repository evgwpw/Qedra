// Шаг 21, коммит 1: тесты парсера программ входного языка (MathReader.mathParseProgram)
// и печати конструкций языка (MathPrinter.mathPrintLang), включая round-trip
module MathLangParserTests

open Xunit
open Types
open Reader
open Evaluator
open Printer
open MathPrinter
open MathReader

// Программа → s-выражения операторов через « | »
let private prog (src: string) : string =
    mathParseProgram src |> List.map prettyPrint |> String.concat " | "

let private progIs (src: string) (expected: string) : unit =
    Assert.Equal(expected, prog src)

// Печать формы (Lisp-запись) в синтаксисе языка
let private show (code: string) : string = mathPrintLang (readAll code |> List.head)

let private showIs (code: string) (expected: string) : unit = Assert.Equal(expected, show code)

// Сообщение об ошибке разбора
let private errOf (src: string) : string =
    let ex = Assert.ThrowsAny<System.Exception>(fun () -> mathParseProgram src |> ignore)
    ex.Message

// --- Операторы ---

[<Fact>]
let ``MathLang: присваивание`` () =
    progIs "a := 5" "(:= a 5)"
    progIs "a := x + 1" "(:= a (+ x 1))"

[<Fact>]
let ``MathLang: определение функции`` () =
    progIs "f(x) := x^2 + sin(x)" "(:= (f x) (+ (^ x 2) (sin x)))"
    progIs "g(x, y) := x*y" "(:= (g x y) (* x y))"
    progIs "h() := 1" "(:= (h) 1)"

[<Fact>]
let ``MathLang: вызов — не определение; f(x) = 3 — уравнение`` () =
    progIs "f(x)" "(f x)"
    progIs "f(x) = 3" "(= (f x) 3)"
    Assert.Contains("слева от", errOf "f(2) := 1 + 1")

[<Fact>]
let ``MathLang: декларация домена :∈ и :in`` () =
    progIs "x :∈ ℝ" "(:declare x reals)"
    progIs "x :in integers" "(:declare x integers)"
    progIs "n :∈ ℕ" "(:declare n naturals)"

[<Fact>]
let ``MathLang: x :∈ без домена — снять декларации`` () =
    progIs "x :∈" "(:declare x)"
    progIs "x :in" "(:declare x)"
    progIs "x :∈; y :∈ ℝ" "(:declare x) | (:declare y reals)"

[<Fact>]
let ``MathLang: a := без правой части — снять присваивание`` () =
    progIs "a :=" "(:= a)"
    progIs "a :=; b := 1" "(:= a) | (:= b 1)"

[<Fact>]
let ``MathLang: ошибка — слева от := не имя`` () =
    Assert.Contains("слева от", errOf "1 + 2 := 3")

// --- Шаг 21a: присваивание в аргументах, элементу, параметры по умолчанию ---

[<Fact>]
let ``MathLang 21a: присваивание внутри аргументов вызова`` () =
    progIs "prog(a := 1, b := a + 1, b)" "(prog (:= a 1) (:= b (+ a 1)) b)"
    progIs "loop(if(k > 3, exit), k := k + 1)" "(loop (if (> k 3) exit) (:= k (+ k 1)))"
    progIs "a := b := 1" "(:= a (:= b 1))"

[<Fact>]
let ``MathLang 21a: присваивание элементу`` () =
    progIs "v[2] := 5" "(:= (m-index v 2) 5)"
    progIs "m[i, j] := 0" "(:= (m-index m i j) 0)"
    progIs "prog(v[1] := 2)" "(prog (:= (m-index v 1) 2))"
    Assert.Contains("слева от", errOf "f(x)[1] := 2")

[<Fact>]
let ``MathLang 21a: параметры по умолчанию в определении функции`` () =
    progIs "f(n, s := 0, k := 1) := n" "(:= (f n (:= s 0) (:= k 1)) n)"
    progIs "g(a, b := a*2) := a + b" "(:= (g a (:= b (* a 2))) (+ a b))"
    progIs "g(a, b := f(1, 2)) := a" "(:= (g a (:= b (f 1 2))) a)"
    // вызов, а не определение: первый «:=» стоит внутри аргументов
    progIs "f(a := 1)" "(f (:= a 1))"

[<Fact>]
let ``MathLang 21a: печать присваиваний элементу и параметров по умолчанию`` () =
    showIs "(:= (m-index v 2) 5)" "v[2] := 5"
    showIs "(:= (f n (:= s 0)) n)" "f(n, s := 0) := n"
    showIs "(prog (:= a 1) a)" "prog(a := 1, a)"

// --- Отношения и логика ---

[<Fact>]
let ``MathLang: отношения ASCII и юникод`` () =
    progIs "a = b" "(= a b)"
    progIs "a /= b" "(/= a b)"
    progIs "a ≠ b" "(/= a b)"
    progIs "a != b" "(/= a b)"
    progIs "a < b" "(< a b)"
    progIs "a > b" "(> a b)"
    progIs "a <= b" "(<= a b)"
    progIs "a ≤ b" "(<= a b)"
    progIs "a >= b" "(>= a b)"
    progIs "a ≥ b" "(>= a b)"

[<Fact>]
let ``MathLang: приоритет — отношения ниже +, логика ниже отношений`` () =
    progIs "a + 1 < b * 2" "(< (+ a 1) (* b 2))"
    progIs "a < b and c = d or not e" "(or (and (< a b) (= c d)) (not e))"
    progIs "not a = b" "(not (= a b))"
    progIs "a and b and c" "(and a b c)"

[<Fact>]
let ``MathLang: принадлежность ∈, in, ∉`` () =
    progIs "x ∈ ℝ" "(:in x reals)"
    progIs "x in reals" "(:in x reals)"
    progIs "x ∉ ℤ" "(not (:in x integers))"
    progIs "x ∈ {1, 2} ∪ {3}" "(:in x (union (m-set 1 2) (m-set 3)))"

// --- Векторы, матрицы, индексы ---

[<Fact>]
let ``MathLang: векторы и матрицы`` () =
    progIs "[1, 2, 3]" "(m-vector 1 2 3)"
    progIs "[[1, 2], [3, 4]]" "(m-vector (m-vector 1 2) (m-vector 3 4))"
    progIs "[x, x^2]" "(m-vector x (^ x 2))"
    progIs "[]" "(m-vector)"

[<Fact>]
let ``MathLang: индексация v[i], m[i, j], v[1][2]`` () =
    progIs "v[2]" "(m-index v 2)"
    progIs "m[i, j]" "(m-index m i j)"
    progIs "m[1][2]" "(m-index (m-index m 1) 2)"
    progIs "v[i + 1] * 2" "(* (m-index v (+ i 1)) 2)"
    progIs "f(x)[1]" "(m-index (f x) 1)"

// --- Множества ---

[<Fact>]
let ``MathLang: множества и операции`` () =
    progIs "{1, 2, 3}" "(m-set 1 2 3)"
    progIs "{}" "(m-set)"
    progIs "∅" "(m-set)"
    progIs "A ∪ B" "(union A B)"
    progIs "A ∩ B" "(intersection A B)"
    progIs "A \\ B" "(set-difference A B)"

[<Fact>]
let ``MathLang: приоритет ∩ выше ∪, + выше ∩`` () =
    progIs "A ∪ B ∩ C" "(union A (intersection B C))"
    progIs "A ∪ B ∪ C" "(union (union A B) C)"
    progIs "A ∪ B = C" "(= (union A B) C)"

// --- Константы и литералы ---

[<Fact>]
let ``MathLang: константы π ∞ ⅈ e и i`` () =
    progIs "π" "pi"
    progIs "pi*2" "(* pi 2)"
    progIs "∞" "inf"
    progIs "-∞" "(- 0 inf)"
    progIs "ⅈ" "%i"
    progIs "%i" "%i"
    progIs "e" "e"
    progIs "i" "i"

[<Fact>]
let ``MathLang: домены ℕ ℤ ℚ ℝ ℂ`` () =
    progIs "ℕ" "naturals"
    progIs "ℤ" "integers"
    progIs "ℚ" "rationals"
    progIs "ℝ" "reals"
    progIs "ℂ" "complexes"

[<Fact>]
let ``MathLang: true false unknown и строки`` () =
    progIs "true" "#t"
    progIs "false" "#f"
    progIs "unknown" "unknown"
    progIs "\"привет\"" "\"привет\""
    progIs "f(\"a b\", 1)" "(f \"a b\" 1)"

[<Fact>]
let ``MathLang: факториал`` () =
    progIs "n!" "(factorial n)"
    progIs "(n + 1)!" "(factorial (+ n 1))"
    progIs "5!" "(factorial 5)"
    progIs "n*(n - 1)!" "(* n (factorial (- n 1)))"
    progIs "-n!" "(- 0 (factorial n))"
    progIs "2^n!" "(^ 2 (factorial n))"

[<Fact>]
let ``MathLang: имя с вопросительным знаком — вызов in?(x, S)`` () =
    progIs "subset?(A, B)" "(subset? A B)"

[<Fact>]
let ``MathLang: вызов без аргументов и вложенные вызовы`` () =
    progIs "clear()" "(clear)"
    progIs "if(n = 0, 1, n*fact(n - 1))" "(if (= n 0) 1 (* n (fact (- n 1))))"

// --- Разделители и комментарии ---

[<Fact>]
let ``MathLang: операторы через ; и перевод строки`` () =
    progIs "a := 1; b := 2" "(:= a 1) | (:= b 2)"
    progIs "a := 1\nb := 2\n\n  \nc" "(:= a 1) | (:= b 2) | c"
    progIs "a := 1;\n" "(:= a 1)"
    progIs "" ""
    progIs "  \n ; ;\n" ""

[<Fact>]
let ``MathLang: комментарии // до конца строки`` () =
    progIs "a := 1 // присваивание\nb := 2" "(:= a 1) | (:= b 2)"
    progIs "// только комментарий" ""

[<Fact>]
let ``MathLang: перевод строки в незакрытых скобках — продолжение`` () =
    progIs "f(1,\n  2)" "(f 1 2)"
    progIs "[1, 2,\n 3, 4]" "(m-vector 1 2 3 4)"
    progIs "{1,\n2}" "(m-set 1 2)"
    progIs "(1 +\n 2) * 3" "(* (+ 1 2) 3)"

[<Fact>]
let ``MathLang: висячий оператор в конце строки — продолжение`` () =
    progIs "a := 1 +\n 2" "(:= a (+ 1 2))"

// --- Ошибки: номер строки и позиция ---

[<Fact>]
let ``MathLang: ошибка с номером строки и позицией — недопустимый символ`` () =
    let m = errOf "x := 1\ny := 2 $ 3"
    Assert.Contains("строка 2, позиция 8", m)
    Assert.Contains("$", m)

[<Fact>]
let ``MathLang: ошибка с номером строки и позицией — неожиданный токен`` () =
    let m = errOf "a := 1\nb := )"
    Assert.Contains("строка 2, позиция 6", m)

[<Fact>]
let ``MathLang: ошибка — незакрытая скобка и лишний токен`` () =
    Assert.Contains("строка 1", errOf "f(1, 2")
    Assert.Contains("ожидался конец оператора", errOf "1 2 )")
    Assert.Contains("строка", errOf "\"abc")

// --- mathParse не изменился ---

[<Fact>]
let ``MathLang: mathParse принимает выражение языка, но не оператор`` () =
    Assert.Equal("(m-vector 1 2)", prettyPrint (mathParse "[1, 2]"))
    Assert.Equal("(< a b)", prettyPrint (mathParse "a < b"))
    Assert.Equal("(* 2 x)", prettyPrint (mathParse "2x"))
    Assert.Equal("(+ (* 2 x) 1)", prettyPrint (mathParse "2x\n + 1"))   // перевод строки — пробел, как раньше
    Assert.ThrowsAny<System.Exception>(fun () -> mathParse "x := 3" |> ignore) |> ignore
    Assert.ThrowsAny<System.Exception>(fun () -> mathParse "1; 2" |> ignore) |> ignore

// --- Печать ---

[<Fact>]
let ``MathLang печать: векторы, матрицы, индексы, множества`` () =
    showIs "(m-vector 1 2 3)" "[1, 2, 3]"
    showIs "(m-vector (m-vector 1 2) (m-vector 3 4))" "[[1, 2], [3, 4]]"
    showIs "(m-index v 2)" "v[2]"
    showIs "(m-index m i j)" "m[i, j]"
    showIs "(m-set 1 2)" "{1, 2}"
    showIs "(m-set)" "{}"

[<Fact>]
let ``MathLang печать: булевы, unknown, бесконечность`` () =
    showIs "#t" "true"
    showIs "#f" "false"
    showIs "unknown" "unknown"
    showIs "inf" "∞"
    showIs "-inf" "-∞"
    showIs "(* -1 inf)" "-∞"
    showIs "(+ 1 inf)" "1 + ∞"

[<Fact>]
let ``MathLang печать: уравнения и отношения`` () =
    showIs "(= (^ x 2) 2)" "x^2 = 2"
    showIs "(/= a b)" "a ≠ b"
    showIs "(<= a 1)" "a ≤ 1"
    showIs "(>= a 1)" "a ≥ 1"
    showIs "(:in x reals)" "x ∈ reals"
    showIs "(solve (= (^ x 2) 2) x)" "solve(x^2 = 2, x)"

[<Fact>]
let ``MathLang печать: невычисленные integrate, limit, if и неизвестные функции`` () =
    showIs "(integrate (foo x) x)" "integrate(foo(x), x)"
    showIs "(limit (/ (sin x) x) x 0)" "limit(sin(x)/x, x, 0)"
    showIs "(if (> x 0) x (- 0 x))" "if(x > 0, x, -x)"
    showIs "(f x (+ y 1))" "f(x, y + 1)"
    showIs "(f)" "f()"

[<Fact>]
let ``MathLang печать: логика, скобки по приоритетам`` () =
    showIs "(and (< a b) (or (= c d) e))" "a < b and (c = d or e)"
    showIs "(or (and a b) c)" "a and b or c"
    showIs "(not (= a b))" "not a = b"
    showIs "(not (and a b))" "not (a and b)"
    showIs "(+ (= a b) 1)" "(a = b) + 1"

[<Fact>]
let ``MathLang печать: присваивания, определения, декларации`` () =
    showIs "(:= a 5)" "a := 5"
    showIs "(:= a)" "a :="
    showIs "(:= (f x y) (+ (^ x 2) y))" "f(x, y) := x^2 + y"
    showIs "(:declare x reals)" "x :∈ reals"
    showIs "(:declare x)" "x :∈"

[<Fact>]
let ``MathLang печать: операции над множествами и факториал`` () =
    showIs "(union a b)" "a ∪ b"
    showIs "(intersection a b)" "a ∩ b"
    showIs "(set-difference a b)" "a \\ b"
    showIs "(union a (intersection b c))" "a ∪ b ∩ c"
    showIs "(intersection (union a b) c)" "(a ∪ b) ∩ c"
    showIs "(factorial n)" "n!"
    showIs "(factorial (+ n 1))" "(n + 1)!"
    showIs "(^ (factorial n) 2)" "(n!)^2"

// --- Round-trip: parse ∘ show ∘ parse = parse ---

let private roundTripSources = [
    "f(x) := x^2 + sin(x)"
    "g(x, y) := if(x > y, x, y)"
    "a := 5"
    "a :="
    "x :∈ ℝ"
    "v := [1, 2, 3]"
    "m := [[1, 2], [3, 4]]"
    "v[2] + m[1, 2]"
    "s := {1, 2, 3} ∪ {3, 4}"
    "A ∩ B ∪ C \\ D"
    "(A ∪ B) ∩ C"
    "x ∈ ℝ and y ≠ 0"
    "not (a < b) or c >= 2"
    "fact(n) := if(n = 0, 1, n*fact(n - 1))"
    "integrate(x^2 + 1, x, 0, 1)"
    "limit(sin(x)/x, x, 0)"
    "solve(x^2 = 2, x)"
    "taylor(exp(x), x, 0, 4)"
    "limit(1/x, x, ∞)"
    "-∞ + 1"
    "true and false"
    "\"строка\""
    "(n + 1)! / n!"
    "2^n! + 1"
    "x_1 + x_2*3"
    "f(a, [1, 2], {3})"
    "1/3*x^3 - cos(x)"
    "(a = b) = c"
    // Шаг 21a: программирование
    "f(n, s := 0, k := 1) := prog(loop(if(k > n, exit), s := s + k, k := k + 1), s)"
    "v[2] := 5"
    "m[i, j] := m[i, j] + 1"
    "prog(a := 1, b := a + 1, return(b))"
    "loop(if(k > 10, exit(s)), s := s + k)"
    "if(c, a, b, u)"
    "vector(k^2, k, 1, 10)"
    "sum(x^k, k, 0, n)"
    "rootsum(t*log(x + t), t, t^3 + t + 1)"
    "a := b := 1"
]

[<Fact>]
let ``MathLang: round-trip печати (parse ∘ show ∘ parse)`` () =
    for src in roundTripSources do
        let ast = mathParseProgram src
        let text = ast |> List.map mathPrintLang |> String.concat "\n"
        let back = mathParseProgram text
        let backText = back |> List.map prettyPrint |> String.concat " | "
        Assert.True(
            List.length ast = List.length back && List.forall2 Numeric.structEqual ast back,
            $"Round-trip нарушен: {src} → «{text}» → {backText}")

// --- Старое поведение печати не изменилось ---

[<Fact>]
let ``MathLang: обычный mathPrint не использует режим языка`` () =
    Assert.Equal("#t", mathPrint (LispBool true))
    Assert.Equal("(foo x y)", mathPrint (readAll "(foo x y)" |> List.head))
    Assert.Equal("inf", mathPrint (LispSym "inf"))
    // а режим языка не «залипает» после вызова
    ignore (mathPrintLang (LispBool true))
    Assert.Equal("#t", mathPrint (LispBool true))

// --- Объекты с хуками печати: ряды, множества, тензоры ---

[<Fact>]
let ``MathLang печать: хуки объектов (ряд, множество, вектор) сохранены`` () =
    let ev (code: string) = eval (readAll code |> List.head) globalEnv
    let s = mathPrintLang (ev "(series '(exp x) 'x 0 3)")
    Assert.Contains("O(x^3)", s)
    Assert.Equal("{1, 2}", mathPrintLang (ev "(set 2 1)"))
    Assert.Equal("[1, 2]", mathPrintLang (ev "(tensor '(1 2))"))
    // внутри вызова функции объекты — атомы
    Assert.Equal("f({1, 2}, [3, 4])", mathPrintLang (LispList [LispSym "f"; ev "(set 2 1)"; ev "(tensor '(3 4))"]))

// --- Шаг 21d: интервалы ---

[<Fact>]
let ``MathLang: литералы интервалов [a, b), (a, b], (a, b)`` () =
    progIs "[0, 1)" "(:interval 0 1 closed open)"
    progIs "(0, 1]" "(:interval 0 1 open closed)"
    progIs "(0, 1)" "(:interval 0 1 open open)"
    progIs "(0, ∞)" "(:interval 0 inf open open)"
    progIs "(-∞, 5]" "(:interval (- 0 inf) 5 open closed)"
    progIs "x :∈ (0, ∞)" "(:declare x (:interval 0 inf open open))"

[<Fact>]
let ``MathLang: [a, b] остаётся вектором, (a + b) — группировка`` () =
    progIs "[0, 1]" "(m-vector 0 1)"
    progIs "[1, 2, 3]" "(m-vector 1 2 3)"
    progIs "(1 + 2)*3" "(* (+ 1 2) 3)"
    progIs "2(3 + 4)" "(* 2 (+ 3 4))"

[<Fact>]
let ``MathLang: ошибки интервалов`` () =
    Assert.Contains("двумя границами", errOf "[1, 2, 3)")
    Assert.Contains("ожидалось «)» или «]»", errOf "(1, 2, 3)")
    Assert.Contains("ожидалось «]»", errOf "[1, 2")
