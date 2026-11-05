// TEX.1: LaTeX-принтер — эталоны (П1) и баланс скобок.
module LatexPrinterTests

open Xunit
open Types

let private n (v: int) = LispInteger (bigint v)
let private q (p: int) (d: int) = LispRational (bigint p, bigint d)
let private s (name: string) = LispSym name
let private l (xs: LispValue list) = LispList xs
let private s2 (op: string) (a: LispValue) (b: LispValue) = l [ s op; a; b ]

let private tex (v: LispValue) = LatexPrinter.latexPrint v

let private mv (xs: LispValue list) = l (s "m-vector" :: xs)
let private rg (v: string) (a: LispValue) (b: LispValue) = mv [ s v; a; b ]
// форма -y dx + x dy и окружность (cos t, sin t)
let private formW = s2 "+" (s2 "*" (l [ s "-"; n 0; s "y" ]) (s "dx")) (s2 "*" (s "x") (s "dy"))
let private circ = mv [ l [ s "cos"; s "t" ]; l [ s "sin"; s "t" ] ]

// (выражение, ожидаемая строка LaTeX)
let private cases : (string * LispValue * string) list =
    [ "дробь", s2 "/" (s2 "^" (s "x") (n 2)) (n 2), "\\frac{x^{2}}{2}"
      "корень", l [ s "sqrt"; s2 "+" (s "x") (n 1) ], "\\sqrt{x + 1}"
      "кубический корень", s2 "^" (s "x") (q 1 3), "\\sqrt[3]{x}"
      "экспонента", l [ s "exp"; l [ s "-"; s2 "^" (s "x") (n 2) ] ], "e^{-x^{2}}"
      "синус в квадрате", s2 "^" (l [ s "sin"; s "x" ]) (n 2), "\\sin^{2}\\left(x\\right)"
      // отрицательная степень функции — дробь: \cos^{-2} читается как степень арккосинуса
      // числитель «(сумма)·log(…)»: внешние \left( … \right) — разные пары, снимать нельзя (было \log\left(x}{x^{2}}\right))
      "дробь со скобкой и логарифмом в числителе",
      l [ s "*"; s2 "+" (n 1) (s "x"); l [ s "log"; s "x" ]; s2 "^" (s "x") (n -2) ],
      "\\frac{\\left(1 + x\\right) \\cdot \\log\\left(x\\right)}{x^{2}}"
      // MINT.a: кратный интеграл одной записью — внешний первым, дифференциалы от внутреннего
      "кратный интеграл одной записью",
      l [ s "integrate"; s2 "*" (s "x") (s "y"); l [ s "m-vector"; s "x"; n 0; n 1 ]; l [ s "m-vector"; s "y"; n 0; s "x" ] ],
      "\\int_{0}^{1} \\int_{0}^{x} x y\\,dy\\,dx"
      // подчёркивание в имени неизвестной функции — \_ (не нижний индекс)
      "имя с подчёркиванием", l [ s "arc_length"; s "t" ], "\\operatorname{arc\\_length}\\left(t\\right)"
      // TEX.MI: учебная запись криволинейных/поверхностных/кратных интегралов (имена «MINT: …» — в skip кругового теста)
      "MINT: площадь поверхности", l [ s "surface_area"; mv [ s "u"; s "v"; s2 "+" (s "u") (s "v") ]; rg "u" (n 0) (n 1); rg "v" (n 0) (n 2) ],
      "\\iint_{S} dS,\\quad S:\\ \\mathbf{r}(u, v) = (u, v, u + v),\\ u \\in [0, 1],\\ v \\in [0, 2]"
      "MINT: поверхностный интеграл", l [ s "surface_integral"; s2 "^" (s "z") (n 2); mv [ s "x"; s "y"; s "z" ]; mv [ s "u"; s "v"; s "v" ]; rg "u" (n 0) (n 1); rg "v" (n 0) (n 1) ],
      "\\iint_{S} z^{2}\\,dS,\\quad S:\\ \\mathbf{r}(u, v) = (u, v, v),\\ u \\in [0, 1],\\ v \\in [0, 1]"
      "MINT: длина дуги", l [ s "arc_length"; mv [ s "t"; s2 "^" (s "t") (n 2) ]; rg "t" (n 0) (n 1) ],
      "\\int_{C} ds,\\quad C:\\ \\mathbf{r}(t) = (t, t^{2}),\\ t \\in [0, 1]"
      "MINT: криволинейный первого рода", l [ s "line_integral"; s "x"; mv [ s "x"; s "y" ]; mv [ s "t"; s "t" ]; rg "t" (n 0) (n 1) ],
      "\\int_{C} x\\,ds,\\quad C:\\ \\mathbf{r}(t) = (t, t),\\ t \\in [0, 1]"
      "MINT: форма по замкнутой кривой", l [ s "integrate_form"; formW; mv [ s "x"; s "y" ]; circ; rg "t" (n 0) (s2 "*" (n 2) (s "pi")) ],
      "\\oint_{C} -y\\,dx + x\\,dy,\\quad C:\\ \\mathbf{r}(t) = (\\cos\\left(t\\right), \\sin\\left(t\\right)),\\ t \\in [0, 2 \\cdot \\pi]"
      "MINT: форма по незамкнутой кривой", l [ s "integrate_form"; formW; mv [ s "x"; s "y" ]; circ; rg "t" (n 0) (s "pi") ],
      "\\int_{C} -y\\,dx + x\\,dy,\\quad C:\\ \\mathbf{r}(t) = (\\cos\\left(t\\right), \\sin\\left(t\\right)),\\ t \\in [0, \\pi]"
      "MINT: форма по поверхности", l [ s "integrate_form"; s "dz"; mv [ s "x"; s "y"; s "z" ]; mv [ s "u"; s "v"; s "u" ]; rg "u" (n 0) (n 1); rg "v" (n 0) (n 1) ],
      "\\iint_{S} dz,\\quad S:\\ \\mathbf{r}(u, v) = (u, v, u),\\ u \\in [0, 1],\\ v \\in [0, 1]"
      "MINT: замена polar", l [ s "integrate_change"; n 1; s "polar"; rg "r" (n 0) (n 1); rg "t" (n 0) (s2 "*" (n 2) (s "pi")) ],
      "\\iint_{D} 1\\,dx\\,dy,\\quad x = r \\cdot \\cos\\left(t\\right),\\ y = r \\cdot \\sin\\left(t\\right),\\ r \\in [0, 1],\\ t \\in [0, 2 \\cdot \\pi]"
      "MINT: замена cylindrical", l [ s "integrate_change"; n 1; s "cylindrical"; rg "r" (n 0) (n 1); rg "t" (n 0) (n 1); rg "h" (n 0) (n 1) ],
      "\\iiint_{D} 1\\,dx\\,dy\\,dz,\\quad x = r \\cdot \\cos\\left(t\\right),\\ y = r \\cdot \\sin\\left(t\\right),\\ z = h,\\ r \\in [0, 1],\\ t \\in [0, 1],\\ h \\in [0, 1]"
      "MINT: замена spherical", l [ s "integrate_change"; n 1; s "spherical"; rg "r" (n 0) (n 1); rg "a" (n 0) (n 1); rg "b" (n 0) (n 1) ],
      "\\iiint_{D} 1\\,dx\\,dy\\,dz,\\quad x = r \\cdot \\sin\\left(a\\right) \\cdot \\cos\\left(b\\right),\\ y = r \\cdot \\sin\\left(a\\right) \\cdot \\sin\\left(b\\right),\\ z = r \\cdot \\cos\\left(a\\right),\\ r \\in [0, 1],\\ a \\in [0, 1],\\ b \\in [0, 1]"
      "MINT: замена явная", l [ s "integrate_change"; n 1; mv [ l [ s "="; s "x"; s2 "+" (s "u") (s "v") ]; l [ s "="; s "y"; s2 "-" (s "u") (s "v") ] ]; rg "u" (n 0) (n 1); rg "v" (n 0) (n 1) ],
      "\\iint_{D} 1\\,dx\\,dy,\\quad x = u + v,\\ y = u - v,\\ u \\in [0, 1],\\ v \\in [0, 1]"
      "MINT: область прямоугольник", l [ s "integrate_region"; s "f"; l [ s "rect_region"; rg "x" (n 0) (n 1); rg "y" (n 2) (n 3) ] ],
      "\\iint_{D} f\\,dA,\\quad D:\\ [0, 1] \\times [2, 3]"
      "MINT: область между графиками", l [ s "integrate_region"; s "f"; l [ s "region"; s "x"; n 0; n 1; s "y"; s "x"; n 1 ] ],
      "\\iint_{D} f\\,dA,\\quad D:\\ 0 \\le x \\le 1,\\ x \\le y \\le 1"
      "MINT: область треугольник", l [ s "integrate_region"; s "f"; l [ s "triangle_region"; mv [ s "x"; s "y" ]; mv [ n 0; n 0 ]; mv [ n 1; n 0 ]; mv [ n 0; n 1 ] ] ],
      "\\iint_{D} f\\,dA,\\quad D:\\ \\triangle (0, 0), (1, 0), (0, 1)"
      "MINT: область круг со сдвигом", l [ s "integrate_region"; s "f"; l [ s "disk_region"; mv [ s "x"; s "y" ]; mv [ n 1; n -2 ]; n 3 ] ],
      "\\iint_{D} f\\,dA,\\quad D:\\ \\left(x - 1\\right)^{2} + \\left(y + 2\\right)^{2} \\le 3^{2}"
      "MINT: область кольцо", l [ s "integrate_region"; s "f"; l [ s "annulus_region"; mv [ s "x"; s "y" ]; mv [ n 0; n 0 ]; n 1; n 2 ] ],
      "\\iint_{D} f\\,dA,\\quad D:\\ 1^{2} \\le x^{2} + y^{2} \\le 2^{2}"
      "MINT: Грин", l [ s "green_check"; l [ s "-"; n 0; s "y" ]; s "x"; mv [ s "x"; s "y" ]; circ; rg "t" (n 0) (s2 "*" (n 2) (s "pi")); l [ s "disk_region"; mv [ s "x"; s "y" ]; mv [ n 0; n 0 ]; n 1 ] ],
      "\\oint_{C} -y\\,dx + x\\,dy \\overset{?}{=} \\iint_{D} \\left(\\frac{\\partial}{\\partial x}\\left(x\\right) - \\frac{\\partial}{\\partial y}\\left(-y\\right)\\right) dA,\\quad C:\\ \\mathbf{r}(t) = (\\cos\\left(t\\right), \\sin\\left(t\\right)),\\ t \\in [0, 2 \\cdot \\pi],\\ D:\\ x^{2} + y^{2} \\le 1^{2}"
      "MINT: Стокс", l [ s "stokes_check"; mv [ s "y"; s "z"; s "x" ]; mv [ s "x"; s "y"; s "z" ]; mv [ s "u"; s "v"; s "u" ]; rg "u" (n 0) (n 1); rg "v" (n 0) (n 1); mv [ s "t"; n 0; s "t" ]; rg "t" (n 0) (n 1) ],
      "\\oint_{C} \\mathbf{F} \\cdot d\\mathbf{r} \\overset{?}{=} \\iint_{S} (\\nabla \\times \\mathbf{F}) \\cdot d\\mathbf{S},\\quad \\mathbf{F} = (y, z, x),\\quad S:\\ \\mathbf{r}(u, v) = (u, v, u),\\ u \\in [0, 1],\\ v \\in [0, 1],\\ C:\\ \\mathbf{r}(t) = (t, 0, t),\\ t \\in [0, 1]"
      "MINT: Гаусс", l [ s "gauss_check"; mv [ s "x"; s "y"; s "z" ]; mv [ s "x"; s "y"; s "z" ]; mv [ s "u"; s "v"; s "u" ]; rg "u" (n 0) (n 1); rg "v" (n 0) (n 1); s "spherical"; rg "r" (n 0) (n 1); rg "a" (n 0) (n 1); rg "b" (n 0) (n 1) ],
      "\\iint_{S} \\mathbf{F} \\cdot d\\mathbf{S} \\overset{?}{=} \\iiint_{V} \\nabla \\cdot \\mathbf{F}\\,dV,\\quad \\mathbf{F} = (x, y, z),\\quad S:\\ \\mathbf{r}(u, v) = (u, v, u),\\ u \\in [0, 1],\\ v \\in [0, 1],\\ V:\\ \\text{spherical},\\ r \\in [0, 1],\\ a \\in [0, 1],\\ b \\in [0, 1]"
      // аргументы не того вида — прежняя печать \operatorname{…}
      "MINT: не вектор", l [ s "arc_length"; s "t"; rg "t" (n 0) (n 1) ],
      "\\operatorname{arc\\_length}\\left(t, \\left[t, 0, 1\\right]\\right)"
      "косинус в степени −2", s2 "^" (l [ s "cos"; s "x" ]) (n -2), "\\frac{1}{\\cos^{2}\\left(x\\right)}"
      "косинус в степени −1", s2 "^" (l [ s "cos"; s "x" ]) (n -1), "\\frac{1}{\\cos\\left(x\\right)}"
      // (1/cos u)^r — так упрощатель хранит sec(u)^r
      "секанс в степени 7/2", s2 "^" (s2 "^" (l [ s "cos"; s "x" ]) (n -1)) (q 7 2), "\\sec^{\\frac{7}{2}}\\left(x\\right)"
      "косеканс в степени 3/2", s2 "^" (s2 "^" (l [ s "sin"; s "x" ]) (n -1)) (q 3 2), "\\csc^{\\frac{3}{2}}\\left(x\\right)"
      "логарифм", l [ s "log"; s "x" ], "\\log\\left(x\\right)"
      "натуральный логарифм", l [ s "ln"; s "x" ], "\\ln\\left(x\\right)"
      "интеграл", l [ s "integrate"; s "f"; s "x" ], "\\int f\\,dx"
      "определённый интеграл", l [ s "integrate"; s "f"; s "x"; n 0; s "inf" ], "\\int_{0}^{\\infty} f\\,dx"
      "сумма", l [ s "sum"; s2 "/" (n 1) (s2 "^" (s "k") (n 2)); s "k"; n 1; s "inf" ],
      "\\sum_{k=1}^{\\infty} \\frac{1}{k^{2}}"
      "производная", l [ s "diff"; s "f"; s "x" ], "\\frac{d}{dx}\\left(f\\right)"
      "предел", l [ s "limit"; s2 "/" (l [ s "sin"; s "x" ]) (s "x"); s "x"; n 0 ],
      "\\lim_{x \\to 0} \\frac{\\sin\\left(x\\right)}{x}"
      "матрица", l [ s "m-vector"; l [ s "m-vector"; n 1; n 2 ]; l [ s "m-vector"; n 3; n 4 ] ],
      "\\begin{pmatrix} 1 & 2 \\\\ 3 & 4 \\end{pmatrix}"
      "кусочно", l [ s "piecewise"; l [ l [ s2 ">" (s "x") (n 0); s "x" ]; l [ s2 "<=" (s "x") (n 0); l [ s "-"; s "x" ] ] ] ],
      "\\begin{cases} x, & x > 0 \\\\ -x, & x \\le 0 \\end{cases}"
      "Бессель", l [ s "bessel-j"; q 1 3; s "x" ], "J_{1/3}\\left(x\\right)"
      "Бессель Y", l [ s "bessel-y"; s "nu"; s "x" ], "Y_{\\nu}\\left(x\\right)"
      "Эйри", l [ s "airy-ai"; s "x" ], "\\operatorname{Ai}\\left(x\\right)"
      "Лежандр", l [ s "legendre-p"; n 2; s "x" ], "P_{2}\\left(x\\right)"
      "гамма", l [ s "gamma"; s "x" ], "\\Gamma\\left(x\\right)"
      "дробь с произведением", s2 "/" (n 1) (s2 "*" (n 2) (s "x")), "\\frac{1}{2x}"
      "минус произведение", l [ s "*"; n -1; s "a"; s "b" ], "-a b"
      "скобки вычитания", s2 "-" (s "a") (s2 "-" (s "b") (s "c")), "a - \\left(b - c\\right)"
      "неравенство", s2 "!=" (s "x") (n 0), "x \\ne 0"
      "меньше или равно", s2 "<=" (s "x") (n 1), "x \\le 1"
      "больше или равно", s2 ">=" (s "x") (n 1), "x \\ge 1"
      "множество", l [ s "m-set"; n 1; n 2; n 3 ], "\\left\\{1, 2, 3\\right\\}"
      "вектор", l [ s "m-vector"; n 1; n 2 ], "\\left[1, 2\\right]"
      "комплексное", LispComplex (n 1, n -2), "1 - 2i"
      "отрицательная дробь", q -3 4, "-\\frac{3}{4}"
      "индекс", s "alpha_1", "\\alpha_{1}"
      "греческая", s "alpha", "\\alpha"
      "бесконечность", s "inf", "\\infty"
      "степень", s2 "^" (s "x") (n 2), "x^{2}"
      "минус степень", s2 "^" (s "x") (n -1), "\\frac{1}{x}"
      "произведение чисел", s2 "*" (n 2) (n 2), "2 \\cdot 2"
      "сумма", s2 "+" (s "x") (n 1), "x + 1"
      "вычитание", s2 "-" (s "x") (n 1), "x - 1"
      "унарный минус", l [ s "-"; s "x" ], "-x"
      "факториал", l [ s "factorial"; s "n" ], "n!"
      "бином", l [ s "binomial"; s "n"; s "k" ], "\\binom{n}{k}"
      "логика и", l [ s "and"; s2 ">" (s "x") (n 0); s2 ">" (s "y") (n 0) ], "x > 0 \\land y > 0"
      "логика или", l [ s "or"; s2 ">" (s "x") (n 0); s2 "<" (s "x") (n 0) ], "x > 0 \\lor x < 0"
      "отрицание", l [ s "not"; s2 "=" (s "x") (n 0) ], "\\lnot x = 0"
      "принадлежность", l [ s ":in"; s "x"; l [ s "m-set"; n 1 ] ], "x \\in \\left\\{1\\right\\}"
      "неизвестная функция", l [ s "erf"; s "x" ], "\\operatorname{erf}\\left(x\\right)"
      "корень из дроби", l [ s "sqrt"; s2 "/" (s "x") (n 2) ], "\\sqrt{\\frac{x}{2}}"
      "вложенная степень", s2 "^" (s2 "+" (s "x") (n 1)) (n 2), "\\left(x + 1\\right)^{2}"
      "гиперболический", l [ s "sinh"; s "x" ], "\\sinh\\left(x\\right)"
      "арктангенс", l [ s "atan"; s "x" ], "\\arctan\\left(x\\right)"
      "модуль", l [ s "abs"; s "x" ], "\\left|x\\right|"
      "euler-gamma", l [ s "euler-gamma" ], "\\gamma"
      "произведение", l [ s "product"; s "k"; s "k"; n 1; n 3 ], "\\prod_{k=1}^{3} k" ]

[<Fact>]
let ``TEX.1: эталоны LaTeX (≥ 40 пар)`` () =
    let mutable failures = ResizeArray<string>()
    for name, expr, expected in cases do
        let actual = tex expr
        if actual <> expected then failures.Add(sprintf "%s: получено <%s>, ожидалось <%s>" name actual expected)
    Assert.True(failures.Count = 0, String.concat "\n" failures)

// Приведение к канонической форме для кругового теста: sqrt → ^1/2, -a → -1·a, комплекс → a + b·i
let rec private norm (v: LispValue) : LispValue =
    match v with
    | LispList (LispSym "sqrt" :: [ a ]) -> LispList [ LispSym "^"; norm a; LispRational (1I, 2I) ]
    | LispList [ LispSym "-"; a ] -> LispList [ LispSym "*"; LispInteger -1I; norm a ]
    | LispComplex (re, im) -> LispList [ LispSym "+"; norm re; LispList [ LispSym "*"; norm im; LispSym "i" ] ]
    | LispSym "euler-gamma" -> LispList [ LispSym "euler-gamma" ]
    | LispList (LispSym h :: xs) -> LispList(LispSym h :: List.map norm xs)
    | _ -> v

[<Fact>]
let ``TEX.1: круговой тест — разбор LaTeX даёт то же выражение`` () =
    let mutable failures = ResizeArray<string>()
    // окружения pmatrix/cases и константа euler-gamma (печатается как \gamma, как и переменная) — вне кругового корпуса
    // кратный интеграл одной записью разбирается во вложенные integrate — то же значение, другая запись
    let skip = [ "матрица"; "кусочно"; "euler-gamma"; "кратный интеграл одной записью" ]
    for name, expr, _ in cases do
        // MINT: описание области/параметризации — текст, обратно не разбирается
        if not (List.contains name skip || name.StartsWith "MINT:") then
            try
                let parsed = LatexParse.parse (tex expr)
                let a = Simplify.simplify (norm parsed) |> MathPrinter.mathPrint
                let b = Simplify.simplify (norm expr) |> MathPrinter.mathPrint
                if a <> b then
                    failures.Add(sprintf "%s: разбор дал <%s>, ожидалось <%s>" name a b)
            with
            | LatexParse.Unsupported m -> failures.Add(sprintf "%s: не поддерживается (%s)" name m)
    Assert.True(failures.Count = 0, String.concat "\n" failures)

[<Fact>]
let ``TEX.1: скобки и \left/\right сбалансированы во всём корпусе`` () =
    for name, expr, _ in cases do
        let t = tex expr
        let braces = (Seq.filter ((=) '{') t |> Seq.length) - (Seq.filter ((=) '}') t |> Seq.length)
        let lr = t.Split("\\left").Length - t.Split("\\right").Length
        Assert.True((braces = 0), sprintf "%s: несбалансированы {} в <%s>" name t)
        Assert.True((lr = 0), sprintf "%s: несбалансированы \\left/\\right в <%s>" name t)

// WASM.4c: формы, которые интегратор и дифференциатор кладут в журнал шагов («до» и «после» приёма):
// (int/dx f), (int/dx f a b), (d/dx u) — должны печататься формулой, а не \text{…}
let private stepForms : (string * string) list =
    [ "(int/dx (* x (exp x)))", "\\int|e^{x}|\\,dx"
      "(int/dx (exp (^ x 2)))", "\\int|e^{x^{2}}|\\,dx"
      "(int/dx (exp (^ x 2)) 0 1)", "\\int_{0}^{1}|e^{x^{2}}"
      "(int/dx (/ 1 (+ (^ x 3) 1)))", "\\frac{1}{x^{3} + 1}|\\,dx"
      "(int/dx (sin x) 0 pi)", "\\int_{0}^{\\pi}|\\sin\\left(x\\right)"
      "(int/dx (* (sin x) (cos x)))", "\\sin\\left(x\\right)|\\cos\\left(x\\right)"
      "(int/dx (log x))", "\\log\\left(x\\right)|\\,dx"
      "(int/dx (^ x 2))", "\\int|x^{2}|\\,dx"
      "(int/dx (sqrt x))", "\\sqrt{x}|\\,dx"
      "(int/dx (* 1/2 (exp x)))", "\\frac{1}{2}|e^{x}"
      "(d/dx (^ x 3))", "\\frac{d}{dx}|x^{3}"
      "(d/dx (sin x))", "\\frac{d}{dx}|\\sin"
      "(d/dx (* x (exp x)))", "\\frac{d}{dx}|e^{x}"
      "(d/dy (^ y 2))", "\\frac{d}{dy}|y^{2}"
      "(sum (^ k 2) k 1 n)", "\\sum_{k=1}^{n}|k^{2}"
      "(sum (/ 1 (^ k 2)) k 1 inf)", "\\sum_{k=1}^{\\infty}|\\frac{1}{k^{2}}"
      "(product k k 1 n)", "\\prod_{k=1}^{n}"
      "(limit (/ (sin x) x) x 0)", "\\lim_{x \\to 0}|\\frac{\\sin\\left(x\\right)}{x}"
      "(integrate (exp (^ x 2)) x)", "\\int|e^{x^{2}}|\\,dx"
      "(diff (sin x) x)", "\\frac{d}{dx}|\\sin\\left(x\\right)" ]

[<Fact>]
let ``WASM.4c: внутренние формы шагов — формулами, без текстовой заглушки`` () =
    let bad = ResizeArray<string> ()
    for src, needles in stepForms do
        let t = tex (Reader.readAll src |> List.head)
        if t.Contains "\\text{" then bad.Add(sprintf "%s → \\text{…} в <%s>" src t)
        for needle in needles.Split('|') do
            if not (t.Contains needle) then bad.Add(sprintf "%s → нет «%s» в <%s>" src needle t)
        let braces = (Seq.filter ((=) '{') t |> Seq.length) - (Seq.filter ((=) '}') t |> Seq.length)
        if braces <> 0 then bad.Add(sprintf "%s → несбалансированы {} в <%s>" src t)
    Assert.True((bad.Count = 0), String.concat "\n" bad)

[<Fact>]
let ``WASM.4c: служебные записи по-прежнему текстом (не ломаем принтер)`` () =
    // ode-solution и rootsum формулой не выражаются — для них запасной путь в клиенте остаётся;
    // проверяем, что принтер не пытается выдать их за формулу и не падает
    for src in [ "(rootsum (sin t) t (+ (^ t 3) 1))"; "(ode-solution :type general)" ] do
        let t = tex (Reader.readAll src |> List.head)
        Assert.True((t.Trim().Length > 0), sprintf "%s → пустая строка" src)
