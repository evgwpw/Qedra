// LaTeX-принтер математических выражений (шаг TEX.1)
// Lisp-дерево → строка LaTeX, совместимая с KaTeX (без пакетов).
// Принципы те же, что у MathPrinter: минимальные скобки по приоритетам, детерминированность, без упрощений.
// Не-математические значения — \text{...} с обычным prettyPrint внутри (не ошибка).
module LatexPrinter

open System
open Types
open Printer
open MathPrinter

// --- Приоритеты: та же шкала, что у MathPrinter (больше — сильнее связывает) ---
let private precAtom = 12
let private precPostfix = 11
let private precPow = 10
let private precUnary = 9
let private precMul = 8
let private precAdd = 7
let private precSetI = 6
let private precSetU = 5
let private precRel = 4
let private precNot = 3
let private precAnd = 2
let private precOr = 1
let private precTop = 0

// Греческие имена → команды LaTeX
let private greek : Map<string, string> =
    Map.ofList [
        "alpha", "\\alpha"; "beta", "\\beta"; "gamma", "\\gamma"; "delta", "\\delta"
        "epsilon", "\\epsilon"; "varepsilon", "\\varepsilon"; "zeta", "\\zeta"; "eta", "\\eta"
        "theta", "\\theta"; "vartheta", "\\vartheta"; "iota", "\\iota"; "kappa", "\\kappa"
        "lambda", "\\lambda"; "mu", "\\mu"; "nu", "\\nu"; "xi", "\\xi"; "pi", "\\pi"
        "rho", "\\rho"; "sigma", "\\sigma"; "tau", "\\tau"; "upsilon", "\\upsilon"
        "phi", "\\phi"; "varphi", "\\varphi"; "chi", "\\chi"; "psi", "\\psi"; "omega", "\\omega"
        "Gamma", "\\Gamma"; "Delta", "\\Delta"; "Theta", "\\Theta"; "Lambda", "\\Lambda"
        "Xi", "\\Xi"; "Pi", "\\Pi"; "Sigma", "\\Sigma"; "Phi", "\\Phi"; "Psi", "\\Psi"; "Omega", "\\Omega"
    ]

// Имена элементарных функций → команды LaTeX
let private funcCommands : Map<string, string> =
    Map.ofList [
        "sin", "\\sin"; "cos", "\\cos"; "tan", "\\tan"; "cot", "\\cot"; "sec", "\\sec"; "csc", "\\csc"
        "sinh", "\\sinh"; "cosh", "\\cosh"; "tanh", "\\tanh"; "coth", "\\coth"; "sech", "\\operatorname{sech}"; "csch", "\\operatorname{csch}"
        "asin", "\\arcsin"; "acos", "\\arccos"; "atan", "\\arctan"
        "acot", "\\operatorname{arccot}"; "asec", "\\operatorname{arcsec}"; "acsc", "\\operatorname{arccsc}"
        "asinh", "\\operatorname{arcsinh}"; "acosh", "\\operatorname{arccosh}"; "atanh", "\\operatorname{arctanh}"
        "acoth", "\\operatorname{arccoth}"; "asech", "\\operatorname{arcsech}"; "acsch", "\\operatorname{arccsch}"
        "log", "\\log"; "ln", "\\ln"
    ]

let private sfCommands : Map<string, string * string> =
    // имя головы → (команда, индекс: "" | "nu" | "n")
    Map.ofList [
        "bessel-j", ("J", "nu"); "bessel-y", ("Y", "nu"); "bessel-i", ("I", "nu"); "bessel-k", ("K", "nu")
        "airy-ai", ("\\operatorname{Ai}", ""); "airy-bi", ("\\operatorname{Bi}", "")
        "airy-ai-prime", ("\\operatorname{Ai}'", ""); "airy-bi-prime", ("\\operatorname{Bi}'", "")
        "legendre-p", ("P", "n"); "legendre-q", ("Q", "n")
    ]

let private isIdent (s: string) : bool =
    s.Length > 0 && (Char.IsLetter s.[0] || s.[0] = '_' || s.[0] = '%')
    && s |> Seq.forall (fun c -> Char.IsLetterOrDigit c || c = '_' || c = '?' || c = '%')

// Шаг WASM.4c: внутренние головы шагов — (int/dx f), (int/dx f a b), (d/dx u) — печатаются формулой,
// а не \text{…}: до этого шага записи журнала (до/после приёма) попадали в дерево шагов текстом
let private isIntHead (s: string) : bool = s.Length > 5 && s.StartsWith "int/d" && isIdent (s.Substring 5)
let private isDerivHead (s: string) : bool = s.Length > 3 && s.StartsWith "d/d" && isIdent (s.Substring 3)

// Экранирование текста для \text{...}
let private escapeText (s: string) : string =
    let sb = Text.StringBuilder()
    for c in s do
        match c with
        | '\\' -> sb.Append("\\textbackslash{}") |> ignore
        | '{' | '}' | '_' | '%' | '&' | '#' | '$' -> sb.Append('\\').Append(c) |> ignore
        | '^' -> sb.Append("\\textasciicircum{}") |> ignore
        | '~' -> sb.Append("\\textasciitilde{}") |> ignore
        | _ -> sb.Append(c) |> ignore
    sb.ToString()

// Символ: греческие, ∞, индексы x_1 → x_{1}
let private symbolTex (s: string) : string =
    match s with
    | "inf" -> "\\infty"
    | "-inf" -> "-\\infty"
    | "euler-gamma" -> "\\gamma"
    // мнимая единица: в LaTeX знак % начинает комментарий, поэтому печатается буквой i
    | "%i" -> "i"
    | _ when greek.ContainsKey s -> greek.[s]
    | _ ->
        let i = s.IndexOf('_')
        if i > 0 && i < s.Length - 1 && isIdent s then
            let head = match greek.TryFind (s.Substring(0, i)) with Some g -> g | None -> s.Substring(0, i)
            head + "_{" + s.Substring(i + 1) + "}"
        elif isIdent s then s
        else "\\text{" + escapeText s + "}"

// Отрицательное вещественное число?
let private isNegReal (v: LispValue) : bool =
    match v with
    | LispInteger n -> n.Sign < 0
    | LispRational (p, _) -> p.Sign < 0
    | LispFloat f -> f < 0.0
    | _ -> false

let private negReal (v: LispValue) : LispValue =
    match v with
    | LispInteger n -> LispInteger (-n)
    | LispRational (p, q) -> LispRational (-p, q)
    | LispFloat f -> LispFloat (-f)
    | other -> other

// Терм с отрицательным числовым коэффициентом → положительный (для «a - b»)
let private positiveTerm (t: LispValue) : LispValue option =
    match t with
    | LispList (LispSym "*" :: c :: rest) when isNegReal c && not rest.IsEmpty ->
        let pc = negReal c
        match pc with
        | LispInteger one when one.IsOne -> (match rest with [single] -> Some single | _ -> Some (LispList (LispSym "*" :: rest)))
        | _ -> Some (LispList (LispSym "*" :: pc :: rest))
    | _ -> None

// --- TEX.MI: кратные, криволинейные и поверхностные интегралы (lib/multiint.lisp) ---
let private mintNames =
    set [ "surface_area"; "surface_integral"; "arc_length"; "line_integral"; "integrate_form"; "integrate_change"
          "integrate_region"; "green_check"; "stokes_check"; "gauss_check" ]

// [t, a, b] как (имя, a, b)
let private rangeParts (r: LispValue) =
    match r with
    | LispList [ LispSym "m-vector"; LispSym v; a; b ] -> Some (v, a, b)
    | _ -> None

// [e1, e2, …] как список компонент
let private vecParts (v: LispValue) =
    match v with
    | LispList (LispSym "m-vector" :: cs) when not cs.IsEmpty -> Some cs
    | _ -> None

let private allSome (xs: 'a option list) : 'a list option =
    if xs |> List.forall Option.isSome then Some (xs |> List.map Option.get) else None

// Численное значение выражения от параметра t (посторонние символы — фиксированные «случайные» значения);
// нужно только чтобы отличить замкнутую кривую r(a) = r(b) от незамкнутой
let rec private numEval (t: string) (tv: float) (v: LispValue) : float option =
    match v with
    | LispInteger n -> Some (float n)
    | LispFloat f -> Some f
    | LispRational (p, q) -> Some (float p / float q)
    | LispSym "pi" -> Some Math.PI
    | LispSym s when s = t -> Some tv
    | LispSym s -> Some (1.3 + float ((s |> Seq.sumBy int) % 53) / 17.0)
    | LispList (LispSym op :: args) ->
        let vs = args |> List.map (numEval t tv)
        if vs |> List.exists Option.isNone then None
        else
            match op, vs |> List.map Option.get with
            | "+", xs -> Some (List.sum xs)
            | "*", xs -> Some (List.fold (*) 1.0 xs)
            | "-", [ a ] -> Some (-a)
            | "-", a :: rest -> Some (a - List.sum rest)
            | "/", [ a; b ] -> Some (a / b)
            | "^", [ a; b ] -> Some (Math.Pow(a, b))
            | "sin", [ a ] -> Some (Math.Sin a)
            | "cos", [ a ] -> Some (Math.Cos a)
            | "tan", [ a ] -> Some (Math.Tan a)
            | "exp", [ a ] -> Some (Math.Exp a)
            | "sqrt", [ a ] -> Some (Math.Sqrt a)
            | _ -> None
    | _ -> None

// r(a) = r(b) во всех компонентах (иначе — не считаем замкнутой)
let private isClosedCurve (comps: LispValue list) (t: string) (a: LispValue) (b: LispValue) =
    match numEval t 0.0 a, numEval t 0.0 b with
    | Some av, Some bv when abs (av - bv) > 1e-12 ->
        comps |> List.forall (fun c ->
            match numEval t av c, numEval t bv c with
            | Some x, Some y when not (Double.IsNaN x || Double.IsNaN y || Double.IsInfinity x || Double.IsInfinity y) ->
                abs (x - y) <= 1e-9 * (1.0 + abs x)
            | _ -> false)
    | _ -> false

// v - c без лишних «- 0» и «- -1»
let private shifted (v: LispValue) (c: LispValue) : LispValue =
    match c with
    | LispInteger z when z.IsZero -> v
    | _ when isNegReal c -> LispList [ LispSym "+"; v; negReal c ]
    | LispList [ LispSym "-"; e ] -> LispList [ LispSym "+"; v; e ]
    | LispList [ LispSym "-"; LispInteger z; e ] when z.IsZero -> LispList [ LispSym "+"; v; e ]
    | _ -> LispList [ LispSym "-"; v; c ]

let rec private tex (context: int) (v: LispValue) : string =
    let wrap (text: string) (prec: int) : string =
        if prec < context then "\\left(" + text + "\\right)" else text
    // База степени: атомы и функции — без скобок, всё прочее — в \left(...\right)
    let powBase (b: LispValue) =
        match b with
        | LispInteger _ | LispFloat _ | LispRational _ | LispSym _ -> tex precAtom b
        // exp(x)^2: e^{x} уже со степенью — без скобок вышло бы e^{x}^{2} (двойной верхний индекс, ошибка LaTeX)
        | LispList [LispSym "exp"; _] -> "\\left(" + tex precTop b + "\\right)"
        | LispList (LispSym _ :: _) -> tex precAtom b
        | _ -> "\\left(" + tex precTop b + "\\right)"
    match v with
    | LispInteger n -> wrap (string n) precAtom
    | LispFloat f -> wrap (string f) precAtom
    | LispRational (p, q) ->
        if p.Sign < 0 then wrap ("-\\frac{" + string (-p) + "}{" + string q + "}") precUnary
        else wrap ("\\frac{" + string p + "}{" + string q + "}") precMul
    | LispSym s -> wrap (symbolTex s) precAtom
    | LispBool b -> wrap ("\\text{" + (if b then "true" else "false") + "}") precAtom
    | LispStr s -> wrap ("\\text{" + escapeText s + "}") precAtom
    | LispComplex (re, im) ->
        let imText = tex precAtom (negReal im)
        let sign = if isNegReal im then " - " else " + "
        wrap (tex precAdd re + sign + imText + "i") precAdd
    | LispObject _ ->
        // Объекты печатаются своей математической формой; интервалы — \left[0, 1\right)
        let m = mathPrint v
        if m.Length > 2 && (m.[0] = '[' || m.[0] = '(') && (m.[m.Length - 1] = ']' || m.[m.Length - 1] = ')') && m.Contains "," then
            let openB = if m.[0] = '[' then "\\left[" else "\\left("
            let closeB = if m.[m.Length - 1] = ']' then "\\right]" else "\\right)"
            wrap (openB + escapeText (m.Substring(1, m.Length - 2)) + closeB) precAtom
        else wrap ("\\text{" + escapeText m + "}") precAtom
    // WASM.4c: служебные записи шагов, которые всё же выражаются формулой — список уравнений
    // ((= (y x) rhs) …) и одиночное булево (#f) из проверки решения
    | LispList eqs when not eqs.IsEmpty
                        && eqs |> List.forall (function
                            | LispList (LispSym r :: [ _; _ ]) ->
                                List.contains r [ "="; "/="; "!="; "<"; ">"; "<="; ">=" ]
                            | _ -> false) ->
        wrap (String.concat ", " (eqs |> List.map (fun e -> tex precTop e))) precTop
    | LispList [ LispBool b ] -> wrap ("\\text{" + (if b then "true" else "false") + "}") precAtom
    | LispList (LispSym op :: args) ->
        match op, args with
        | "+", [] -> wrap "0" precAtom
        | "+", [single] -> tex context single
        | "+", first :: rest ->
            let restText =
                rest |> List.map (fun a ->
                    match positiveTerm a with
                    | Some pos -> " - " + tex (precAdd + 1) pos
                    | None -> " + " + tex (precAdd + 1) a)
            wrap (tex precAdd first + String.concat "" restText) precAdd
        | "-", [] -> wrap (prettyPrint v) precAtom
        | "-", [single] -> wrap ("-" + tex precUnary single) precUnary
        | "-", [LispInteger z; single] when z.IsZero -> wrap ("-" + tex precUnary single) precUnary
        | "-", first :: rest ->
            wrap (String.concat " - " (tex precAdd first :: (rest |> List.map (fun a -> tex (precAdd + 1) a)))) precAdd
        | "*", [] -> wrap "1" precAtom
        | "*", [single] -> tex context single
        | "*", _ ->
            // коэффициент -1 → унарный минус; отрицательные показатели → знаменатель
            let hasDenom = args |> List.exists (function LispList [LispSym "^"; _; n] when isNegReal n -> true | _ -> false)
            let argsR, extraDen =
                match args with
                | LispRational (p, q) :: rest when hasDenom -> (if p.IsOne then rest else LispInteger p :: rest), [LispInteger q]
                | _ -> args, []
            let neg, args' =
                match argsR with
                | LispInteger m :: (_ :: _ as rest) when m = -1I -> true, rest
                | _ -> false, argsR
            let denomOf (f: LispValue) =
                match f with
                | LispList [LispSym "^"; b; n] when isNegReal n ->
                    let pn = negReal n
                    match pn with
                    | LispInteger one when one.IsOne -> Some b
                    | _ -> Some (LispList [LispSym "^"; b; pn])
                | _ -> None
            let numer = args' |> List.filter (fun a -> (denomOf a).IsNone)
            let denom = extraDen @ (args' |> List.choose denomOf)
            // Соединение множителей: без знака умножения там, где это однозначно
            let joinText (fs: LispValue list) =
                fs |> List.map (fun a -> tex precMul a)
                |> List.reduce (fun l r ->
                    if r.StartsWith("\\left(") || r.StartsWith("\\left[") || r.StartsWith("\\left\\{") then l + r
                    elif r.Length > 0 && Char.IsLetter r.[0] && l |> Seq.forall Char.IsDigit then l + r
                    elif l.Length > 0 && Char.IsLetter l.[0] && r.Length > 0 && Char.IsLetter r.[0] then l + " " + r
                    elif l.Length > 0 && Char.IsDigit l.[l.Length - 1] && r.Length > 0 && Char.IsDigit r.[0] then l + " \\cdot " + r
                    else l + " \\cdot " + r)
            // В \frac{…}{…} фигурные скобки уже группируют: внешние \left( … \right) избыточны
            // (ревью WASM.1: \frac{a}{\left(b c\right)} → \frac{a}{b c})
            // Снимать только если первая «\left(» закрывается последней «\right)»: в «\left(a\right) \cdot \log\left(b\right)»
            // это разные пары, и снятие ломало скобки (\log\left(b}{…}\right) — KaTeX: ошибка разбора)
            let outerPairs (s: string) =
                let mutable depth = 0
                let mutable ok = true
                let mutable i = 0
                while ok && i < s.Length do
                    if String.CompareOrdinal(s, i, "\\left", 0, 5) = 0 then (depth <- depth + 1; i <- i + 5)
                    elif String.CompareOrdinal(s, i, "\\right", 0, 6) = 0 then
                        depth <- depth - 1
                        i <- i + 6
                        if depth = 0 && i < s.Length - 1 then ok <- false
                    else i <- i + 1
                ok
            let stripOuterParens (s: string) =
                if s.Length > 13 && s.StartsWith("\\left(") && s.EndsWith("\\right)") && outerPairs s then
                    s.Substring(6, s.Length - 13)
                else s
            let body =
                if denom.IsEmpty then joinText numer
                else
                    let numText = if numer.IsEmpty then "1" else stripOuterParens (joinText numer)
                    let denText =
                        if denom.Length = 1 then stripOuterParens (tex (precMul + 1) denom.Head)
                        else "\\left(" + joinText denom + "\\right)"
                    "\\frac{" + numText + "}{" + stripOuterParens denText + "}"
            if neg then wrap ("-" + body) precUnary else wrap body precMul
        | "/", [single] -> wrap ("\\frac{1}{" + tex precTop single + "}") precMul
        | "/", first :: rest ->
            wrap ("\\frac{" + tex precTop first + "}{" + String.concat " \\cdot " (rest |> List.map (fun a -> tex precTop a)) + "}") precMul
        // (1/cos u)^r → \sec^{r}(u): упрощатель хранит sec/csc/sech/csch как (^ (cos u) -1) и т. п.;
        // запись \left(\frac{1}{\cos u}\right)^{7/2} верна, но не то, что ввёл человек
        | "^", [LispList [LispSym "^"; LispList [LispSym f; arg]; LispInteger m]; ex]
            when m = -1I && (match f with "cos" | "sin" | "cosh" | "sinh" | "tan" -> true | _ -> false) ->
            let recip =
                match f with
                | "cos" -> "\\sec" | "sin" -> "\\csc" | "cosh" -> "\\operatorname{sech}"
                | "sinh" -> "\\operatorname{csch}" | _ -> "\\cot"
            wrap (recip + "^{" + tex precTop ex + "}\\left(" + tex precTop arg + "\\right)") precPow
        // cos(x)^(-2) → \frac{1}{\cos^{2}(x)}: \cos^{-2} читается как степень арккосинуса
        | "^", [LispList [LispSym f; _] as bse; ex]
            when funcCommands.ContainsKey f && isNegReal ex && (match ex with LispInteger n -> n <> -1I | _ -> true) ->
            wrap ("\\frac{1}{" + tex precTop (LispList [LispSym "^"; bse; negReal ex]) + "}") precMul
        | "^", [bse; LispRational (p, q)] when p.IsOne && q = 2I ->
            wrap ("\\sqrt{" + tex precTop bse + "}") precAtom
        | "^", [bse; LispRational (p, q)] when p.IsOne && q = 3I ->
            wrap ("\\sqrt[3]{" + tex precTop bse + "}") precAtom
        | "^", [bse; ex] when (match ex with LispInteger n -> n = -1I | _ -> false) ->
            wrap ("\\frac{1}{" + tex precTop bse + "}") precMul
        | "^", [bse; ex] ->
            // sin(x)^2 → \sin^{2}\left(x\right)
            match bse, ex with
            | LispList [LispSym f; arg], _ when funcCommands.ContainsKey f ->
                wrap (funcCommands.[f] + "^{" + tex precTop ex + "}\\left(" + tex precTop arg + "\\right)") precPow
            | _ -> wrap (powBase bse + "^{" + tex precTop ex + "}") precPow
        | rel, [l; r] when List.contains rel ["="; "/="; "!="; "<"; ">"; "<="; ">="] ->
            let sign = match rel with "/=" | "!=" -> "\\ne" | "<=" -> "\\le" | ">=" -> "\\ge" | s -> s
            wrap (tex precSetU l + " " + sign + " " + tex precSetU r) precRel
        | "and", _ :: _ :: _ -> wrap (String.concat " \\land " (args |> List.map (tex (precAnd + 1)))) precAnd
        | "or", _ :: _ :: _ -> wrap (String.concat " \\lor " (args |> List.map (tex (precOr + 1)))) precOr
        | "not", [a] -> wrap ("\\lnot " + tex precNot a) precNot
        | ":in", [x; d] -> wrap (tex precSetU x + " \\in " + tex precSetU d) precRel
        | "m-set", _ -> wrap ("\\left\\{" + String.concat ", " (args |> List.map (tex precTop)) + "\\right\\}") precAtom
        | "m-vector", _ when args |> List.forall (function LispList (LispSym "m-vector" :: _) -> true | _ -> false) ->
            // матрица: вектор векторов → pmatrix
            let rows =
                args |> List.map (function
                    | LispList (LispSym "m-vector" :: cells) -> String.concat " & " (cells |> List.map (tex precTop))
                    | _ -> "")
            wrap ("\\begin{pmatrix} " + String.concat " \\\\ " rows + " \\end{pmatrix}") precAtom
        | "m-vector", _ -> wrap ("\\left[" + String.concat ", " (args |> List.map (tex precTop)) + "\\right]") precAtom
        | "m-index", bse :: idx -> wrap (tex precPostfix bse + "_{" + String.concat "," (idx |> List.map (tex precTop)) + "}") precPostfix
        | "factorial", [a] -> wrap (tex precPostfix a + "!") precPostfix
        | "binomial", [n; k] -> wrap ("\\binom{" + tex precTop n + "}{" + tex precTop k + "}") precAtom
        | "union", _ :: _ :: _ -> wrap (tex precSetU args.Head + String.concat "" (args.Tail |> List.map (fun a -> " \\cup " + tex (precSetU + 1) a))) precSetU
        | "intersection", _ :: _ :: _ -> wrap (tex precSetI args.Head + String.concat "" (args.Tail |> List.map (fun a -> " \\cap " + tex (precSetI + 1) a))) precSetI
        | "set-difference", _ :: _ :: _ -> wrap (tex precSetU args.Head + String.concat "" (args.Tail |> List.map (fun a -> " \\setminus " + tex (precSetU + 1) a))) precSetU
        // Невычисленные производная и интеграл
        | "diff", [e; LispSym x] -> wrap ("\\frac{d}{d" + x + "}\\left(" + tex precTop e + "\\right)") precAtom
        // Шаг WASM.4c: те же формы в записи журнала шагов — (d/dx u), (int/dx f), (int/dx f a b)
        | name, [u] when isDerivHead name ->
            wrap ("\\frac{d}{d" + symbolTex (name.Substring 3) + "}\\left(" + tex precTop u + "\\right)") precAtom
        | name, [e] when isIntHead name ->
            wrap ("\\int " + tex precMul e + "\\,d" + symbolTex (name.Substring 5)) precAtom
        | name, [e; a; b] when isIntHead name ->
            wrap ("\\int_{" + tex precTop a + "}^{" + tex precTop b + "} " + tex precMul e + "\\,d" + symbolTex (name.Substring 5)) precAtom
        // TEX.MI: аргументы не того вида — mintTex даёт None и печать идёт общим \operatorname{…}
        | name, _ when mintNames.Contains name && (mintTex name args).IsSome ->
            wrap (mintTex name args).Value precAtom
        | "integrate", [e; LispSym x] -> wrap ("\\int " + tex precMul e + "\\,d" + x) precAtom
        | "integrate", [e; LispSym x; a; b] ->
            wrap ("\\int_{" + tex precTop a + "}^{" + tex precTop b + "} " + tex precMul e + "\\,d" + x) precAtom
        // MINT.a: кратный интеграл одной записью integrate(f, [x, a, b], [y, c, d], …) — первый список внешний:
        // \int_a^b \int_c^d f\,dy\,dx (дифференциалы — от внутреннего к внешнему)
        | "integrate", e :: (_ :: _ as ranges)
            when ranges |> List.forall (function
                    | LispList [LispSym "m-vector"; LispSym _] | LispList [LispSym "m-vector"; LispSym _; _; _] -> true
                    | _ -> false) ->
            let sign (r: LispValue) =
                match r with
                | LispList [LispSym _; LispSym _; a; b] -> "\\int_{" + tex precTop a + "}^{" + tex precTop b + "} "
                | _ -> "\\int "
            let dvar (r: LispValue) = match r with LispList (_ :: LispSym v :: _) -> "\\,d" + symbolTex v | _ -> ""
            wrap (String.concat "" (ranges |> List.map sign) + tex precMul e + String.concat "" (ranges |> List.rev |> List.map dvar)) precAtom
        // Сумма/произведение/предел
        | "sum", [e; LispSym k; a; b] ->
            wrap ("\\sum_{" + k + "=" + tex precTop a + "}^{" + tex precTop b + "} " + tex precMul e) precAtom
        | "product", [e; LispSym k; a; b] ->
            wrap ("\\prod_{" + k + "=" + tex precTop a + "}^{" + tex precTop b + "} " + tex precMul e) precAtom
        | "limit", [e; LispSym x; a] ->
            wrap ("\\lim_{" + x + " \\to " + tex precTop a + "} " + tex precMul e) precAtom
        | "piecewise", [LispList branches] ->
            let rows =
                branches |> List.choose (fun b ->
                    match b with
                    | LispList [c; e] -> Some (tex precTop e + ", & " + tex precTop c)
                    | _ -> None)
            wrap ("\\begin{cases} " + String.concat " \\\\ " rows + " \\end{cases}") precAtom
        | "root-sum", [LispSym tv; q; e] ->
            wrap ("\\operatorname{rootsum}\\left(" + tex precTop e + ", " + tv + ", " + tex precTop q + "\\right)") precAtom
        // WASM.6a Д1: ответ ОДУ — уравнения (общее и особые через ∨), а не служебная запись
        | "ode-solution", _ ->
            let rec field (key: string) (xs: LispValue list) : LispValue option =
                match xs with
                | LispSym k :: value :: rest -> if k = key then Some value else field key rest
                | _ :: rest -> field key rest
                | [] -> None
            let asList (x: LispValue option) =
                match x with
                | Some (LispList xs) -> xs
                | _ -> []
            let eqs = asList (field ":solutions" args) @ asList (field ":singular" args)
            if not eqs.IsEmpty then
                wrap (eqs |> List.map (tex precTop) |> String.concat "\\ \\lor\\ ") precAtom
            else wrap "\\text{unknown}" precAtom
        | "euler-gamma", [] -> wrap "\\gamma" precAtom
        | ("gamma" | "psi"), _ ->
            let cmd = if op = "gamma" then "\\Gamma" else "\\psi"
            wrap (cmd + "\\left(" + String.concat ", " (args |> List.map (tex precTop)) + "\\right)") precAtom
        // SF.HYP: {}_2F_1(a, b; c; z) и F_1(a; b_1, b_2; c; x, y)
        | "hypergeometric-2f1", [a; b; c; z] ->
            wrap ("{}_2F_1\\left(" + tex precTop a + ", " + tex precTop b + "; " + tex precTop c + "; " + tex precTop z + "\\right)") precAtom
        | "appell-f1", [a; b1; b2; c; x; y] ->
            wrap ("F_1\\left(" + tex precTop a + "; " + tex precTop b1 + ", " + tex precTop b2 + "; " + tex precTop c + "; "
                  + tex precTop x + ", " + tex precTop y + "\\right)") precAtom
        | name, _ :: _ when Map.containsKey name sfCommands ->
            let cmd, idxKind = sfCommands.[name]
            // индекс: рациональный — как p/q (J_{1/3}), иначе обычная запись
            let idxTex (a: LispValue) =
                match a with
                | LispRational (p, q) when p.Sign >= 0 -> string p + "/" + string q
                | _ -> tex precTop a
            let idx = if idxKind = "" then "" else "_{" + idxTex args.Head + "}"
            let rest = if idxKind = "" then args else args.Tail
            wrap (cmd + idx + "\\left(" + String.concat ", " (rest |> List.map (tex precTop)) + "\\right)") precAtom
        | "sqrt", [a] -> wrap ("\\sqrt{" + tex precTop a + "}") precAtom
        | "exp", [a] -> wrap ("e^{" + tex precTop a + "}") precAtom
        | "abs", [a] -> wrap ("\\left|" + tex precTop a + "\\right|") precAtom
        | name, [arg] when funcCommands.ContainsKey name ->
            wrap (funcCommands.[name] + "\\left(" + tex precTop arg + "\\right)") precAtom
        // Неизвестная голова: \operatorname{f}\left(...\right) — не ошибка
        | name, _ when isIdent name ->
            // «_» в имени (arc_length, integrate_change) — текстовое подчёркивание, а не нижний индекс
            wrap ("\\operatorname{" + name.Replace("-", "}").Replace("_", "\\_") + "}\\left(" + String.concat ", " (args |> List.map (tex precTop)) + "\\right)") precAtom
        | _ -> wrap ("\\text{" + escapeText (prettyPrint v) + "}") precAtom
    // REL.1e П5а: результат-список без головы-символа (groebner, eigenvalues) — вектор формул,
    // а не \text{...} с \textasciicircum
    | LispList xs when not xs.IsEmpty ->
        wrap ("\\left[" + (xs |> List.map (tex precTop) |> String.concat ", ") + "\\right]") precAtom
    | _ -> wrap ("\\text{" + escapeText (prettyPrint v) + "}") precAtom

// TEX.MI: учебная запись интегралов; None — аргументы не того вида
and private mintTex (op: string) (args: LispValue list) : string option =
    let tx = tex precTop
    let rng (v: string, a, b) = symbolTex v + " \\in [" + tx a + ", " + tx b + "]"
    let vars (rs: (string * LispValue * LispValue) list) = String.concat ", " (rs |> List.map (fun (v, _, _) -> symbolTex v))
    let param (comps: LispValue list) rs =
        "\\mathbf{r}(" + vars rs + ") = (" + String.concat ", " (comps |> List.map tx) + "),\\ "
        + String.concat ",\\ " (rs |> List.map rng)
    let curve r t =
        match vecParts r, rangeParts t with
        | Some cs, Some (tv, a, b) -> Some (cs, (tv, a, b))
        | _ -> None
    let surf r ru rv =
        match vecParts r, rangeParts ru, rangeParts rv with
        | Some cs, Some p, Some q -> Some (cs, [ p; q ])
        | _ -> None
    let curveTail (cs, rg) = ",\\quad C:\\ " + param cs [ rg ]
    let surfTail (cs, rgs) = ",\\quad S:\\ " + param cs rgs
    let vecTex (v: LispValue) =
        match vecParts v with
        | Some cs -> "(" + String.concat ", " (cs |> List.map tx) + ")"
        | None -> tx v
    let point (p: LispValue) = vecParts p |> Option.map (fun cs -> "(" + String.concat ", " (cs |> List.map tx) + ")")
    let sq (e: LispValue) = tex precPow (LispList [ LispSym "^"; e; LispInteger (bigint 2) ])
    let rel (e: LispValue) = tex (precRel + 1) e
    // дифференциальная форма: -y*dx + x*dy → -y\,dx + x\,dy
    let formTex (w: LispValue) =
        let isD (s: string) = s.Length > 1 && s.[0] = 'd'
        let term (t: LispValue) =
            match t with
            | LispList (LispSym "*" :: (_ :: _ :: _ as xs)) when (match List.last xs with LispSym s -> isD s | _ -> false) ->
                let d = match List.last xs with LispSym s -> symbolTex s | _ -> ""
                let body = xs |> List.take (xs.Length - 1)
                (match body with [ b ] -> tex precMul b | _ -> tex precMul (LispList (LispSym "*" :: body))) + "\\," + d
            | _ -> tx t
        let terms = match w with LispList (LispSym "+" :: ts) when ts.Length > 1 -> ts | _ -> [ w ]
        terms |> List.map term
        |> List.mapi (fun i s -> if i = 0 then s elif s.StartsWith "-" then " - " + s.Substring 1 else " + " + s)
        |> String.concat ""
    let region (reg: LispValue) : string option =
        match reg with
        | LispList [ LispSym "rect_region"; r1; r2 ] ->
            match rangeParts r1, rangeParts r2 with
            | Some (_, a, b), Some (_, c, d) -> Some ("[" + tx a + ", " + tx b + "] \\times [" + tx c + ", " + tx d + "]")
            | _ -> None
        | LispList [ LispSym "region"; LispSym x; a; b; LispSym y; g1; g2 ] ->
            Some (tx a + " \\le " + symbolTex x + " \\le " + tx b + ",\\ " + tx g1 + " \\le " + symbolTex y + " \\le " + tx g2)
        | LispList [ LispSym "triangle_region"; _; p1; p2; p3 ] ->
            match point p1, point p2, point p3 with
            | Some a, Some b, Some c -> Some ("\\triangle " + a + ", " + b + ", " + c)
            | _ -> None
        | LispList [ LispSym "disk_region"; vs; c; r ] ->
            match vecParts vs, vecParts c with
            | Some [ LispSym x; LispSym y ], Some [ cx; cy ] ->
                Some (sq (shifted (LispSym x) cx) + " + " + sq (shifted (LispSym y) cy) + " \\le " + sq r)
            | _ -> None
        | LispList [ LispSym "annulus_region"; vs; c; r1; r2 ] ->
            match vecParts vs, vecParts c with
            | Some [ LispSym x; LispSym y ], Some [ cx; cy ] ->
                Some (sq r1 + " \\le " + sq (shifted (LispSym x) cx) + " + " + sq (shifted (LispSym y) cy) + " \\le " + sq r2)
            | _ -> None
        | _ -> None
    match op, args with
    | "surface_area", [ r; ru; rv ] ->
        surf r ru rv |> Option.map (fun s -> "\\iint_{S} dS" + surfTail s)
    | "surface_integral", [ f; _; r; ru; rv ] ->
        surf r ru rv |> Option.map (fun s -> "\\iint_{S} " + tex precMul f + "\\,dS" + surfTail s)
    | "arc_length", [ r; t ] ->
        curve r t |> Option.map (fun c -> "\\int_{C} ds" + curveTail c)
    | "line_integral", [ f; _; r; t ] ->
        curve r t |> Option.map (fun c -> "\\int_{C} " + tex precMul f + "\\,ds" + curveTail c)
    | "integrate_form", [ w; _; r; t ] ->
        curve r t |> Option.map (fun (cs, (tv, a, b)) ->
            let sign = if isClosedCurve cs tv a b then "\\oint" else "\\int"
            sign + "_{C} " + formTex w + curveTail (cs, (tv, a, b)))
    | "integrate_form", [ w; _; r; ru; rv ] ->
        surf r ru rv |> Option.map (fun s -> "\\iint_{S} " + formTex w + surfTail s)
    | "integrate_change", f :: subs :: (_ :: _ as rs) when rs.Length <= 3 ->
        match allSome (rs |> List.map rangeParts) with
        | None -> None
        | Some rgs ->
            let us = rgs |> List.map (fun (v, _, _) -> LispSym v)
            let n = rgs.Length
            let mul (ps: LispValue list) = LispList (LispSym "*" :: ps)
            let fn (name: string) (a: LispValue) = LispList [ LispSym name; a ]
            let std =
                match subs, us with
                | LispSym "polar", [ r; t ] -> Some [ "x", mul [ r; fn "cos" t ]; "y", mul [ r; fn "sin" t ] ]
                | LispSym "cylindrical", [ r; t; z ] -> Some [ "x", mul [ r; fn "cos" t ]; "y", mul [ r; fn "sin" t ]; "z", z ]
                | LispSym "spherical", [ r; th; ph ] ->
                    Some [ "x", mul [ r; fn "sin" th; fn "cos" ph ]; "y", mul [ r; fn "sin" th; fn "sin" ph ]; "z", mul [ r; fn "cos" th ] ]
                | _ -> None
            let listed =
                match subs with
                | LispList (LispSym "m-vector" :: items) when not items.IsEmpty ->
                    allSome (items |> List.map (function LispList [ LispSym "="; LispSym x; e ] -> Some (x, e) | _ -> None))
                | _ -> None
            match (match std with Some s -> Some s | None -> listed) with
            | Some ss when ss.Length = n ->
                let sign = [| "\\int"; "\\iint"; "\\iiint" |].[n - 1]
                let dif = ss |> List.map (fun (x, _) -> "d" + symbolTex x) |> String.concat "\\,"
                let eqs = ss |> List.map (fun (x, e) -> symbolTex x + " = " + tx e)
                Some (sign + "_{D} " + tex precMul f + "\\," + dif + ",\\quad "
                      + String.concat ",\\ " (eqs @ (rgs |> List.map rng)))
            | _ -> None
    | "integrate_region", [ f; reg ] ->
        region reg |> Option.map (fun d -> "\\iint_{D} " + tex precMul f + "\\,dA,\\quad D:\\ " + d)
    | "green_check", [ p; q; vs; phi; t; reg ] ->
        match vecParts vs, curve phi t, region reg with
        | Some [ LispSym x; LispSym y ], Some c, Some d ->
            let dx, dy = symbolTex x, symbolTex y
            Some ("\\oint_{C} " + tex precAdd p + "\\,d" + dx + " + " + tex precAdd q + "\\,d" + dy
                  + " \\overset{?}{=} \\iint_{D} \\left(\\frac{\\partial}{\\partial " + dx + "}\\left(" + tx q
                  + "\\right) - \\frac{\\partial}{\\partial " + dy + "}\\left(" + tx p + "\\right)\\right) dA"
                  + curveTail c + ",\\ D:\\ " + d)
        | _ -> None
    | "stokes_check", [ f; _; r; ru; rv; phi; t ] ->
        match surf r ru rv, curve phi t with
        | Some s, Some c ->
            Some ("\\oint_{C} \\mathbf{F} \\cdot d\\mathbf{r} \\overset{?}{=} \\iint_{S} (\\nabla \\times \\mathbf{F}) \\cdot d\\mathbf{S},\\quad \\mathbf{F} = "
                  + vecTex f + surfTail s + ",\\ C:\\ " + param (fst c) [ snd c ])
        | _ -> None
    | "gauss_check", f :: _ :: r :: ru :: rv :: (_ :: _ as vol) ->
        let name, rest =
            match vol with
            | LispSym n :: rs when n = "spherical" || n = "cylindrical" -> Some n, rs
            | rs -> None, rs
        match surf r ru rv, allSome (rest |> List.map rangeParts) with
        | Some s, Some rgs when not rgs.IsEmpty ->
            let pre = match name with Some n -> "\\text{" + n + "},\\ " | None -> ""
            Some ("\\iint_{S} \\mathbf{F} \\cdot d\\mathbf{S} \\overset{?}{=} \\iiint_{V} \\nabla \\cdot \\mathbf{F}\\,dV,\\quad \\mathbf{F} = "
                  + vecTex f + surfTail s + ",\\ V:\\ " + pre + String.concat ",\\ " (rgs |> List.map rng))
        | _ -> None
    | _ -> None

// Главная функция: LaTeX для любого значения; неизвестные формы — \text{...} (не ошибка)
let latexPrint (v: LispValue) : string = tex precTop v
