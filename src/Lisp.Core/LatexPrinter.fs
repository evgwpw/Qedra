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

let rec private tex (context: int) (v: LispValue) : string =
    let wrap (text: string) (prec: int) : string =
        if prec < context then "\\left(" + text + "\\right)" else text
    // База степени: атомы и функции — без скобок, всё прочее — в \left(...\right)
    let powBase (b: LispValue) =
        match b with
        | LispInteger _ | LispFloat _ | LispRational _ | LispSym _ -> tex precAtom b
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
            let stripOuterParens (s: string) =
                if s.Length > 13 && s.StartsWith("\\left(") && s.EndsWith("\\right)") then
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
        | "integrate", [e; LispSym x] -> wrap ("\\int " + tex precMul e + "\\,d" + x) precAtom
        | "integrate", [e; LispSym x; a; b] ->
            wrap ("\\int_{" + tex precTop a + "}^{" + tex precTop b + "} " + tex precMul e + "\\,d" + x) precAtom
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
            wrap ("\\operatorname{" + name.Replace("-", "}") + "}\\left(" + String.concat ", " (args |> List.map (tex precTop)) + "\\right)") precAtom
        | _ -> wrap ("\\text{" + escapeText (prettyPrint v) + "}") precAtom
    // REL.1e П5а: результат-список без головы-символа (groebner, eigenvalues) — вектор формул,
    // а не \text{...} с \textasciicircum
    | LispList xs when not xs.IsEmpty ->
        wrap ("\\left[" + (xs |> List.map (tex precTop) |> String.concat ", ") + "\\right]") precAtom
    | _ -> wrap ("\\text{" + escapeText (prettyPrint v) + "}") precAtom

// Главная функция: LaTeX для любого значения; неизвестные формы — \text{...} (не ошибка)
let latexPrint (v: LispValue) : string = tex precTop v
