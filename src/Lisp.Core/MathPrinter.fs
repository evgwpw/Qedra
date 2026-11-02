// Pretty-printer математических выражений в инфиксной записи (Шаг 8a)
// Lisp-дерево → «2x^2 + 3x + 5». Принципы: минимальные скобки по приоритетам,
// детерминированность (без упрощений — только печать).
// Не-математические значения (строки, произвольные списки, функции) — обычный prettyPrint.
module MathPrinter

open System
open Types
open Printer

// --- Приоритеты (больше — сильнее связывает) ---
// Шаг 21: шкала расширена (отношения, множества, логика); относительный порядок прежних уровней не менялся
//   12 — атомы: числа, символы, вызовы функций sin(x), векторы [..], множества {..}
//   11 — постфикс: v[i], n!
//   10 — степень ^ (правоассоциативна: x^y^2 = x^(y^2))
//    9 — унарный минус
//    8 — умножение и деление (и рациональные дроби: 1/3)
//    7 — сложение и вычитание
//    6 — пересечение ∩
//    5 — объединение ∪ и разность \
//    4 — отношения = ≠ < > ≤ ≥ ∈ (не ассоциативны)
//    3 — not
//    2 — and
//    1 — or
//    0 — верхний уровень (скобки не нужны никогда)
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

// Режим входного языка (Шаг 21): булевы true/false, ∞, любые вызовы f(args) для неизвестных имён.
// Без него — прежнее поведение (#t, inf, s-выражение для неизвестных форм): так нужно старым тестам и op "parse".
// Флаг на поток: вложенные math-print (методы объектов: множества, векторы) видят тот же режим
let private langMode = new System.Threading.ThreadLocal<bool>(fun () -> false)
let private lang () : bool = langMode.Value

// Шаг S.5: слово «or» в печати совокупности (x = 2 or x = 3). В шагах по-русски — «или»; по умолчанию — «or»
// (читается обратно парсером). Флаг на поток
let private orWord = new System.Threading.ThreadLocal<string>(fun () -> "or")

// Выполнить f, печатая «or» словом word (прежнее слово восстанавливается)
let withOrWord (word: string) (f: unit -> 'a) : 'a =
    let saved = orWord.Value
    orWord.Value <- word
    try f ()
    finally orWord.Value <- saved

// Имя можно печатать как f(...) и читать обратно парсером
let private isIdent (s: string) : bool =
    s.Length > 0 && (Char.IsLetter s.[0] || s.[0] = '_' || s.[0] = '%')
    && s |> Seq.forall (fun c -> Char.IsLetterOrDigit c || c = '_' || c = '?' || c = '%')

// Шаг S.2: невычисленная производная в шагах — (d/dx u) печатается как d/dx(u) (обратно не читается)
let private isDerivHead (s: string) : bool = s.Length > 3 && s.StartsWith "d/d" && isIdent (s.Substring 3)

// Шаг S.3: невычисленный интеграл в шагах — (int/dx f) печатается «∫ f dx», (int/dx f a b) — «∫_a^b f dx» (обратно не читается)
let private isIntHead (s: string) : bool = s.Length > 5 && s.StartsWith "int/d" && isIdent (s.Substring 5)

// Отношения: тег → печатный знак
let private relationSigns : Map<string, string> =
    Map.ofList [ "=", "="; "/=", "≠"; "!=", "≠"; "<", "<"; ">", ">"; "<=", "≤"; ">=", "≥" ]

// Известные математические функции — печатаются как f(x)
// (полный набор из Builtins.fs: тригонометрия, гиперболические, обратные, exp/log/ln/sqrt/abs)
let private knownFunctions =
    Set.ofList [
        "sin"; "cos"; "tan"; "cot"; "sec"; "csc"
        "sinh"; "cosh"; "tanh"; "coth"; "sech"; "csch"
        "asin"; "acos"; "atan"; "acot"; "asec"; "acsc"
        "asinh"; "acosh"; "atanh"; "acoth"; "asech"; "acsch"
        "exp"; "log"; "ln"; "sqrt"; "abs"
        // Шаг 21l.0: Γ/ψ — известные функции одного аргумента (печатаются греческой головой Γ(x)/ψ(x) — ветка greekHeads)
        "gamma"; "psi"
        // замечание ревью WASM.5): спецфункции остатков Риша — erfi(x), Ei(x)…, а не Lisp-форма в пояснениях
        "erf"; "erfc"; "erfi"; "Ei"; "Si"; "Ci"; "li"; "Shi"; "Chi"
    ]

// A3′.7: эллиптические интегралы Лежандра — EllipticF(φ,k), EllipticE(φ,k), EllipticPi(n,φ,k), EllipticK(k), EllipticEC(k)
let private ellipticFunctions =
    Set.ofList [ "elliptic-f"; "elliptic-e"; "elliptic-pi"; "elliptic-k"; "elliptic-ec" ]

// Функции с несколькими аргументами (Шаг 18) — печатаются f(a, b): solve(x^2 = 4, x)
let private multiArgFunctions =
    // имена без «-», иначе f(a, b) читалось бы как вычитание; Шаг 21: невычисленные integrate/limit и if
    // Шаг 21l.0: binomial печатается C(n, k); rf/ff/harmonic/bernoulli — как f(a, b)
    Set.ofList [ "solve"; "resultant"; "nroots"; "integrate"; "limit"; "if"
                 "rf"; "ff"; "harmonic"; "bernoulli" ]

// Печать головы символом (Шаг 21l.0): Γ(x), ψ(x), ψ(x, m)
let private greekHeads : Map<string, string> =
    Map.ofList [ "gamma", "Γ"; "psi", "ψ" ]

// SFn.2a: головы Бесселя, Эри, Лежандра — BesselJ(ν, x), AiryAi(x), LegendreP(n, x)
let private sfHeads : Map<string, string> =
    Map.ofList [ "bessel-j", "BesselJ"; "bessel-y", "BesselY"; "bessel-i", "BesselI"; "bessel-k", "BesselK"
                 "airy-ai", "AiryAi"; "airy-bi", "AiryBi"
                 "airy-ai-prime", "AiryAiPrime"; "airy-bi-prime", "AiryBiPrime"
                 "legendre-p", "LegendreP"; "legendre-q", "LegendreQ" ]

// Проверка: значение — математическое выражение?
// Числа, символы, арифметические цепочки и известные функции.
// Всё прочее (строки, булевы, произвольные списки, функции) — НЕ математика
let rec isMathValue (v: LispValue) : bool =
    match v with
    | LispInteger _ | LispFloat _ | LispRational _ | LispSym _ -> true
    | LispComplex (re, im) -> isMathValue re && isMathValue im
    // Шаг 14: объекты печатаются собственными методами, внутри выражений — как атомы
    | LispObject _ -> true
    // Шаг 21: в языке булевы значения, строки и алгебраические числа — значения как все остальные
    | LispBool _ | LispStr _ | LispAlgebraic _ -> lang ()
    | LispList (LispSym op :: args) ->
        let all () = List.forall isMathValue args
        match op, args with
        | ("+" | "-" | "*" | "/"), _ -> all ()
        | "^", [bse; ex] -> isMathValue bse && isMathValue ex
        | rel, [_; _] when Map.containsKey rel relationSigns -> all ()
        // Шаг 21: логика, принадлежность, декларации, присваивания, векторы, множества, индексы, факториал
        | ("and" | "or"), _ :: _ :: _ -> all ()
        | "not", [_] -> all ()
        | (":in" | ":declare"), [_; _] -> all ()
        | ":=", [LispSym _] -> true
        | ":declare", [LispSym _] -> true      // Шаг 21c: «x :∈» — снять декларации
        | ":=", [LispSym _; rhs] -> isMathValue rhs
        // Шаг 21a: присваивание элементу v[i] := e
        | ":=", [LispList (LispSym "m-index" :: _ :: _ :: _) as lhs; rhs] -> isMathValue lhs && isMathValue rhs
        // параметры функции — имена или name := значение_по_умолчанию (Шаг 21a)
        | ":=", [LispList (LispSym _ :: ps); rhs] ->
            ps |> List.forall (function
                               | LispSym _ -> true
                               | LispList [LispSym ":="; LispSym _; d] -> isMathValue d
                               | _ -> false) && isMathValue rhs
        | ("m-vector" | "m-set"), _ -> all ()
        | "m-index", _ :: _ :: _ -> all ()
        | "factorial", [_] -> all ()
        | "binomial", [_; _] -> all ()
        // Шаг 21l.0: Γ(x) — функция с символьной головой; euler-gamma — константа
        | "euler-gamma", [] -> true
        | ("union" | "intersection" | "set-difference"), _ :: _ :: _ -> all ()
        | name, _ :: _ when Set.contains name multiArgFunctions -> all ()
        | name, _ :: _ when Map.containsKey name sfHeads -> all ()
        | name, [arg] when isDerivHead name -> isMathValue arg
        | name, ([_] | [_; _; _]) when isIntHead name -> all ()
        // Шаг 21h: сумма по корням (root-sum t Q E) печатается rootsum(E, t, Q)
        | "root-sum", [LispSym _; q; e] -> isMathValue q && isMathValue e
        // WASM.6a Д1: запись ОДУ (ode-solution :solutions ((= (y x) rhs)) …) — ответ как уравнения,
        // иначе во входном языке печаталась служебная Lisp-форма
        | "ode-solution", _ :: _ -> true
        // Q.2: (piecewise ((условие ответ) …)) — математическая форма
        | "piecewise", [LispList branches] ->
            branches |> List.forall (fun b ->
                match b with
                | LispList [c; e] -> isMathValue c && isMathValue e
                | _ -> false)
        // Шаг 21l.5: рекуррентность — математическая форма
        | "recurrence", [LispSym _; LispSym _; LispList cs; rhs; LispList init] ->
            isMathValue rhs && cs |> List.forall isMathValue
            && init |> List.forall (fun p -> match p with LispList [_; v] -> isMathValue v | _ -> false)
        | name, [arg] when Set.contains name knownFunctions -> isMathValue arg
        // A3′.7: эллиптические головы — математические формы
        | name, _ :: _ when Set.contains name ellipticFunctions -> all ()
        // Шаг 21l.0: Γ/ψ с несколькими аргументами (ψ(x, m)) — тоже математика
        | ("gamma" | "psi"), _ -> all ()
        // язык: любое имя-идентификатор — вызов f(args) (в том числе f() без аргументов)
        | name, _ when lang () && isIdent name -> all ()
        | _ -> false
    | _ -> false

// Правый операнд бинарной операции: если текст начинается с «-», берём в скобки —
// иначе «a - -b», «a/-x», «x^-2» читаются неоднозначно
let private negativeSafe (text: string) : string =
    if text.StartsWith("-") then "(" + text + ")" else text

// Унарный минус: операнд, начинающийся с «-», — в скобки: -(-2), -(-x)
let private unaryText (operand: string) : string =
    if operand.StartsWith("-") then "-(" + operand + ")" else "-" + operand

// Соединение множителей — правила НЕЯВНОГО умножения (когда «*» можно опустить):
//   - правый множитель начинается с «(» и левый — число или закрывающая скобка: 3(x + 1), (x + 1)(y + 2)
//   - правый начинается с буквы, а левый — целое число без знака: 2x, 2x^2, 3sin(x)
// В остальных случаях — явная «*»:
//   - символ перед «(»: x*(x + 1) — иначе MathReader читает «x(…)» как вызов (WASM.5b)
//   - между числами: 2*3 (иначе «23»), между символами: x*y (иначе «xy» — как одно имя)
//   - рациональный множитель: 1/3*x^3 — выбран явный «*», т.к. «1/3x^3» читалось бы как 1/(3x)
//   - перед унарным минусом — со скобками: 2*(-x)
let private joinFactors (left: string) (right: string) : string =
    if right.StartsWith("(") then
        let leftIsNumberOrParen =
            left.Length > 0 && (left.[left.Length - 1] = ')' || Char.IsDigit left.[left.Length - 1])
        if leftIsNumberOrParen then left + right else left + "*" + right
    elif right.Length > 0 && (Char.IsLetter right.[0] || right.[0] = '%')
         && left.Length > 0 && left |> Seq.forall (fun c -> Char.IsDigit c) then left + right
    elif right.StartsWith("-") then left + "*(" + right + ")"
    else left + "*" + right

// --- Каноническая форма Шага 13: вычитание и деление печатаем по-человечески ---
//   (+ x (* -1 y)) → x - y;  (* -1 x) → -x;  (* x (^ y -1)) → x/y;  (^ x -1) → 1/x
//   Рациональный коэффициент остаётся явным множителем: 1/2*x (так он читается обратно MathReader)

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

// Терм суммы с отрицательным числовым коэффициентом → тот же терм с положительным
// ((* -1 y) → y; (* -2 x y) → (* 2 x y)); иначе None
let private positiveTerm (t: LispValue) : LispValue option =
    match t with
    | LispList (LispSym "*" :: c :: rest) when isNegReal c && not rest.IsEmpty ->
        let pc = negReal c
        let isOneC = (match pc with LispInteger n -> n.IsOne | _ -> false)
        if isOneC then
            (match rest with [single] -> Some single | _ -> Some (LispList (LispSym "*" :: rest)))
        else Some (LispList (LispSym "*" :: pc :: rest))
    | _ -> None

// Множитель со степенью с отрицательным числовым показателем → знаменатель: (^ y -2) → y^2
let private denominatorOf (f: LispValue) : LispValue option =
    match f with
    | LispList [LispSym "^"; b; n] when isNegReal n ->
        let pn = negReal n
        (match pn with
         | LispInteger one when one.IsOne -> Some b
         | _ -> Some (LispList [LispSym "^"; b; pn]))
    | _ -> None

// Печать подвыражения в заданном контексте: context — минимальный приоритет,
// при котором скобки ещё не нужны; собственный приоритет ниже — оборачиваем
let rec private printExpr (context: int) (v: LispValue) : string =
    let wrap (text: string) (prec: int) : string =
        if prec < context then "(" + text + ")" else text
    match v with
    // --- Атомы ---
    | LispInteger n -> wrap (string n) precAtom
    | LispFloat f ->
        // Шаг 21a: целое дробное печатается с «.0» (1.0, а не 1), иначе при чтении получилось бы точное целое
        let s = string f
        let s = if lang () && Seq.forall (fun c -> Char.IsDigit c || c = '-') s then s + ".0" else s
        wrap s precAtom
    // Рациональная дробь «1/3» — приоритет деления: в сумме без скобок (1/3 + x),
    // в показателе степени — со скобками (x^(1/2))
    | LispRational (p, q) -> wrap (string p + "/" + string q) precMul
    // Шаг 21 (режим языка): бесконечности ∞ / -∞ (символы inf и -inf), булевы true/false
    | LispSym "inf" when lang () -> wrap "∞" precAtom
    | LispSym "-inf" when lang () -> wrap "-∞" precUnary
    | LispBool b when lang () -> wrap (if b then "true" else "false") precAtom
    | LispSym s -> wrap s precAtom
    // Комплексное число содержит «+» внутри («2 + 3i») — приоритет суммы
    | LispComplex _ -> wrap (prettyPrint v) precAdd
    // Объект: метод (math-print type) возвращает строку; иначе как prettyPrint (метод print или #<type ...>)
    | LispObject o ->
        match Objects.findMethod "math-print" [o.Type] with
        | Some fn ->
            match Objects.applyHook fn [v] with
            | LispStr s -> wrap s precAtom
            | other -> wrap (prettyPrint other) precAtom
        | None -> wrap (prettyPrint v) precAtom
    // --- Операции ---
    | LispList (LispSym op :: args) ->
        match op, args with
        // Сумма: цепочка «a + b + c», левоассоциативная:
        // вложенная сумма слева — без скобок (a + b + c), справа — со скобками (a + (b + c))
        | "+", [] -> wrap (prettyPrint v) precAtom
        | "+", [single] -> printExpr context single
        | "+", first :: rest ->
            // термы с отрицательным числовым коэффициентом (не первые) — через « - »: x - y
            let restText =
                rest |> List.map (fun a ->
                    match positiveTerm a with
                    | Some pos -> " - " + printExpr (precAdd + 1) pos
                    | None -> " + " + negativeSafe (printExpr (precAdd + 1) a))
            wrap (printExpr precAdd first + String.concat "" restText) precAdd
        // Унарный минус: канонические формы проекта (- x) и (- 0 x)
        | "-", [] -> wrap (prettyPrint v) precAtom
        | "-", [single] -> wrap (unaryText (printExpr precUnary single)) precUnary
        | "-", [LispInteger z; single] when z.IsZero ->
            wrap (unaryText (printExpr precUnary single)) precUnary
        // Цепочка вычитаний: a - b - c (левоассоциативная)
        | "-", first :: rest ->
            let parts =
                printExpr precAdd first
                :: (rest |> List.map (fun a -> negativeSafe (printExpr (precAdd + 1) a)))
            wrap (String.concat " - " parts) precAdd
        // Произведение: множители в контексте умножения, соединяем неявным умножением
        | "*", [] -> wrap (prettyPrint v) precAtom
        | "*", [single] -> printExpr context single
        | "*", _ ->
            // коэффициент -1 → унарный минус; множители с отрицательным показателем → знаменатель
            // при наличии знаменателя рациональный коэффициент p/q → p в числителе, q в знаменателе:
            // (* 1/2 x (^ y -1)) → x/(2y)
            let hasDenom = args |> List.exists (fun a -> (denominatorOf a).IsSome)
            let argsR, extraDen =
                match args with
                | LispRational (p, q) :: rest when hasDenom -> (if p.IsOne then rest else LispInteger p :: rest), [LispInteger q]
                | _ -> args, []
            let neg, args' =
                match argsR with
                | LispInteger m :: (_ :: _ as rest) when m = -1I -> true, rest
                | _ -> false, argsR
            let numer = args' |> List.filter (fun a -> (denominatorOf a).IsNone)
            let denom = extraDen @ (args' |> List.choose denominatorOf)
            let joinText (fs: LispValue list) =
                fs |> List.map (fun a -> printExpr precMul a) |> List.reduce joinFactors
            let body =
                if denom.IsEmpty then joinText numer
                else
                    let numText = if numer.IsEmpty then "1" else joinText numer
                    let denText =
                        match denom with
                        | [one] -> negativeSafe (printExpr (precMul + 1) one)
                        | _ -> "(" + joinText denom + ")"
                    numText + "/" + denText
            if neg then wrap (unaryText body) precUnary else wrap body precMul
        // Степень с отрицательным числовым показателем: x^-1 → 1/x, x^-2 → 1/x^2
        | "^", [bse; ex] when (denominatorOf v).IsSome ->
            wrap ("1/" + negativeSafe (printExpr (precMul + 1) (denominatorOf v).Value)) precMul
        // Унарное деление: (/ x) = 1/x
        | "/", [] -> wrap (prettyPrint v) precAtom
        | "/", [single] ->
            wrap ("1/" + negativeSafe (printExpr (precMul + 1) single)) precMul
        // Цепочка делений: a/b/c (левоассоциативная — правые операнды выше контекстом)
        | "/", first :: rest ->
            let parts =
                printExpr precMul first
                :: (rest |> List.map (fun a -> negativeSafe (printExpr (precMul + 1) a)))
            wrap (String.concat "/" parts) precMul
        // Степень: правоассоциативна (x^y^2 = x^(y^2)).
        // База — в скобках всем, кроме атомов и функций: (x + 1)^2, (2x)^2, но x^2 и sin(x)^2
        | "^", [bse; ex] ->
            let baseText = negativeSafe (printExpr precAtom bse)
            let expText = negativeSafe (printExpr precPow ex)
            wrap (baseText + "^" + expText) precPow
        // Шаг 18: равенство a = b (внутри любой операции — в скобках); Шаг 21: все отношения — один уровень precRel
        | rel, [l; r] when Map.containsKey rel relationSigns ->
            wrap (printExpr precSetU l + " " + relationSigns.[rel] + " " + printExpr precSetU r) precRel
        // --- Шаг 21: конструкции входного языка ---
        | "and", _ :: _ :: _ ->
            wrap (String.concat " and " (args |> List.map (printExpr (precAnd + 1)))) precAnd
        | "or", _ :: _ :: _ ->
            wrap (String.concat (" " + orWord.Value + " ") (args |> List.map (printExpr (precOr + 1)))) precOr
        | "not", [a] -> wrap ("not " + printExpr precNot a) precNot
        | ":in", [x; d] -> wrap (printExpr precSetU x + " ∈ " + printExpr precSetU d) precRel
        | ":declare", [x; d] -> wrap (printExpr precTop x + " :∈ " + printExpr precTop d) precTop
        | ":=", [LispSym n] -> wrap (n + " :=") precTop
        | ":declare", [LispSym n] -> wrap (n + " :∈") precTop
        | ":=", [lhs; rhs] ->
            let lhsText =
                match lhs with
                | LispList (LispSym f :: ps) when f <> "m-index" -> f + "("+ String.concat ", " (ps |> List.map (printExpr precTop)) + ")"
                | other -> printExpr precTop other
            wrap (lhsText + " := " + printExpr precTop rhs) precTop
        | "m-vector", _ -> wrap ("[" + String.concat ", " (args |> List.map (printExpr precTop)) + "]") precAtom
        | "m-set", _ -> wrap ("{" + String.concat ", " (args |> List.map (printExpr precTop)) + "}") precAtom
        | "m-index", bse :: idx ->
            wrap (printExpr precPostfix bse + "[" + String.concat ", " (idx |> List.map (printExpr precTop)) + "]") precPostfix
        | "factorial", [a] -> wrap (printExpr precPostfix a + "!") precPostfix
        // Шаг 21l.0: биномиальный коэффициент C(n, k); Γ/ψ — греческая голова
        | "binomial", [n; k] -> wrap ("C(" + printExpr precTop n + ", " + printExpr precTop k + ")") precAtom
        | "euler-gamma", [] -> wrap "γ" precAtom
        | name, args when Map.containsKey name greekHeads ->
            wrap (greekHeads.[name] + "(" + String.concat ", " (args |> List.map (printExpr precTop)) + ")") precAtom
        | "union", _ :: _ :: _ | "set-difference", _ :: _ :: _ ->
            let sep = if op = "union" then " ∪ " else " \\ "
            wrap (printExpr precSetU args.Head + String.concat "" (args.Tail |> List.map (fun a -> sep + printExpr (precSetU + 1) a))) precSetU
        | "intersection", _ :: _ :: _ ->
            wrap (printExpr precSetI args.Head + String.concat "" (args.Tail |> List.map (fun a -> " ∩ " + printExpr (precSetI + 1) a))) precSetI
        | name, _ :: _ when Set.contains name multiArgFunctions ->
            wrap (name + "(" + String.concat ", " (args |> List.map (printExpr precTop)) + ")") precAtom
        | name, _ :: _ when Map.containsKey name sfHeads ->
            wrap (sfHeads.[name] + "(" + String.concat ", " (args |> List.map (printExpr precTop)) + ")") precAtom
        | name, [arg] when isDerivHead name ->
            wrap (name + "(" + printExpr precTop arg + ")") precAtom
        | name, ([_] | [_; _; _]) when isIntHead name ->
            let bound (t: LispValue) =
                let s = printExpr precTop t
                if s |> Seq.forall (fun c -> Char.IsLetterOrDigit c || c = '∞') then s else "(" + s + ")"
            let body = printExpr precMul args.Head
            let dv = " d" + name.Substring 5
            match args with
            | [_; a; b] -> wrap ("∫_" + bound a + "^" + bound b + " " + body + dv) precAtom
            | _ -> wrap ("∫ " + body + dv) precAtom
        // Шаг 21h: (root-sum t Q E) — сумма E по корням t многочлена Q: rootsum(E, t, Q) (читается обратно MathReader)
        | "root-sum", [LispSym tv; q; e] ->
            wrap ("rootsum(" + printExpr precTop e + ", " + tv + ", " + printExpr precTop q + ")") precAtom
        // WASM.6a Д1: ответ ОДУ — уравнения y(x) = … (общее и особые через «or»); статус не ok — «unknown»
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
            let text =
                if not eqs.IsEmpty then
                    eqs |> List.map (printExpr precTop) |> String.concat (" " + orWord.Value + " ")
                else "unknown"
            wrap text precTop
        // Q.2: (piecewise ((условие ответ) …)) — piecewise((условие, ответ), …) (читается обратно MathReader)
        | "piecewise", [LispList branches] ->
            let one (b: LispValue) =
                match b with
                | LispList [c; e] -> "(" + printExpr precTop c + ", " + printExpr precTop e + ")"
                | _ -> "(" + printExpr precTop b + ")"
            wrap ("piecewise(" + String.concat ", " (branches |> List.map one) + ")") precAtom
        // Шаг 21l.5: (recurrence S n (a0…aJ) rhs init) — рекуррентность:
        // a0·S(n) + a1·S(n+1) + … + aJ·S(n+J) = rhs, S(n0)=v0, …
        | "recurrence", [LispSym s; LispSym nv; LispList coeffs; rhs; LispList init] ->
            let term j a =
                match j with
                | 0 -> "(" + printExpr precMul a + ")·" + s + "(" + nv + ")"
                | _ -> "(" + printExpr precMul a + ")·" + s + "(" + nv + "+" + string j + ")"
            let eq =
                coeffs |> List.mapi (fun j a -> term j a) |> String.concat " + "
                |> fun l -> l + " = " + printExpr precTop rhs
            let inits =
                init |> List.map (fun p ->
                    match p with
                    | LispList [LispInteger m; v] -> s + "(" + string m + ") = " + printExpr precTop v
                    | _ -> prettyPrint p)
                |> String.concat ", "
            let body = if inits = "" then eq else eq + ", " + inits
            wrap ("recurrence(" + body + ")") precAtom
        // A3′.7: эллиптические интегралы Лежандра — EllipticF(φ,k), EllipticE(φ,k), EllipticPi(n,φ,k), EllipticK(k)
        | "elliptic-f", [phi; k] ->
            wrap ("EllipticF(" + printExpr precTop phi + ", " + printExpr precTop k + ")") precAtom
        | "elliptic-e", [phi; k] ->
            wrap ("EllipticE(" + printExpr precTop phi + ", " + printExpr precTop k + ")") precAtom
        | "elliptic-e", [k] -> wrap ("EllipticE(" + printExpr precTop k + ")") precAtom
        | "elliptic-k", [k] -> wrap ("EllipticK(" + printExpr precTop k + ")") precAtom
        | "elliptic-ec", [k] -> wrap ("EllipticEC(" + printExpr precTop k + ")") precAtom
        | "elliptic-pi", [n; phi; k] ->
            wrap ("EllipticPi(" + printExpr precTop n + ", " + printExpr precTop phi + ", " + printExpr precTop k + ")") precAtom
        // Известная функция: sin(x); аргумент — внутри скобок функции, без лишних
        | name, [arg] when Set.contains name knownFunctions ->
            wrap (name + "(" + printExpr precTop arg + ")") precAtom
        // Режим языка: любой вызов f(a, b) (неизвестная функция остаётся невычисленной формой)
        | name, _ when lang () && isIdent name ->
            wrap (name + "(" + String.concat ", " (args |> List.map (printExpr precTop)) + ")") precAtom
        // Не-математическая форма — обычный s-выраженческий вывод (defensive)
        | _ -> wrap (prettyPrint v) precAtom
    // REL.1e: список пар (p e) — разложение factorint: p^e, при e = 1 степень не печатается
    | LispList ps when not ps.IsEmpty
        && (ps |> List.forall (function LispList [LispInteger _; LispInteger _] -> true | _ -> false)) ->
        let one = function
            | LispList [LispInteger p; LispInteger e] -> if e = 1I then string p else string p + "^" + string e
            | _ -> ""
        wrap (ps |> List.map one |> String.concat "·") precMul
    // Не-математические значения (строки, булевы, функции...) — defensive
    | _ -> wrap (prettyPrint v) precAtom

// Главная функция: математическое выражение → инфиксная запись,
// всё остальное — обычный prettyPrint (s-выражение)
let mathPrint (v: LispValue) : string =
    if isMathValue v then printExpr precTop v
    else prettyPrint v

// Шаг 21: печать в синтаксисе входного языка — true/false, ∞, вызовы f(args) любых имён, строки.
// Результат читается обратно mathParseProgram (round-trip). Режим действует и на вложенные math-print
let mathPrintLang (v: LispValue) : string =
    let saved = langMode.Value
    langMode.Value <- true
    try mathPrint v
    finally langMode.Value <- saved