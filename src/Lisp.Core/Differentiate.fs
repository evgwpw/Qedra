// Символьное дифференциание (CAS-примитив)
// (diff 'x expr) → производная expr по переменной x
// Поддерживает: +, -, *, /, ^, а также полный набор
// тригонометрических, гиперболических, обратных триг. и обратных гип. функций
module Differentiate

open System.Numerics
open Types
open Numeric
open Simplify

// Вспомогательное: создать LispList
let private lst (items: LispValue list) : LispValue = LispList items

// Вспомогательное: создать бинарную операцию
let private binop (op: string) (a: LispValue) (b: LispValue) : LispValue =
    lst [LispSym op; a; b]

// Вспомогательное: создать числовую константу
let private num (n: int) : LispValue = LispInteger (bigint n)

// Вспомогательное: применить функцию к u, не вычисляя
let private f (name: string) (u: LispValue) : LispValue = lst [LispSym name; u]

// Подстановка выражения вместо символа (структурная; для правила Лейбница)
let rec private substSym (name: string) (value: LispValue) (e: LispValue) : LispValue =
    match e with
    | LispSym s when s = name -> value
    | LispList items -> LispList (List.map (substSym name value) items)
    | _ -> e

// --- Шаг S.2: шаги дифференцирования (журнал StepLog; при выключенном журнале — одна проверка признака на узел) ---
// Шаг на каждое применённое правило: before — невычисленная производная d/dx(u) (символ-голова «d/dx» печатается как
// d/dx(u)), after — её упрощённое значение. Неизвестные функции и интегралы шагов не пишут

// Зависит ли выражение от переменной x
let rec private mentions (x: string) (e: LispValue) : bool =
    match e with
    | LispSym s -> s = x
    | LispList items -> List.exists (mentions x) items
    | LispVector items -> Array.exists (mentions x) items
    | _ -> false

// Листья, которые родитель просит не записывать (константа-множитель, переменная в основании степени и т. п.):
// глубина рамки родителя; 0 — нет. По потокам: алгебра тестируется параллельно
[<Sealed; AbstractClass>]
type private DiffState private () =
    [<System.ThreadStatic; DefaultValue>]
    static val mutable private quietDepth : int
    static member QuietDepth
        with get () : int = DiffState.quietDepth
        and set (v: int) = DiffState.quietDepth <- v

// Выполнить f с отключённым журналом (внутренние вычисления для «после» шагов не должны писать шаги)
let private quietly (f: unit -> 'a) : 'a =
    let was = StepLog.Journal.Enabled
    StepLog.Journal.Enabled <- false
    try f ()
    finally StepLog.Journal.Enabled <- was

// Производная d/dv(e) как невычисленное выражение (для before шагов)
let private dOf (v: string) (e: LispValue) : obj = box (LispList [LispSym ("d/d" + v); e])

// Правила функций одного аргумента: (rule, заголовок, вид f(u), производная f'(u)); {u} — место аргумента
let private funcRule (op: string) : (string * string * string * string) option =
    let trig = "Производная тригонометрической функции"
    let hyp = "Производная гиперболической функции"
    let itrig = "Производная обратной тригонометрической функции"
    let ihyp = "Производная обратной гиперболической функции"
    match op with
    | "sin" -> Some ("diff-trig", trig, "sin({u})", "cos({u})")
    | "cos" -> Some ("diff-trig", trig, "cos({u})", "−sin({u})")
    | "tan" -> Some ("diff-trig", trig, "tan({u})", "1/cos²{u}")
    | "cot" -> Some ("diff-trig", trig, "cot({u})", "−1/sin²{u}")
    | "sec" -> Some ("diff-trig", trig, "sec({u})", "sec({u})·tan({u})")
    | "csc" -> Some ("diff-trig", trig, "csc({u})", "−csc({u})·cot({u})")
    | "sinh" -> Some ("diff-hyperbolic", hyp, "sinh({u})", "cosh({u})")
    | "cosh" -> Some ("diff-hyperbolic", hyp, "cosh({u})", "sinh({u})")
    | "tanh" -> Some ("diff-hyperbolic", hyp, "tanh({u})", "sech²{u}")
    | "coth" -> Some ("diff-hyperbolic", hyp, "coth({u})", "−csch²{u}")
    | "sech" -> Some ("diff-hyperbolic", hyp, "sech({u})", "−sech({u})·tanh({u})")
    | "csch" -> Some ("diff-hyperbolic", hyp, "csch({u})", "−csch({u})·coth({u})")
    | "asin" -> Some ("diff-inverse-trig", itrig, "asin({u})", "1/√(1−{u}²)")
    | "acos" -> Some ("diff-inverse-trig", itrig, "acos({u})", "−1/√(1−{u}²)")
    | "atan" -> Some ("diff-inverse-trig", itrig, "atan({u})", "1/(1+{u}²)")
    | "acot" -> Some ("diff-inverse-trig", itrig, "acot({u})", "−1/(1+{u}²)")
    | "asec" -> Some ("diff-inverse-trig", itrig, "asec({u})", "1/({u}·√({u}²−1))")
    | "acsc" -> Some ("diff-inverse-trig", itrig, "acsc({u})", "−1/({u}·√({u}²−1))")
    | "asinh" -> Some ("diff-inverse-hyperbolic", ihyp, "asinh({u})", "1/√({u}²+1)")
    | "acosh" -> Some ("diff-inverse-hyperbolic", ihyp, "acosh({u})", "1/√({u}²−1)")
    | "atanh" -> Some ("diff-inverse-hyperbolic", ihyp, "atanh({u})", "1/(1−{u}²)")
    | "acoth" -> Some ("diff-inverse-hyperbolic", ihyp, "acoth({u})", "1/(1−{u}²)")
    | "asech" -> Some ("diff-inverse-hyperbolic", ihyp, "asech({u})", "−1/({u}·√(1−{u}²))")
    | "acsch" -> Some ("diff-inverse-hyperbolic", ihyp, "acsch({u})", "−1/({u}·√(1+{u}²))")
    | "exp" -> Some ("diff-exp", "Производная экспоненты", "e^{u}", "e^{u}")
    | "log" | "ln" -> Some ("diff-log", "Производная логарифма", "ln({u})", "1/{u}")
    | "sqrt" -> Some ("diff-sqrt", "Производная квадратного корня", "√{u}", "1/(2√{u})")
    | "abs" -> Some ("diff-abs", "Производная модуля", "|{u}|", "sign({u})")
    // Шаг 21k.6′: специальные функции (остатки неэлементарных интегралов, risch-special)
    | "erf" -> Some ("diff-special", "Производная специальной функции", "erf({u})", "2/√π·e^(−{u}²)")
    | "erfc" -> Some ("diff-special", "Производная специальной функции", "erfc({u})", "−2/√π·e^(−{u}²)")
    | "erfi" -> Some ("diff-special", "Производная специальной функции", "erfi({u})", "2/√π·e^({u}²)")
    | "Ei" -> Some ("diff-special", "Производная специальной функции", "Ei({u})", "e^{u}/{u}")
    | "li" -> Some ("diff-special", "Производная специальной функции", "li({u})", "1/ln({u})")
    | "Si" -> Some ("diff-special", "Производная специальной функции", "Si({u})", "sin({u})/{u}")
    | "Ci" -> Some ("diff-special", "Производная специальной функции", "Ci({u})", "cos({u})/{u}")
    | "Shi" -> Some ("diff-special", "Производная специальной функции", "Shi({u})", "sinh({u})/{u}")
    | "Chi" -> Some ("diff-special", "Производная специальной функции", "Chi({u})", "cosh({u})/{u}")
    // Шаг 21l.0: комбинаторные головы
    | "gamma" -> Some ("diff-special", "Производная специальной функции", "Γ({u})", "Γ({u})·ψ({u})")
    | "psi" -> Some ("diff-special", "Производная специальной функции", "ψ({u})", "ψ({u}, 1)")
    | "harmonic" -> Some ("diff-special", "Производная специальной функции", "H({u})", "ψ({u} + 1) + γ")
    // SFn.2a: Бессель, Эйри, Лежандр
    | "bessel-j" -> Some ("diff-special", "Производная специальной функции", "J_ν({u})", "½(J_{ν−1}({u}) − J_{ν+1}({u}))")
    | "bessel-y" -> Some ("diff-special", "Производная специальной функции", "Y_ν({u})", "½(Y_{ν−1}({u}) − Y_{ν+1}({u}))")
    | "bessel-i" -> Some ("diff-special", "Производная специальной функции", "I_ν({u})", "½(I_{ν−1}({u}) + I_{ν+1}({u}))")
    | "bessel-k" -> Some ("diff-special", "Производная специальной функции", "K_ν({u})", "−½(K_{ν−1}({u}) + K_{ν+1}({u}))")
    | "airy-ai" -> Some ("diff-special", "Производная специальной функции", "Ai({u})", "Ai′({u})")
    | "airy-bi" -> Some ("diff-special", "Производная специальной функции", "Bi({u})", "Bi′({u})")
    | "airy-ai-prime" -> Some ("diff-special", "Производная специальной функции", "Ai′({u})", "{u}·Ai({u})")
    | "airy-bi-prime" -> Some ("diff-special", "Производная специальной функции", "Bi′({u})", "{u}·Bi({u})")
    | "legendre-p" -> Some ("diff-special", "Производная специальной функции", "P_n({u})", "n({u}·P_n({u}) − P_{n−1}({u}))/({u}²−1)")
    | "legendre-q" -> Some ("diff-special", "Производная специальной функции", "Q_n({u})", "n({u}·Q_n({u}) − Q_{n−1}({u}))/({u}²−1)")
    | _ -> None

// Правило для узла (op args): (rule, заголовок, формула с {u}, внутренняя функция u для цепного правила).
// None — шаг не пишется (неизвестная функция, интеграл, сумма по корням, одноэлементное произведение)
let private classify (x: string) (op: string) (args: LispValue list)
    : (string * string * string * LispValue option) option =
    let isX u = (match u with LispSym s -> s = x | _ -> false)
    let sumTitle = "Производная суммы"
    let constMul = "Вынесение постоянного множителя"
    match op, args with
    | "+", _ :: _ :: _ -> Some ("diff-sum", sumTitle, "(u + v)' = u' + v'", None)
    | "-", [_] -> Some ("diff-constant-multiple", constMul, "(−u)' = −u'", None)
    | "-", _ :: _ :: _ -> Some ("diff-sum", "Производная разности", "(u − v)' = u' − v'", None)
    | "*", _ :: _ :: _ ->
        if (args |> List.filter (mentions x)).Length = 1 then Some ("diff-constant-multiple", constMul, "(c·u)' = c·u'", None)
        else Some ("diff-product", "Правило произведения", "(u·v)' = u'·v + u·v'", None)
    | "/", [_; b] ->
        if not (mentions x b) then Some ("diff-constant-multiple", constMul, "(u/c)' = u'/c", None)
        else Some ("diff-quotient", "Правило частного", "(u/v)' = (u'·v − u·v')/v²", None)
    | "/", [_] -> Some ("diff-quotient", "Правило частного", "(1/u)' = −u'/u²", None)
    | "^", [b; e] ->
        if isNumber e then Some ("diff-power", "Производная степенной функции", "({u}^n)' = n·{u}^(n−1)", (if isX b then None else Some b))
        elif not (mentions x b) then Some ("diff-exp", "Производная показательной функции", "(a^u)' = a^u·ln a·u'", None)
        else Some ("diff-power-general", "Производная показательно-степенной функции", "(u^v)' = u^v·(v'·ln u + v·u'/u)", None)
    | _, [u] ->
        funcRule op |> Option.map (fun (id, title, fu, dfu) ->
            id, title, sprintf "(%s)' = %s" fu dfu, (if isX u then None else Some u))
    // SFn.2a: двухместные головы Бесселя/Лежандра (порядок ν — параметр, производная по аргументу)
    | ("bessel-j" | "bessel-y" | "bessel-i" | "bessel-k" | "legendre-p" | "legendre-q"), [_; _] ->
        funcRule op |> Option.map (fun (id, title, fu, dfu) ->
            id, title, sprintf "(%s)' = %s" fu dfu, None)
    | _ -> None

// Имя формальной переменной для внешней функции в цепном правиле: свободное в выражении и отличное от x
let private formalVar (x: string) (e: LispValue) : string =
    [ "u"; "v"; "w"; "t"; "s" ] |> List.tryFind (fun n -> n <> x && not (mentions n e)) |> Option.defaultValue "u1"

// Основная функция дифференцирования: d/dx(expr). Журнал выключен — прямое вычисление
let rec private diffRaw (x: string) (expr: LispValue) : LispValue =
    if StepLog.Journal.Enabled then diffTraced x expr else diffCore x expr

// То же с записью шагов (журнал включён): рамка на узел-правило, листья — шаги detail
and private diffTraced (x: string) (expr: LispValue) : LispValue =
    let leaf (rule: string) (title: string) (comment: string) (result: LispValue) : LispValue =
        let q = DiffState.QuietDepth
        if not (q > 0 && q = StepLog.Journal.Depth) then
            StepLog.Journal.Record(rule, title, comment, dOf x expr, box result, StepLog.Detail)
        result
    match expr with
    | LispSym name when name = x -> leaf "diff-variable" "Производная переменной" (sprintf "(%s)' = 1" x) (num 1)
    | LispSym _ | LispInteger _ | LispRational _ | LispFloat _ | LispComplex _ ->
        leaf "diff-constant" "Производная постоянной" "(c)' = 0" (num 0)
    | LispList (LispSym op :: args) ->
        if not (mentions x expr) then leaf "diff-constant" "Производная постоянной" "(c)' = 0" (num 0)
        else
            match classify x op args with
            | None -> diffCore x expr
            | Some (id, title, formula, inner) ->
                let before = dOf x expr
                let finish (comment: string) (r: LispValue) = Some (comment, box (quietly (fun () -> simplify r)))
                match inner with
                | None ->
                    // листья родителя молчат там, где их производная очевидна из формулы
                    let quiet = id = "diff-constant-multiple" || id = "diff-power" || (funcRule op).IsSome
                    let run () =
                        if quiet then
                            let prev = DiffState.QuietDepth
                            DiffState.QuietDepth <- StepLog.Journal.Depth
                            try diffCore x expr
                            finally DiffState.QuietDepth <- prev
                        else diffCore x expr
                    StepLog.Journal.Within(id, title, before, StepLog.Main, run, finish (formula.Replace("{u}", x)))
                | Some _ ->
                    // сложная функция: внешняя производная по формальной переменной, затем внутренняя
                    let t = formalVar x expr
                    let outerExpr =
                        match op, args with
                        | "^", [_; e] -> lst [LispSym "^"; LispSym t; e]
                        | _ -> lst [LispSym op; LispSym t]
                    let run () =
                        let outerD = quietly (fun () -> simplify (diffCore t outerExpr))
                        StepLog.Journal.Record(id, title, formula.Replace("{u}", t), box (lst [LispSym ("d/d" + t); outerExpr]),
                                               box outerD, StepLog.Main)
                        diffCore x expr
                    StepLog.Journal.Within("diff-chain", "Цепное правило (сложная функция)", before, StepLog.Main, run,
                                           finish "(f(u))' = f'(u)·u'")
    | _ -> diffCore x expr

and private diffCore (x: string) (expr: LispValue) : LispValue =
    match expr with
    | LispInteger _ | LispRational _ | LispFloat _ | LispComplex _
    | LispBool _ | LispStr _ | LispNil -> num 0
    | LispSym name -> if name = x then num 1 else num 0
    | LispList (LispSym op :: args) -> diffOp x op args
    | LispList [] -> num 0
    // Шаг 14: объект — метод (diff type) со всеми аргументами (obj x); нет метода — символьно (diff obj x)
    | LispObject _ ->
        match Objects.tryDispatch "diff" [expr] [expr; LispSym x] with
        | Some r -> r
        | None -> lst [LispSym "diff"; expr; LispSym x]
    | LispVector items -> LispVector (Array.map (diffRaw x) items)
    // Шаг 15: список с головой-не-символом — не выражение и не вектор: константа
    | LispList _ -> num 0
    | _ -> num 0

// Дифференцирование конкретной операции
and private diffOp (x: string) (op: string) (args: LispValue list) : LispValue =
    // Цепное правило: f'(u) * u' — используется почти везде
    let chain (dfu: LispValue) (u: LispValue) : LispValue =
        binop "*" dfu (diffRaw x u)

    match op, args with

    // --- Арифметика ---

    // (piecewise ((условие ответ) …)) — производная по ветвям (раньше: список-константа → 0)
    | "piecewise", [LispList branches] ->
        let dbranch b =
            match b with
            | LispList [c; a] -> lst [c; diffRaw x a]
            | other -> other
        lst [LispSym "piecewise"; lst (List.map dbranch branches)]

    | "+", _ -> lst (LispSym "+" :: List.map (diffRaw x) args)

    | "-", [a] -> binop "-" (num 0) (diffRaw x a)
    | "-", _ -> lst (LispSym "-" :: List.map (diffRaw x) args)

    | "*", [a; b] ->
        binop "+" (binop "*" (diffRaw x a) b) (binop "*" a (diffRaw x b))
    | "*", [a] -> diffRaw x a
    | "*", _ ->
        let terms = args |> List.mapi (fun i _ ->
            let d = diffRaw x args.[i]
            // Шаг 19: скобки вокруг mapi — раньше mapi шёл по списку вместе с головой "*" (n-арное произведение
            // из 3+ множителей дифференцировалось неверно)
            lst (LispSym "*" :: (args |> List.mapi (fun j arg -> if j = i then d else arg))))
        lst (LispSym "+" :: terms)

    | "/", [a; b] ->
        let da, db = diffRaw x a, diffRaw x b
        binop "/" (binop "-" (binop "*" da b) (binop "*" a db)) (binop "^" b (num 2))
    | "/", [a] ->
        binop "-" (num 0) (binop "/" (diffRaw x a) (binop "^" a (num 2)))

    | "^", [bse; exp] ->
        match exp with
        | k when isNumber k ->
            let nMinus1 = binop "-" k (num 1)
            lst [LispSym "*"; k; binop "^" bse nMinus1; diffRaw x bse]
        | _ ->
            let db, de = diffRaw x bse, diffRaw x exp
            let term1 = binop "*" de (f "log" bse)
            let term2 = binop "/" (binop "*" exp db) bse
            binop "*" (binop "^" bse exp) (binop "+" term1 term2)

    // --- Тригонометрические ---
    | "sin", [u] -> chain (f "cos" u) u
    | "cos", [u] -> chain (binop "-" (num 0) (f "sin" u)) u
    | "tan", [u] -> chain (binop "/" (num 1) (binop "^" (f "cos" u) (num 2))) u
    | "cot", [u] -> chain (binop "-" (num 0) (binop "/" (num 1) (binop "^" (f "sin" u) (num 2)))) u
    | "sec", [u] -> chain (binop "*" (f "sec" u) (f "tan" u)) u
    | "csc", [u] -> chain (binop "-" (num 0) (binop "*" (f "csc" u) (f "cot" u))) u

    // --- Гиперболические ---
    | "sinh", [u] -> chain (f "cosh" u) u
    | "cosh", [u] -> chain (f "sinh" u) u
    // Шаг 19: (tanh u)' = sech²u, (coth u)' = −csch²u (раньше было 1/sech² и −1/csch² — ошибка в знаке показателя)
    | "tanh", [u] -> chain (binop "^" (f "sech" u) (num 2)) u
    | "coth", [u] -> chain (binop "-" (num 0) (binop "^" (f "csch" u) (num 2))) u
    | "sech", [u] -> chain (binop "-" (num 0) (binop "*" (f "sech" u) (f "tanh" u))) u
    | "csch", [u] -> chain (binop "-" (num 0) (binop "*" (f "csch" u) (f "coth" u))) u

    // --- Обратные тригонометрические ---
    // d/dx(asin u) = u' / sqrt(1 - u²)
    | "asin", [u] -> chain (binop "/" (num 1) (f "sqrt" (binop "-" (num 1) (binop "^" u (num 2))))) u
    // d/dx(acos u) = -u' / sqrt(1 - u²)
    | "acos", [u] -> chain (binop "-" (num 0) (binop "/" (num 1) (f "sqrt" (binop "-" (num 1) (binop "^" u (num 2)))))) u
    // d/dx(atan u) = u' / (1 + u²)
    | "atan", [u] -> chain (binop "/" (num 1) (binop "+" (num 1) (binop "^" u (num 2)))) u
    // d/dx(acot u) = -u' / (1 + u²)
    | "acot", [u] -> chain (binop "-" (num 0) (binop "/" (num 1) (binop "+" (num 1) (binop "^" u (num 2))))) u
    // d/dx(asec u) = u' / (u * sqrt(u² - 1))
    | "asec", [u] -> chain (binop "/" (num 1) (binop "*" u (f "sqrt" (binop "-" (binop "^" u (num 2)) (num 1))))) u
    // d/dx(acsc u) = -u' / (u * sqrt(u² - 1))
    | "acsc", [u] -> chain (binop "-" (num 0) (binop "/" (num 1) (binop "*" u (f "sqrt" (binop "-" (binop "^" u (num 2)) (num 1)))))) u

    // --- Обратные гиперболические ---
    // d/dx(asinh u) = u' / sqrt(1 + u²)
    | "asinh", [u] -> chain (binop "/" (num 1) (f "sqrt" (binop "+" (num 1) (binop "^" u (num 2))))) u
    // d/dx(acosh u) = u' / sqrt(u² - 1)
    | "acosh", [u] -> chain (binop "/" (num 1) (f "sqrt" (binop "-" (binop "^" u (num 2)) (num 1)))) u
    // d/dx(atanh u) = u' / (1 - u²)
    | "atanh", [u] -> chain (binop "/" (num 1) (binop "-" (num 1) (binop "^" u (num 2)))) u
    // d/dx(acoth u) = u' / (1 - u²)
    | "acoth", [u] -> chain (binop "/" (num 1) (binop "-" (num 1) (binop "^" u (num 2)))) u
    // d/dx(asech u) = -u' / (u * sqrt(1 - u²))
    | "asech", [u] -> chain (binop "-" (num 0) (binop "/" (num 1) (binop "*" u (f "sqrt" (binop "-" (num 1) (binop "^" u (num 2))))))) u
    // d/dx(acsch u) = -u' / (u * sqrt(1 + u²))
    | "acsch", [u] -> chain (binop "-" (num 0) (binop "/" (num 1) (binop "*" u (f "sqrt" (binop "+" (num 1) (binop "^" u (num 2))))))) u

    // --- Прочие ---
    | "exp", [u] -> chain (f "exp" u) u
    | "log", [u] -> chain (binop "/" (num 1) u) u
    | "ln", [u] -> chain (binop "/" (num 1) u) u  // ln — алиас для log
    | "sqrt", [u] -> chain (binop "/" (num 1) (binop "*" (num 2) (f "sqrt" u))) u
    | "abs", [u] -> chain (f "sign" u) u

    // --- Шаг 21k.6′: специальные функции ---
    | "erf", [u] -> chain (binop "*" (binop "/" (num 2) (binop "^" (LispSym "pi") (binop "/" (num 1) (num 2)))) (f "exp" (binop "-" (num 0) (binop "^" u (num 2))))) u
    | "erfc", [u] -> chain (binop "-" (num 0) (binop "*" (binop "/" (num 2) (binop "^" (LispSym "pi") (binop "/" (num 1) (num 2)))) (f "exp" (binop "-" (num 0) (binop "^" u (num 2)))))) u
    | "erfi", [u] -> chain (binop "*" (binop "/" (num 2) (binop "^" (LispSym "pi") (binop "/" (num 1) (num 2)))) (f "exp" (binop "^" u (num 2)))) u
    | "Ei", [u] -> chain (binop "/" (f "exp" u) u) u
    | "li", [u] -> chain (binop "/" (num 1) (f "log" u)) u
    | "Si", [u] -> chain (binop "/" (f "sin" u) u) u
    | "Ci", [u] -> chain (binop "/" (f "cos" u) u) u
    | "Shi", [u] -> chain (binop "/" (f "sinh" u) u) u
    | "Chi", [u] -> chain (binop "/" (f "cosh" u) u) u

    // --- Шаг 21l.0: комбинаторные головы ---
    // d/dx Γ(u) = Γ(u)·ψ(u)
    | "gamma", [u] -> chain (binop "*" (f "gamma" u) (f "psi" u)) u
    // d/dx ψ(u) = ψ(u, 1) (полигамма 1-го порядка)
    | "psi", [u] -> chain (lst [LispSym "psi"; u; num 1]) u
    // d/dx ψ(u, m) = ψ(u, m+1) (m — целая константа)
    | "psi", [u; k] when (match k with LispInteger n -> n >= 0I && n <= 99I | _ -> false) ->
        chain (lst [LispSym "psi"; u; binop "+" k (num 1)]) u
    // d/dx H(u) = ψ(u+1) + γ (γ — константа Эйлера; вводим символ euler-gamma, правило задаётся в lib/rules.lisp)
    | "harmonic", [u] -> chain (binop "+" (f "psi" (binop "+" u (num 1))) (LispSym "euler-gamma")) u
    // factorial: d/dx u! = Γ(u+1)·ψ(u+1)
    | "factorial", [u] -> chain (binop "*" (f "gamma" (binop "+" u (num 1))) (f "psi" (binop "+" u (num 1)))) u

    // --- SFn.2a: Бессель (порядок ν — параметр, производная по аргументу) ---
    | "bessel-j", [nu; u] when not (mentions x nu) ->
        chain (binop "*" (binop "/" (num 1) (num 2))
                       (binop "-" (lst [LispSym "bessel-j"; binop "-" nu (num 1); u])
                                  (lst [LispSym "bessel-j"; binop "+" nu (num 1); u]))) u
    | "bessel-y", [nu; u] when not (mentions x nu) ->
        chain (binop "*" (binop "/" (num 1) (num 2))
                       (binop "-" (lst [LispSym "bessel-y"; binop "-" nu (num 1); u])
                                  (lst [LispSym "bessel-y"; binop "+" nu (num 1); u]))) u
    | "bessel-i", [nu; u] when not (mentions x nu) ->
        chain (binop "*" (binop "/" (num 1) (num 2))
                       (binop "+" (lst [LispSym "bessel-i"; binop "-" nu (num 1); u])
                                  (lst [LispSym "bessel-i"; binop "+" nu (num 1); u]))) u
    | "bessel-k", [nu; u] when not (mentions x nu) ->
        chain (binop "*" (binop "/" (num -1) (num 2))
                       (binop "+" (lst [LispSym "bessel-k"; binop "-" nu (num 1); u])
                                  (lst [LispSym "bessel-k"; binop "+" nu (num 1); u]))) u

    // --- SFn.2a: Эри (Ai″ = x·Ai, Bi″ = x·Bi) ---
    | "airy-ai", [u] -> chain (f "airy-ai-prime" u) u
    | "airy-bi", [u] -> chain (f "airy-bi-prime" u) u
    | "airy-ai-prime", [u] -> chain (binop "*" u (f "airy-ai" u)) u
    | "airy-bi-prime", [u] -> chain (binop "*" u (f "airy-bi" u)) u

    // --- SFn.2a: Лежандр n(xP_n − P_{n−1})/(x²−1) ---
    | "legendre-p", [n; u] when not (mentions x n) ->
        chain (binop "/" (binop "*" n (binop "-" (binop "*" u (lst [LispSym "legendre-p"; n; u]))
                                              (lst [LispSym "legendre-p"; binop "-" n (num 1); u])))
                            (binop "-" (binop "^" u (num 2)) (num 1))) u
    | "legendre-q", [n; u] when not (mentions x n) ->
        chain (binop "/" (binop "*" n (binop "-" (binop "*" u (lst [LispSym "legendre-q"; n; u]))
                                              (lst [LispSym "legendre-q"; binop "-" n (num 1); u])))
                            (binop "-" (binop "^" u (num 2)) (num 1))) u

    // --- A3′.3: эллиптические интегралы (производная по φ; модуль k считается постоянным) ---
    // d/dφ F(φ,k) = 1/√(1 − k²sin²φ)
    | "elliptic-f", [u; k] ->
        let s = f "sin" u
        let inner = binop "-" (num 1) (binop "*" (binop "^" k (num 2)) (binop "^" s (num 2)))
        chain (binop "^" inner (LispRational(-1I, 2I))) u
    // d/dφ E(φ,k) = √(1 − k²sin²φ)
    | "elliptic-e", [u; k] ->
        let s = f "sin" u
        let inner = binop "-" (num 1) (binop "*" (binop "^" k (num 2)) (binop "^" s (num 2)))
        chain (binop "^" inner (LispRational(1I, 2I))) u
    // d/dφ Π(n;φ,k) = 1/((1 − n·sin²φ)·√(1 − k²sin²φ))
    | "elliptic-pi", [n; u; k] ->
        let s = f "sin" u
        let a = binop "-" (num 1) (binop "*" n (binop "^" s (num 2)))
        let b = binop "-" (num 1) (binop "*" (binop "^" k (num 2)) (binop "^" s (num 2)))
        chain (binop "/" (num 1) (binop "*" a (binop "^" b (LispRational(1I, 2I))))) u

    // --- Шаг 20: невычисленные интегралы ---
    // d/dx (integrate f x) = f (неопределённый, та же переменная); другая переменная v — под знаком интеграла
    | "integrate", [fe; LispSym v] ->
        if v = x then fe
        else
            let df = simplify (diffRaw x fe)
            if isZero df then num 0 else lst [LispSym "integrate"; df; LispSym v]
    // Правило Лейбница: d/dx ∫_a^b f dt = f(b)·b' − f(a)·a' + ∫_a^b ∂f/∂x dt
    | "integrate", [fe; LispSym t; a; b] ->
        if t = x then num 0
        else
            let lead =
                binop "-" (binop "*" (substSym t b fe) (diffRaw x b))
                          (binop "*" (substSym t a fe) (diffRaw x a))
            let df = simplify (diffRaw x fe)
            if isZero df then lead
            else binop "+" lead (lst [LispSym "integrate"; df; LispSym t; a; b])

    // --- Шаг 21h: сумма по корням (root-sum t Q E) = Σ_{Q(α)=0} E(α, x) ---
    // d/dx: внутрь; если Q зависит от x, корни «движутся»: α' = −Q_x/Q_t, добавка E_t·α'
    | "root-sum", [LispSym tv; q; e] ->
        if tv = x then num 0
        else
            let dq = simplify (diffRaw x q)
            let de =
                if isZero dq then diffRaw x e
                else
                    let moving = binop "*" (diffRaw tv e) (binop "/" (binop "-" (num 0) dq) (diffRaw tv q))
                    binop "+" (diffRaw x e) moving
            lst [LispSym "root-sum"; LispSym tv; q; de]

    // --- ODE.0: производная неизвестной функции в точке ---
    // (deriv f k u) — k-я производная f в точке u; d/dx → (deriv f (k+1) u)·u′
    | "deriv", [fs; k; u] ->
        if not (mentions x u) then num 0
        else chain (lst [LispSym "deriv"; fs; binop "+" k (num 1); u]) u

    // --- Кусочно-постоянные (производная 0 почти всюду) и корни по связанной переменной ---
    | ("sign" | "floor" | "ceiling" | "round" | "truncate" | "root-of"), _ -> num 0

    // --- ODE.0: неизвестная функция одного аргумента, зависящего от x ---
    // f(u) → f′(u)·u′ (цепное правило через deriv). Для f(x) производная остаётся
    // невычисленной (diff (f x) x) — так не ломается y(x); для (u x t) — частная, тоже невычисленная.
    | _ when args.Length = 1 && List.exists (mentions x) args
             && (match args.[0] with LispSym s -> s <> x | _ -> true) ->
        chain (lst [LispSym "deriv"; LispSym op; num 1; args.[0]]) args.[0]

    // --- Шаг 21k.6′: неизвестная функция от x — невычисленная производная (diff (f u) x); раньше 0 (неверно) ---
    | _ when List.exists (mentions x) args -> lst [LispSym "diff"; lst (LispSym op :: args); LispSym x]
    | _ -> num 0

// Публичная функция: производная, приведённая к канонической форме (Шаг 13).
// Внутри строится «сырое» выражение по правилам, затем один раз вызывается simplify
let diff (x: string) (expr: LispValue) : LispValue =
    if not StepLog.Journal.Enabled then simplify (diffRaw x expr)
    else
        // Шаг S.2: верхний шаг «Дифференцирование по x»; внутри — дерево правил и шаг упрощения результата (detail)
        StepLog.Journal.Within("differentiation", "Дифференцирование по " + x, dOf x expr, StepLog.Main,
            (fun () ->
                let raw = diffRaw x expr
                StepLog.Journal.Within("simplify-result", "Упрощение результата", box raw, StepLog.Detail,
                    (fun () -> simplify raw),
                    (fun r -> if structEqual raw r then None else Some ("", box r)))),
            (fun r -> Some ("", box r)))
