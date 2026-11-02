// Регистрация CAS-функций и арифметики (Шаг 15a: вынесено из Evaluator.fs)
//
// Здесь всё, что не требует eval/apply: simplify/diff/integrate/expand/factor, match/rewrite,
// math-print/math-read/math, orderp, poly-*, алгебраические числа, арифметика и сравнения.
// Каждое имя регистрируется РОВНО ОДИН РАЗ (дубликаты ловит Evaluator.newEnv).
module CasBuiltins

open Types
open Numeric
open Builtins
open Algebraic

// Список коэффициентов (от старшей степени к младшей; целые или рациональные) → MPoly от переменной 0
let private polyOfCoeffs (who: string) (v: LispValue) : MPoly.MPoly =
    match v with
    | LispList items ->
        let cs =
            items |> List.map (fun i ->
                match i with
                | LispInteger n -> MPoly.ofInt n
                | LispRational (n, d) -> MPoly.ofRat (n, d)
                | other -> failwithf "%s: коэффициент должен быть целым или рациональным, получено %s" who (Printer.prettyPrint other))
        MPoly.mk 0 (cs |> List.rev |> Array.ofList)
    | other -> failwithf "%s: ожидается список коэффициентов, получено %s" who (Printer.prettyPrint other)

// MPoly от переменной 0 → список коэффициентов от старшей степени к младшей (ноль → (0))
let private polyToValue (p: MPoly.MPoly) : LispValue =
    match p with
    | MPoly.Const q -> LispList [ratToValue q]
    | MPoly.Poly (_, cs) ->
        LispList (cs |> Array.rev |> Array.map (fun c ->
            match c with
            | MPoly.Const q -> ratToValue q
            | _ -> failwith "poly: внутренняя ошибка (многомерный коэффициент)") |> List.ofArray)

// CAS-функция simplify
let private doSimplify (args: LispValue list) : LispValue =
    match args with
    | [e] -> Simplify.simplify e
    | _ -> failwith "simplify: требуется один аргумент"

// Шаг S.2: упрощение с шагом «Упрощение» (simplification): внутри — сработавшие преобразования упрощателя (шаги 21d,
// level detail, rule simplify:имя). Неизменное выражение шага не даёт. Журнал выключен — обычный simplify
let simplifyRecorded (e: LispValue) : LispValue =
    if not StepLog.Journal.Enabled then Simplify.simplify e
    else
        StepLog.Journal.Within("simplification", "Упрощение", box e, StepLog.Main,
            (fun () -> Debug.withSimplifyJournal (fun () -> Simplify.simplify e)),
            (fun r -> if structEqual e r then None else Some ("", box r)))

// CAS-функция diff — символьное дифференцирование
let private doDiff (args: LispValue list) : LispValue =
    match args with
    | [LispSym var; expr] -> Differentiate.diff var expr
    | [var; expr] ->
        match var with
        | LispSym v -> Differentiate.diff v expr
        | v -> Printer.expectError "diff" 1 "ожидался символ (имя переменной)" v
    | _ -> failwith "diff: требуется два аргумента: переменная и выражение"

// CAS-функция expand — раскрытие скобок
let private doExpand (args: LispValue list) : LispValue =
    match args with
    | [e] -> Expand.expand e
    | _ -> failwith "expand: требуется один аргумент"

// CAS-функция factor — вынесение общего множителя
let private doFactor (args: LispValue list) : LispValue =
    match args with
    | [e] -> Factor.factor e
    | _ -> failwith "factor: требуется один аргумент"

// CAS-функция match — паттерн-матчинг: (match pattern expr) → #t или #f
let private doMatch (args: LispValue list) : LispValue =
    match args with
    | [pattern; expr] ->
        match PatternMatching.matchPattern pattern expr PatternMatching.noBindings with
        | Some _ -> LispBool true
        | None -> LispBool false
    | _ -> failwith "match: требуется два аргумента: паттерн и выражение"

// Шаг 21h'': (match-bindings pattern expr) → список привязок ((?x значение) ...) в порядке имён или #f;
// пустой список (образец без переменных совпал) — истина: ложь в Lisp только #f
let private doMatchBindings (args: LispValue list) : LispValue =
    match args with
    | [pattern; expr] ->
        match PatternMatching.matchPattern pattern expr PatternMatching.noBindings with
        | Some b -> LispList [ for KeyValue (k, v) in b -> LispList [ LispSym k; v ] ]
        | None -> LispBool false
    | _ -> failwith "match-bindings: требуется два аргумента: паттерн и выражение"

// CAS-функция rewrite — применить правило: (rewrite pattern replacement expr)
let private doRewrite (args: LispValue list) : LispValue =
    match args with
    | [pattern; replacement; expr] ->
        match PatternMatching.applyRule pattern replacement expr with
        | Some result -> result
        | None -> expr
    | _ -> failwith "rewrite: требуется три аргумента: паттерн, замена, выражение"

// --- Арифметика (Шаг 15: символьная, как в muSIMP; Шаг 15a: алгебраические — через методы) ---

// Не-числа и значения, требующие диспетчеризации (объекты, векторы, алгебраические числа),
// идут через упроститель: (+ 'a 1) → (+ 1 a); для алгебраических — методы + и *
let private arith (op: string) (numeric: LispValue list -> LispValue) (args: LispValue list) : LispValue =
    if List.exists Objects.needsDispatch args || not (List.forall isNumber args) then
        Simplify.simplify (LispList (LispSym op :: args))
    else numeric args

// Сравнения: значения с диспетчеризацией — методы по имени операции; нет метода — числовая
// ветка (бросает то же исключение, что и раньше)
let private compareOp (op: string) (numeric: LispValue list -> LispValue) (args: LispValue list) : LispValue =
    if List.exists Objects.needsDispatch args then
        match Objects.tryDispatch op args args with
        | Some r -> r
        | None -> numeric args
    else numeric args

// LANG.1: цепочечное сравнение (< a b c ...): 2 аргумента — как compareOp (с диспетчеризацией
// алгебраических чисел); больше — каждая соседняя пара через compareOp, все пары — истина
let private compareChain (op: string) (chain: LispValue list -> LispValue) (args: LispValue list) : LispValue =
    if args.Length <= 2 then compareOp op chain args
    else
        let pair (a: LispValue) (b: LispValue) : bool =
            match compareOp op chain [a; b] with
            | LispBool r -> r
            | _ -> failwithf "%s: цепочка применима к сравнимым значениям" op
        args |> List.pairwise |> List.forall (fun (a, b) -> pair a b) |> LispBool

// Алгебраический квадратный корень из p/q (положительный корень qx² - p = 0)
let private algSqrt (p: bigint) (q: bigint) : LispValue =
    let roots = Sturm.isolateRoots [q; 0I; -p]
    roots |> List.tryFind (fun (_, (loN, _), (hiN, _)) -> loN >= 0I || hiN > 0I)
    |> Option.map (fun (poly, lo, hi) -> LispAlgebraic (poly, lo, hi))
    |> Option.defaultWith (fun () -> LispFloat (sqrt (double p / double q)))

// sqrt: точный результат для полных квадратов, алгебраическое число для прочих n >= 0
let rec private doSqrt (args: LispValue list) : LispValue =
    match args with
    // Шаг 18: корень из отрицательного рационального числа — %i-форма: (sqrt -4) → (* 2 %i), (sqrt -2) → (* %i <корень 2>)
    | [(LispInteger _ | LispRational _) as v] when compareNum v (LispInteger 0I) < 0 ->
        Simplify.simplify (LispList [LispSym "*"; LispSym "%i"; doSqrt [Simplify.simplify (LispList [LispSym "*"; LispInteger -1I; v])]])
    | [LispInteger n] when n >= 0I ->
        let sq = isqrtBigint n
        if sq * sq = n then LispInteger sq else algSqrt n 1I
    | [LispRational (p, q)] ->
        let sqP = isqrtBigint p
        let sqQ = isqrtBigint q
        if sqP * sqP = p && sqQ * sqQ = q then makeRational sqP sqQ
        else algSqrt p q
    // отрицательный float → комплексный float (0, sqrt|f|); NaN больше никогда не возвращается
    | [LispFloat f] when f < 0.0 -> LispComplex (LispFloat 0.0, LispFloat (sqrt (-f)))
    | [v] when isNumber v -> LispFloat (sqrt (toDouble v))
    | [v] -> LispList [LispSym "sqrt"; v]
    | _ -> failwith "sqrt: один аргумент"

// Целые коэффициенты из списка
let private intCoeffs (who: string) (items: LispValue list) : bigint list =
    items |> List.map (fun i ->
        match i with
        | LispInteger n -> n
        | _ -> failwithf "%s: коэффициенты — целые" who)

let private ratOf (who: string) (what: string) (v: LispValue) : bigint * bigint =
    match v with
    | LispInteger n -> (n, 1I)
    | LispRational (p, q) -> (p, q)
    | _ -> failwithf "%s: %s — число" who what

// --- Методы алгебраических чисел (механизм шага 14) ---

let private binMethod (name: string) (f: LispValue -> LispValue -> LispValue) : LispValue =
    LispBuiltin (Builtin (fun args ->
        match args with
        | [a; b] -> f a b
        | _ -> failwithf "%s: метод принимает два аргумента" name))

// Методы + * = < > для пар (real algebraic), (algebraic real), (algebraic algebraic).
// «real» покрывает integer/rational/float по иерархии (float — вещественная арифметика Numeric).
// Вызывается из Evaluator.newEnv; повторный вызов безвреден (метод с тем же ключом заменяется)
let registerAlgebraicMethods () : unit =
    let pairs = [ ["real"; "algebraic"]; ["algebraic"; "real"]; ["algebraic"; "algebraic"] ]
    for types in pairs do
        Objects.addMethod "+" types (binMethod "+" algAddRaw)
        Objects.addMethod "*" types (binMethod "*" algMulRaw)
        Objects.addMethod "=" types (binMethod "=" (fun a b -> LispBool (algCompare a b = 0)))
        Objects.addMethod "<" types (binMethod "<" (fun a b -> LispBool (algCompare a b < 0)))
        Objects.addMethod ">" types (binMethod ">" (fun a b -> LispBool (algCompare a b > 0)))
    // Шаг 15b: (^ algebraic integer), n >= 0 — бинарное возведение повторным algMulRaw;
    // n < 0 — символьная форма (^ a n) (simplifyPow распознаёт её как «метод не применим»)
    Objects.addMethod "^" ["algebraic"; "integer"] (binMethod "^" (fun a n ->
        match n with
        | LispInteger k when k >= 0I ->
            let rec pow (k: int) : LispValue =
                if k = 0 then LispInteger 1I
                elif k = 1 then a
                elif k % 2 = 0 then (let h = pow (k / 2) in algMulRaw h h)
                else algMulRaw a (pow (k - 1))
            pow (int k)
        | _ -> LispList [ LispSym "^"; a; n ]))

// Шаг 21d: упрощение с журналом шагов. Шаг — ((имя до после)); если журнал усечён (Debug.simpMaxSteps) —
// последний элемент (…усечено)
let private truncatedMark = "…усечено"

let private simplifyWithSteps (e: LispValue) : LispValue * LispValue list =
    let r, steps, truncated = Debug.collectSimpSteps (fun () -> Simplify.simplify e)
    let items = steps |> List.map (fun (n, b, a) -> LispList [ LispSym n; b; a ])
    r, (if truncated then items @ [ LispList [ LispSym truncatedMark ] ] else items)

// Строка шага в синтаксисе math-print (lang = true — в синтаксисе входного языка): «[exact-value] sin(1/2*pi) → 1»
let private stepText (lang: bool) (step: LispValue) : string =
    let pr = if lang then MathPrinter.mathPrintLang else MathPrinter.mathPrint
    match step with
    | LispList [ LispSym name; b; a ] -> sprintf "[%s] %s → %s" name (pr b) (pr a)
    | LispList [ LispSym s ] when s = truncatedMark ->
        sprintf "%s (показаны первые %d шагов)" truncatedMark Debug.simpMaxSteps
    | other -> Printer.prettyPrint other

// Все CAS-builtins (порядок не важен — имена уникальны)
let all : (string * LispValue) list = [
    builtin "simplify" doSimplify
    builtin "diff" doDiff
    // Шаг 21l.0: комбинаторные головы — Lisp-вызовы (binomial 10 3) упрощаются (точные значения
    // в Simplify.combinatorValue, правила — rules.lisp; арность/типы проверяет упрощатель)
    builtin "binomial" (fun args -> Simplify.simplify (LispList (LispSym "binomial" :: args)))
    builtin "gamma" (fun args -> Simplify.simplify (LispList (LispSym "gamma" :: args)))
    builtin "rf" (fun args -> Simplify.simplify (LispList (LispSym "rf" :: args)))
    builtin "ff" (fun args -> Simplify.simplify (LispList (LispSym "ff" :: args)))
    builtin "harmonic" (fun args -> Simplify.simplify (LispList (LispSym "harmonic" :: args)))
    builtin "psi" (fun args -> Simplify.simplify (LispList (LispSym "psi" :: args)))
    builtin "bernoulli" (fun args -> Simplify.simplify (LispList (LispSym "bernoulli" :: args)))
    // Шаг S.2: (step-simplify e) — simplify с записью шага «Упрощение» и преобразований упрощателя
    builtin "step-simplify" (fun args ->
        match args with
        | [e] -> simplifyRecorded e
        | _ -> failwith "step-simplify: требуется один аргумент")
    // Шаг 13: полный порядок на выражениях — (orderp a b) → #t, если a предшествует b или равно
    builtin "orderp" (fun args ->
        match args with
        | [a; b] -> LispBool (Order.orderp a b)
        | _ -> failwith "orderp: требуется два аргумента")
    // Шаг 21d: (simplify-steps e) → ((имя до после) ...) без печати; (trace-simplify e) печатает шаги построчно и
    // возвращает результат упрощения; (simplify-step-text шаг [язык?]) — строка шага
    builtin "simplify-steps" (fun args ->
        match args with
        | [e] -> LispList (snd (simplifyWithSteps e))
        | _ -> failwith "simplify-steps: один аргумент — выражение")
    builtin "trace-simplify" (fun args ->
        match args with
        | [e] ->
            let r, steps = simplifyWithSteps e
            for s in steps do Debug.out().WriteLine(stepText false s)
            r
        | _ -> failwith "trace-simplify: один аргумент — выражение")
    builtin "simplify-step-text" (fun args ->
        match args with
        | [s] -> LispStr (stepText false s)
        | [s; lang] -> LispStr (stepText (Builtins.isTruthy lang) s)
        | _ -> failwith "simplify-step-text: шаг [и признак языка]")
    builtin "expand" doExpand
    builtin "factor" doFactor
    // Шаг 19: integrate — функция Lisp (lib\integrate.lisp), не builtin
    builtin "match" doMatch
    builtin "match-bindings" doMatchBindings
    builtin "rewrite" doRewrite
    // Шаг D1: (show e) — печатает e в математической записи (mathPrint) с учётом ограничения печати,
    // перевод строки; возвращает e (удобно вставлять в цепочки при отладке). Печать — побочный эффект
    builtin "show" (fun args ->
        match args with
        | [ e ] ->
            System.Console.WriteLine(Printer.limitPrint e (MathPrinter.mathPrint e))
            e
        | _ -> failwith "show: требуется один аргумент")
    // Шаг D1: (set-print-limit n) — ограничение печати результата хостом (REPL, -e, show); 0 — без лимита
    builtin "set-print-limit" (fun args ->
        match args with
        | [ LispInteger n ] -> Printer.PrintLimit <- int n; LispInteger n
        | [v] -> Printer.expectError "set-print-limit" 1 "ожидалось целое число" v
        | _ -> failwith "set-print-limit: один аргумент")
    // Шаг 8a: красивая математическая запись — (math-print 'expr) → строка с инфиксной записью
    builtin "math-print" (fun args ->
        match args with
        | [e] -> LispStr (MathPrinter.mathPrint e)
        | _ -> failwith "math-print: требуется один аргумент")
    // Шаг TEX.1: LaTeX-запись (KaTeX) — (math-latex 'expr) → строка
    builtin "math-latex" (fun args ->
        match args with
        | [e] -> LispStr (LatexPrinter.latexPrint e)
        | _ -> failwith "math-latex: требуется один аргумент")
    // Шаг 8b: разбор инфиксной математической записи — (math-read "2x^2+3x-5") возвращает дерево БЕЗ вычисления
    builtin "math-read" (fun args ->
        match args with
        | [LispStr s] -> MathReader.mathParse s
        | _ -> failwith "math-read: требуется одна строка")
    // (math "2x^2+3x") — разбирает И СРАЗУ упрощает; «сырое» дерево — через math-read
    builtin "math" (fun args ->
        match args with
        | [LispStr s] -> MathReader.mathParse s |> Simplify.simplify
        | _ -> failwith "math: требуется одна строка")
    // Шаг 21: программа входного языка → список операторов (AST, см. MathReader.fs); ошибка — с номером строки и позиции
    builtin "math-read-program" (fun args ->
        match args with
        | [LispStr s] -> LispList (MathReader.mathParseProgram s)
        // Шаг 21d: второй аргумент — имя файла для позиций (строка .mth в стеке ошибок)
        | [LispStr s; LispStr file] -> LispList (MathReader.mathParseProgramFrom file s)
        | _ -> failwith "math-read-program: требуется строка [и имя файла]")
    // Шаг 21: печать в синтаксисе входного языка (true/false, ∞, вызовы любых функций)
    builtin "math-show" (fun args ->
        match args with
        | [e] -> LispStr (MathPrinter.mathPrintLang e)
        | _ -> failwith "math-show: требуется один аргумент")
    // Шаг 21: содержимое текстового файла (load-math)
    builtin "read-text-file" (fun args ->
        match args with
        | [LispStr path] ->
            Sandbox.checkRead "read-text-file" path      // подшаг 22.4: песочница --mcp
            if System.IO.File.Exists path then LispStr (System.IO.File.ReadAllText path)
            else failwithf "файл не найден: %s" path
        | _ -> failwith "read-text-file: требуется путь (строка)")
    // --- Многочлены (коэффициенты: старшая степень первой) ---
    // (poly-add '(1 1) '(1 -1)) → (2 0), т.е. (x+1)+(x-1) = 2x
    // Шаг 17a: реализация через MPoly (одна переменная с номером 0); коэффициенты — целые или рациональные
    builtin "poly-add" (fun args ->
        match args with
        | [a; b] -> MPoly.add (polyOfCoeffs "poly-add" a) (polyOfCoeffs "poly-add" b) |> polyToValue
        | _ -> failwith "poly-add: два аргумента")
    builtin "poly-sub" (fun args ->
        match args with
        | [a; b] -> MPoly.sub (polyOfCoeffs "poly-sub" a) (polyOfCoeffs "poly-sub" b) |> polyToValue
        | _ -> failwith "poly-sub: два аргумента")
    builtin "poly-mul" (fun args ->
        match args with
        | [a; b] -> MPoly.mul (polyOfCoeffs "poly-mul" a) (polyOfCoeffs "poly-mul" b) |> polyToValue
        | _ -> failwith "poly-mul: два аргумента")
    builtin "poly-degree" (fun args ->
        match args with
        | [a] -> LispInteger (bigint (max 0 (MPoly.degMain (polyOfCoeffs "poly-degree" a))))
        | _ -> failwith "poly-degree: один аргумент")
    // (poly-eval '(coeffs) x) — значение в точке x (целой или рациональной)
    builtin "poly-eval" (fun args ->
        match args with
        | [a; x] ->
            let xq =
                match x with
                | LispInteger n -> (n, 1I)
                | LispRational (n, d) -> ratNorm (n, d)
                | other -> failwithf "poly-eval: точка должна быть рациональной, получено %s" (Printer.prettyPrint other)
            match MPoly.subst 0 (MPoly.ofRat xq) (polyOfCoeffs "poly-eval" a) with
            | MPoly.Const q -> ratToValue q
            | _ -> failwith "poly-eval: внутренняя ошибка"
        | _ -> failwith "poly-eval: два аргумента")
    // (poly-deriv '(coeffs)) — производная
    builtin "poly-deriv" (fun args ->
        match args with
        | [a] -> MPoly.deriv 0 (polyOfCoeffs "poly-deriv" a) |> polyToValue
        | _ -> failwith "poly-deriv: один аргумент")
    // (poly-div '(a) '(b)) → список (частное остаток); деление над ℚ: a = q*b + r, deg r < deg b
    builtin "poly-div" (fun args ->
        match args with
        | [a; b] ->
            let pa = polyOfCoeffs "poly-div" a
            let pb = polyOfCoeffs "poly-div" b
            if MPoly.isZero pb then failwith "poly-div: деление на нулевой многочлен"
            let db = MPoly.degMain pb
            let lcb = match MPoly.lcMain pb with MPoly.Const q -> q | _ -> failwith "poly-div: внутренняя ошибка"
            let mutable rem = pa
            let mutable quo = MPoly.zero
            // каждый шаг снимает старший член остатка: степень строго падает — цикл конечен
            while not (MPoly.isZero rem) && MPoly.degMain rem >= db do
                let lcr = match MPoly.lcMain rem with MPoly.Const q -> q | _ -> failwith "poly-div: внутренняя ошибка"
                let term = MPoly.mulConst (ratDiv lcr lcb) (MPoly.pow (MPoly.var 0) (MPoly.degMain rem - db))
                quo <- MPoly.add quo term
                rem <- MPoly.sub rem (MPoly.mul term pb)
            LispList [polyToValue quo; polyToValue rem]
        | _ -> failwith "poly-div: два аргумента")
    // --- Алгебраические числа (Шаг 12) ---
    // (roots '(1 0 -2)) → список алгебраических чисел (действительные корни)
    builtin "roots" (fun args ->
        match args with
        | [LispList items] ->
            let roots = Sturm.isolateRoots (intCoeffs "roots" items)
            LispList (roots |> List.map (fun (p, lo, hi) -> LispAlgebraic (p, lo, hi)))
        | _ -> failwith "roots: один аргумент — список коэффициентов")
    // (algebraic '(1 0 -2) 1 2) → конструкция с явным интервалом
    builtin "algebraic" (fun args ->
        match args with
        | [LispList items; lo; hi] ->
            LispAlgebraic (intCoeffs "algebraic" items, ratOf "algebraic" "lo" lo, ratOf "algebraic" "hi" hi)
        | _ -> failwith "algebraic: 3 аргумента (poly lo hi)")
    builtin "alg?" (fun args ->
        match args with | [v] -> LispBool (isAlgebraic v) | _ -> failwith "alg?: один аргумент")
    // (alg-compare a b) → -1, 0, 1
    builtin "alg-compare" (fun args ->
        match args with
        | [a; b] -> LispInteger (bigint (algCompare a b))
        | _ -> failwith "alg-compare: два аргумента")
    builtin "alg-refine" (fun args ->
        match args with | [v] -> algRefine v | _ -> failwith "alg-refine: один аргумент")
    builtin "alg-neg" (fun args ->
        match args with | [v] -> algNeg v | _ -> failwith "alg-neg: один аргумент")
    // явные алгебраические операции (то же, что делают методы + и *)
    builtin "alg+" (fun args ->
        match args with | [a; b] -> algAddRaw a b | _ -> failwith "alg+: два аргумента")
    builtin "alg-" (fun args ->
        match args with | [a; b] -> algSubRaw a b | _ -> failwith "alg-: два аргумента")
    builtin "alg*" (fun args ->
        match args with | [a; b] -> algMulRaw a b | _ -> failwith "alg*: два аргумента")

    // --- Арифметика и сравнения ---
    builtin "+" (arith "+" bAdd)
    builtin "-" (arith "-" bSub)
    builtin "*" (arith "*" bMul)
    builtin "/" (arith "/" bDiv)
    builtin "^" (arith "^" bPowExact)
    builtin "=" (compareChain "=" bNumEqChain)
    builtin "<" (compareChain "<" bLessChain)
    builtin ">" (compareChain ">" bGreaterChain)
    // sqrt — точный/алгебраический результат
    builtin "sqrt" doSqrt
]
