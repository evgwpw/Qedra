// Встроенные функции Lisp — доступны по умолчанию в глобальном окружении
module Builtins

open System.Numerics
open Types
open Numeric

// Преобразование LispValue в double (для встроенных функций)
let toDouble (v: LispValue) : double =
    match v with
    | LispInteger n -> double n
    | LispRational (p, q) -> double p / double q
    | LispFloat f -> f
    | _ -> failwithf "Ожидалось число, получено %s" (Printer.prettyPrint v)

// Проверка, что значение истинно (всё кроме #f — истина)
let isTruthy (v: LispValue) : bool =
    match v with
    | LispBool false -> false
    | _ -> true

// Создаём встроенную функцию из F#-делегата
let builtin (name: string) (fn: LispValue list -> LispValue) : (string * LispValue) =
    (name, LispBuiltin (BuiltinFunction.Builtin fn))

// Сложить все аргументы (variadic)
let bAdd (args: LispValue list) : LispValue =
    match args with
    | [] -> LispInteger 0I
    | [x] -> x
    | x :: rest -> List.fold add x rest

// Вычитание: первый минус остальные; один аргумент — унарный минус
let bSub (args: LispValue list) : LispValue =
    match args with
    | [] -> failwith "-: требуется хотя бы один аргумент"
    | [x] -> sub (LispInteger 0I) x  // унарный минус
    | x :: rest -> List.fold sub x rest

// Умножение всех аргументов
let bMul (args: LispValue list) : LispValue =
    match args with
    | [] -> LispInteger 1I
    | [x] -> x
    | x :: rest -> List.fold mul x rest

// Деление: первый делится на остальные
let bDiv (args: LispValue list) : LispValue =
    match args with
    | [] -> failwith "/: требуется хотя бы один аргумент"
    | [x] -> div (LispInteger 1I) x  // унарное деление → 1/x
    | x :: rest -> List.fold div x rest

// Остаток от деления (только целые)
let bMod (args: LispValue list) : LispValue =
    match args with
    | [LispInteger a; LispInteger b] ->
        if b.IsZero then failwith "mod: деление на ноль"
        LispInteger (a % b)
    | _ -> failwith "mod: требуется два целых числа"

// Шаг 21c: целочисленные примитивы. quotient — частное с усечением к нулю; remainder — остаток с знаком делимого
// (то же, что mod); modulo — остаток со знаком делителя (математический mod). Только целые; деление на ноль — ошибка
let private twoInts (who: string) (args: LispValue list) : BigInteger * BigInteger =
    match args with
    | [LispInteger a; LispInteger b] ->
        if b.IsZero then failwithf "%s: деление на ноль" who
        a, b
    | _ -> failwithf "%s: требуется два целых числа" who

let bQuotient (args: LispValue list) : LispValue =
    let a, b = twoInts "quotient" args
    LispInteger (BigInteger.Divide(a, b))

let bRemainder (args: LispValue list) : LispValue =
    let a, b = twoInts "remainder" args
    LispInteger (BigInteger.Remainder(a, b))

let bModulo (args: LispValue list) : LispValue =
    let a, b = twoInts "modulo" args
    let r = BigInteger.Remainder(a, b)
    LispInteger (if not r.IsZero && (r.Sign < 0) <> (b.Sign < 0) then r + b else r)

let private onlyInts (who: string) (args: LispValue list) : BigInteger list =
    args |> List.map (fun a ->
        match a with
        | LispInteger n -> n
        | _ -> failwithf "%s: ожидаются целые числа" who)

// (gcd a b ...) — неотрицательный НОД; (gcd) = 0; (lcm a b ...) — НОК; (lcm) = 1, любой нуль даёт 0
let bGcd (args: LispValue list) : LispValue =
    LispInteger (onlyInts "gcd" args |> List.fold (fun acc n -> BigInteger.GreatestCommonDivisor(acc, n)) 0I)

let bLcm (args: LispValue list) : LispValue =
    let lcm2 (a: BigInteger) (b: BigInteger) =
        if a.IsZero || b.IsZero then 0I
        else BigInteger.Abs(a * b) / BigInteger.GreatestCommonDivisor(a, b)
    LispInteger (onlyInts "lcm" args |> List.fold lcm2 1I)

// (min a b ...), (max a b ...) — n-арные, числа любой точности (целые, рациональные, float); результат — сам
// наибольший/наименьший аргумент, но при наличии float — float (как в Scheme). Не вещественный аргумент
// (символ, комплексное, алгебраическое) — ошибка: сравнивать нечего, невычисленных форм min/max нет
let private extremum (who: string) (wantMax: bool) (args: LispValue list) : LispValue =
    if args.IsEmpty then failwithf "%s: требуется хотя бы один аргумент" who
    for a in args do
        match a with
        | LispInteger _ | LispRational _ | LispFloat _ -> ()
        | _ -> failwithf "%s: ожидаются вещественные числа" who
    let best = args |> List.reduce (fun a b ->
                   let c = compareNum b a
                   if (wantMax && c > 0) || (not wantMax && c < 0) then b else a)
    if args |> List.exists (function LispFloat _ -> true | _ -> false) then LispFloat (toDouble best) else best

let bMin (args: LispValue list) : LispValue = extremum "min" false args
let bMax (args: LispValue list) : LispValue = extremum "max" true args

// --- Сравнения ---

let bNumEq (args: LispValue list) : LispValue =
    match args with
    | [a; b] -> LispBool (numEqual a b)
    | _ -> failwith "=: требуется два аргумента"

let bLess (args: LispValue list) : LispValue =
    match args with
    | [a; b] -> LispBool (numLess a b)
    | _ -> failwith "<: требуется два аргумента"

let bGreater (args: LispValue list) : LispValue =
    match args with
    | [a; b] -> LispBool (numGreater a b)
    | _ -> failwith ">: требуется два аргумента"

let bLessEq (args: LispValue list) : LispValue =
    match args with
    | [a; b] -> LispBool (numLessEq a b)
    | _ -> failwith "<=: требуется два аргумента"

let bGreaterEq (args: LispValue list) : LispValue =
    match args with
    | [a; b] -> LispBool (numGreaterEq a b)
    | _ -> failwith ">=: требуется два аргумента"

// --- Списки ---

let bCar (args: LispValue list) : LispValue =
    match args with
    | [LispList (h :: _)] -> h
    | [LispPair (a, _)] -> a      // Шаг 21d: точечная пара
    | [LispNil] -> failwith "car: nil"
    | [other] -> failwithf "car: ожидается список, получено %s" (Printer.prettyPrint other)
    | _ -> failwith "car: требуется один аргумент"

let bCdr (args: LispValue list) : LispValue =
    match args with
    | [LispList (_ :: t)] -> LispList t
    | [LispPair (_, b)] -> b
    | [LispNil] -> LispNil
    | [other] -> failwithf "cdr: ожидается список, получено %s" (Printer.prettyPrint other)
    | _ -> failwith "cdr: требуется один аргумент"

// Шаг 21d: второй аргумент не список (и не nil) — точечная пара (a . b); со списком — как раньше
let bCons (args: LispValue list) : LispValue =
    match args with
    | [h; LispList t] -> LispList (h :: t)
    | [h; LispNil] -> LispList [h]
    | [h; other] -> LispPair (h, other)
    | _ -> failwith "cons: требуется два аргумента"

// Шаг 21d: (assoc ключ алист) — первый элемент, у которого car равен ключу (equal?): пара (k . v) или список (k v ...);
// элементы, не являющиеся парой/непустым списком, пропускаются; нет — #f
let bAssoc (args: LispValue list) : LispValue =
    match args with
    | [key; LispList items] ->
        items
        |> List.tryFind (fun it ->
            match it with
            | LispPair (k, _) | LispList (k :: _) -> structEqual key k
            | _ -> false)
        |> Option.defaultValue (LispBool false)
    | [_; LispNil] -> LispBool false
    | [_; other] -> failwithf "assoc: ожидается список, получено %s" (Printer.prettyPrint other)
    | _ -> failwith "assoc: требуются ключ и список пар"

let bList (args: LispValue list) : LispValue =
    LispList args

let bNull (args: LispValue list) : LispValue =
    match args with
    | [LispList []] -> LispBool true
    | [LispNil] -> LispBool true
    | [_] -> LispBool false
    | _ -> failwith "null?: требуется один аргумент"

// --- Логика ---

let bNot (args: LispValue list) : LispValue =
    match args with
    | [v] -> LispBool (not (isTruthy v))
    | _ -> failwith "not: требуется один аргумент"

// --- Ввод/вывод ---

let bDisplay (args: LispValue list) : LispValue =
    match args with
    | [v] ->
        // display печатает без кавычек для строк
        let s =
            match v with
            | LispStr str -> str
            | other -> Printer.prettyPrint other
        System.Console.Write(s)
        LispNil
    | _ -> failwith "display: требуется один аргумент"

let bNewline (args: LispValue list) : LispValue =
    System.Console.WriteLine()
    LispNil

// --- Строковые операции ---

let bStrAppend (args: LispValue list) : LispValue =
    let sb = System.Text.StringBuilder()
    for arg in args do
        match arg with
        | LispStr s -> sb.Append(s) |> ignore
        | other -> sb.Append(other.ToString()) |> ignore
    LispStr (sb.ToString())

// (string-contains? строка подстрока) → #t, если подстрока входит в строку (регистр учитывается; пустая — входит всегда)
let bStrContains (args: LispValue list) : LispValue =
    match args with
    | [LispStr s; LispStr sub] -> LispBool (s.Contains(sub, System.StringComparison.Ordinal))
    | _ -> failwith "string-contains?: требуются две строки"

// --- Глубокое равенство (делегирует в Numeric.structEqual) ---

let bEqual (args: LispValue list) : LispValue =
    match args with
    | [a; b] -> LispBool (structEqual a b)
    | _ -> failwith "equal?: требуется два аргумента"

// Псевдоним для обратной совместимости (тесты используют Builtins.deepEqual)
let deepEqual (a: LispValue) (b: LispValue) : bool = structEqual a b

// --- Степень (для символьных выражений) ---

let bPow (args: LispValue list) : LispValue =
    match args with
    | [a; b] ->
        // Если оба числовые — вычисляем; иначе оставляем как символ
        match a, b with
        | LispInteger x, LispInteger e when e >= 0I ->
            LispInteger (BigInteger.Pow(x, int e))
        | _ -> LispList [LispSym "^"; a; b]
    | _ -> failwith "^: требуется два аргумента"

// --- Математические функции (численно или символьно) ---

// Универсальный helper: если аргумент числовой — вычисляем, иначе — символ
let mathBuiltin (name: string) (fn: double -> double) (args: LispValue list) : LispValue =
    match args with
    | [v] when isNumber v -> LispFloat (fn (toDouble v))
    | [v] -> LispList [LispSym name; v]
    | _ -> failwithf "%s: требуется один аргумент" name

let bSin (args: LispValue list) : LispValue = mathBuiltin "sin" sin args
let bCos (args: LispValue list) : LispValue = mathBuiltin "cos" cos args
let bTan (args: LispValue list) : LispValue = mathBuiltin "tan" tan args
let bCot (args: LispValue list) : LispValue = mathBuiltin "cot" (fun x -> 1.0 / tan x) args
let bSec (args: LispValue list) : LispValue = mathBuiltin "sec" (fun x -> 1.0 / cos x) args
let bCsc (args: LispValue list) : LispValue = mathBuiltin "csc" (fun x -> 1.0 / sin x) args

// --- Гиперболические ---
let bSinh (args: LispValue list) : LispValue = mathBuiltin "sinh" sinh args
let bCosh (args: LispValue list) : LispValue = mathBuiltin "cosh" cosh args
let bTanh (args: LispValue list) : LispValue = mathBuiltin "tanh" tanh args
let bCoth (args: LispValue list) : LispValue = mathBuiltin "coth" (fun x -> 1.0 / tanh x) args
let bSech (args: LispValue list) : LispValue = mathBuiltin "sech" (fun x -> 1.0 / cosh x) args
let bCsch (args: LispValue list) : LispValue = mathBuiltin "csch" (fun x -> 1.0 / sinh x) args

// --- Обратные тригонометрические ---
let bAsin (args: LispValue list) : LispValue = mathBuiltin "asin" asin args
let bAcos (args: LispValue list) : LispValue = mathBuiltin "acos" acos args
let bAtan (args: LispValue list) : LispValue = mathBuiltin "atan" atan args
let bAcot (args: LispValue list) : LispValue = mathBuiltin "acot" (fun x -> atan (1.0 / x)) args
let bAsec (args: LispValue list) : LispValue = mathBuiltin "asec" (fun x -> acos (1.0 / x)) args
let bAcsc (args: LispValue list) : LispValue = mathBuiltin "acsc" (fun x -> asin (1.0 / x)) args

// --- Обратные гиперболические ---
let bAsinh (args: LispValue list) : LispValue = mathBuiltin "asinh" (fun x -> log (x + sqrt (x*x + 1.0))) args
let bAcosh (args: LispValue list) : LispValue = mathBuiltin "acosh" (fun x -> log (x + sqrt (x*x - 1.0))) args
let bAtanh (args: LispValue list) : LispValue = mathBuiltin "atanh" (fun x -> 0.5 * log ((1.0 + x) / (1.0 - x))) args
let bAcoth (args: LispValue list) : LispValue = mathBuiltin "acoth" (fun x -> 0.5 * log ((x + 1.0) / (x - 1.0))) args
let bAsech (args: LispValue list) : LispValue = mathBuiltin "asech" (fun x -> log (1.0 / x + sqrt (1.0 / (x*x) - 1.0))) args
let bAcsch (args: LispValue list) : LispValue = mathBuiltin "acsch" (fun x -> log (1.0 / x + sqrt (1.0 / (x*x) + 1.0))) args

let bExp (args: LispValue list) : LispValue = mathBuiltin "exp" exp args
let bLog (args: LispValue list) : LispValue = mathBuiltin "log" log args
let bLn (args: LispValue list) : LispValue = mathBuiltin "ln" log args  // ln = log (натуральный)
let bSqrt (args: LispValue list) : LispValue = mathBuiltin "sqrt" sqrt args

let bAbs (args: LispValue list) : LispValue =
    match args with
    | [LispInteger n] -> LispInteger (abs n)
    | [v] when isNumber v -> LispFloat (abs (toDouble v))
    | [v] -> LispList [LispSym "abs"; v]
    | _ -> failwith "abs: требуется один аргумент"

// Шаг 16: floor / ceiling — целая часть вниз / вверх. Точны для целых и рациональных; float → целое число
let private roundToInteger (name: string) (down: bool) (args: LispValue list) : LispValue =
    match args with
    | [LispInteger n] -> LispInteger n
    | [LispRational (p, q)] ->
        // q > 0; BigInteger.Divide усекает к нулю — поправка для отрицательного остатка
        let quot = BigInteger.Divide(p, q)
        let fl = if (p - quot * q).Sign < 0 then quot - BigInteger.One else quot
        LispInteger (if down then fl else fl + BigInteger.One)
    | [LispFloat f] when not (System.Double.IsNaN f || System.Double.IsInfinity f) ->
        LispInteger (BigInteger (if down then System.Math.Floor f else System.Math.Ceiling f))
    | _ -> failwithf "%s: ожидается конечное вещественное число (целое, рациональное, float)" name

// --- Шаг 15: фундамент для библиотек на Lisp ---

// Элементы списка (nil и пустой список — пусто)
let private listItems (who: string) (v: LispValue) : LispValue list =
    match v with
    | LispList xs -> xs
    | LispNil -> []
    | other -> failwithf "%s: ожидается список, получено %s" who (Printer.prettyPrint other)

// (length x) — длина списка, вектора или строки
let bLength (args: LispValue list) : LispValue =
    match args with
    | [LispList xs] -> LispInteger (bigint xs.Length)
    | [LispNil] -> LispInteger 0I
    | [LispVector v] -> LispInteger (bigint v.Length)
    | [LispStr s] -> LispInteger (bigint s.Length)
    | [other] -> failwithf "length: ожидается список, вектор или строка, получено %s" (Printer.prettyPrint other)
    | _ -> failwith "length: требуется один аргумент"

// (append l1 l2 ...) — n-арная конкатенация списков
let bAppend (args: LispValue list) : LispValue =
    match args |> List.collect (listItems "append") with
    | [] -> LispNil
    | items -> LispList items

// (apply f args) — вызов функции со списком аргументов (через Objects.applyHook)
let bApply (args: LispValue list) : LispValue =
    match args with
    | [f; l] -> Objects.applyHook f (listItems "apply" l)
    | _ -> failwith "apply: требуются функция и список аргументов"

// (call-with-time-limit секунды thunk) — выполнить thunk с бюджетом времени. Результат: (ok v) или (timeout).
// Бюджет — дедлайн на флаге Cancel (тот же механизм, что у таймаута MCP); внешняя отмена (запрос/память)
// не гасится: если флаг поднят не нами — исключение идёт дальше. Раньше бюджет ставил System.Threading.Timer,
// но в WASM его колбэк не выполняется, пока интерпретатор синхронно занят, и вычисление висело навсегда;
// дедлайн же опрашивают те же проверки Cancel.check, что и флаг отмены (Debug.checkStack, трамплин, алгебра).
let bCallWithTimeLimit (args: LispValue list) : LispValue =
    match args with
    | [secs; thunk] ->
        let s =
            match secs with
            | LispInteger n -> float n
            | LispFloat f -> f
            | LispRational (n, d) -> float n / float d
            | _ -> failwith "call-with-time-limit: бюджет — число секунд"
        let prev = Cancel.pushDeadline s
        let mutable popped = false
        let stop () =
            if popped then false
            else
                popped <- true
                let expired = Cancel.ownExpired prev
                Cancel.popDeadline prev
                expired
        try
            try
                let v = Objects.applyHook thunk []
                if stop () then
                    Cancel.clear ()
                    LispList [ LispSym "timeout" ]
                else LispList [ LispSym "ok"; v ]
            with
            | :? Cancel.CancelledException ->
                // истёк наш бюджет — (timeout); внешняя отмена — дальше
                if stop () then
                    Cancel.clear ()
                    LispList [ LispSym "timeout" ]
                else reraise ()
            | LispError (_, _, LispList [ LispSym "timeout"; _ ]) ->
                if stop () then
                    Cancel.clear ()
                    LispList [ LispSym "timeout" ]
                else reraise ()
        finally
            // прочее исключение из thunk: снять дедлайн, иначе он «залипает» и даёт ложные timeout
            // в последующих вычислениях (deadlineExpired сам не сбрасывается)
            if not popped && stop () then Cancel.clear ()
    | _ -> failwith "call-with-time-limit: требуются секунды и thunk"

// (error "сообщение" значения...) — бросает исключение; строки как есть, прочее — через prettyPrint
let bError (args: LispValue list) : LispValue =
    let parts = args |> List.map (fun a -> match a with LispStr s -> s | other -> Printer.prettyPrint other)
    failwith (String.concat " " parts)

let private predicate (name: string) (f: LispValue -> bool) : string * LispValue =
    builtin name (fun args ->
        match args with
        | [v] -> LispBool (f v)
        | _ -> failwithf "%s: требуется один аргумент" name)

// (nth l i) — 0-based элемент списка
let bNth (args: LispValue list) : LispValue =
    match args with
    | [l; LispInteger i] ->
        let xs = listItems "nth" l
        if i.Sign < 0 || BigInteger.Compare(i, BigInteger xs.Length) >= 0 then failwithf "nth: индекс %A вне границ [0, %d)" i xs.Length
        else xs.[int i]
    | _ -> failwith "nth: требуются список и целый индекс"

let bCadr (args: LispValue list) : LispValue =
    match args with
    | [l] -> bNth [l; LispInteger 1I]
    | _ -> failwith "cadr: требуется один аргумент"

let bCaddr (args: LispValue list) : LispValue =
    match args with
    | [l] -> bNth [l; LispInteger 2I]
    | _ -> failwith "caddr: требуется один аргумент"

// (cddr l) — хвост без двух первых элементов (шаг 21i: не было, хотя cadr/caddr есть)
let bCddr (args: LispValue list) : LispValue =
    match args with
    | [LispList (_ :: _ :: t)] -> if t.IsEmpty then LispNil else LispList t
    | [l] -> failwithf "cddr: ожидается список не короче 2, получено %s" (Printer.prettyPrint l)
    | _ -> failwith "cddr: требуется один аргумент"

// --- LANG.1: строки ---

// Шаг LANG.1: string-append требует строки (раньше нестрока молча давала «LispInteger 5» от ToString)
let bStrAppendStrict (args: LispValue list) : LispValue =
    match args with
    | [] -> LispStr ""
    | _ ->
        for a in args do
            match a with
            | LispStr _ -> ()
            | other -> failwithf "string-append: ожидается строка, получено %s" (Printer.prettyPrint other)
        LispStr (args |> List.map (fun a -> match a with LispStr s -> s | _ -> "") |> String.concat "")

let private oneStr (who: string) (args: LispValue list) : string =
    match args with
    | [LispStr s] -> s
    | _ -> failwithf "%s: требуется строка" who

let private twoStrs (who: string) (args: LispValue list) : string * string =
    match args with
    | [LispStr a; LispStr b] -> a, b
    | _ -> failwithf "%s: требуются две строки" who

let bStringLength (args: LispValue list) : LispValue =
    LispInteger (bigint (oneStr "string-length" args).Length)

// (substring s start [end]) — end не указан — до конца; индексы за границами — ошибка
let bSubstring (args: LispValue list) : LispValue =
    let checkIdx (s: string) (i: BigInteger) =
        if i.Sign < 0 || i > bigint s.Length then failwithf "substring: индекс %A вне границ [0, %d]" i s.Length else int i
    match args with
    | [LispStr s; LispInteger a] -> LispStr (s.Substring (checkIdx s a))
    | [LispStr s; LispInteger a; LispInteger b] ->
        let st, en = checkIdx s a, checkIdx s b
        if en < st then failwithf "substring: конец (%d) меньше начала (%d)" en st
        LispStr (s.Substring(st, en - st))
    | _ -> failwith "substring: строка и начало [конец]"

// (string-ref s i) — строка из одного символа; отдельного типа char нет
let bStringRef (args: LispValue list) : LispValue =
    match args with
    | [LispStr s; LispInteger i] ->
        if i.Sign < 0 || BigInteger.Compare(i, bigint s.Length) >= 0 then
            failwithf "string-ref: индекс %A вне границ [0, %d)" i s.Length
        else LispStr (string s.[int i])
    | _ -> failwith "string-ref: строка и индекс"

// (string->list s) — список односимвольных строк
let bStringToList (args: LispValue list) : LispValue =
    let s = oneStr "string->list" args
    if s = "" then LispNil else LispList (Seq.toList s |> List.map (fun c -> LispStr (string c)))

// (list->string список) — элементы — строки (символов нет), конкатенация
let bListToString (args: LispValue list) : LispValue =
    match args with
    | [l] ->
        let items = listItems "list->string" l
        for it in items do
            match it with
            | LispStr _ -> ()
            | other -> failwithf "list->string: элементы — строки, получено %s" (Printer.prettyPrint other)
        LispStr (items |> List.map (fun it -> match it with LispStr s -> s | _ -> "") |> String.concat "")
    | _ -> failwith "list->string: один аргумент — список строк"

// (string->number s) — точное чтение: целое, дробь 1/3 (точно), float; не число — #f
let bStringToNumber (args: LispValue list) : LispValue =
    let s = (oneStr "string->number" args).Trim()
    let (|Big|_|) (t: string) = match BigInteger.TryParse t with | true, v -> Some v | _ -> None
    match s with
    | Big v -> LispInteger v
    | _ ->
        let parts = s.Split '/'
        if parts.Length = 2 then
            match parts.[0], parts.[1] with
            | Big p, Big q when not q.IsZero -> makeRational p q
            | _ -> LispBool false
        else
            match System.Double.TryParse(s, System.Globalization.NumberStyles.Float,
                                          System.Globalization.CultureInfo.InvariantCulture) with
            | true, f when not (System.Double.IsNaN f) && s <> "" -> LispFloat f
            | _ -> LispBool false

// (number->string n) — число печатается как ридер его прочитает
let bNumberToString (args: LispValue list) : LispValue =
    match args with
    | [v] when isNumber v -> LispStr (Printer.prettyPrint v)
    | _ -> failwith "number->string: один аргумент — число"

let bSymbolToString (args: LispValue list) : LispValue =
    match args with
    | [LispSym s] -> LispStr s
    | _ -> failwith "symbol->string: один аргумент — символ"

let bStringQ (args: LispValue list) : LispValue =
    match args with
    | [LispStr _] -> LispBool true
    | [_] -> LispBool false
    | _ -> failwith "string?: один аргумент"

let bStringEq (args: LispValue list) : LispValue =
    let a, b = twoStrs "string=?" args
    LispBool (a = b)

let bStringLess (args: LispValue list) : LispValue =
    let a, b = twoStrs "string<?" args
    LispBool (a < b)

// (string-split s разделитель) — разделитель — непустая строка
let bStringSplit (args: LispValue list) : LispValue =
    let s, sep = twoStrs "string-split" args
    if sep = "" then failwith "string-split: разделитель — непустая строка"
    let parts = s.Split([| sep |], System.StringSplitOptions.None) |> Array.toList
    if parts.IsEmpty then LispNil else LispList (List.map LispStr parts)

// (string-join список разделитель) — элементы — строки
let bStringJoin (args: LispValue list) : LispValue =
    match args with
    | [l; LispStr sep] ->
        let items = listItems "string-join" l
        for it in items do
            match it with
            | LispStr _ -> ()
            | other -> failwithf "string-join: элементы — строки, получено %s" (Printer.prettyPrint other)
        LispStr (String.concat sep (items |> List.map (fun it -> match it with LispStr s -> s | _ -> "")))
    | _ -> failwith "string-join: список строк и разделитель"

let bStringUpcase (args: LispValue list) : LispValue = LispStr ((oneStr "string-upcase" args).ToUpperInvariant())
let bStringDowncase (args: LispValue list) : LispValue = LispStr ((oneStr "string-downcase" args).ToLowerInvariant())

// (string-index s подстрока) — позиция первого вхождения (ord) или #f
let bStringIndex (args: LispValue list) : LispValue =
    let s, sub = twoStrs "string-index" args
    match s.IndexOf(sub, System.StringComparison.Ordinal) with
    | -1 -> LispBool false
    | i -> LispInteger (bigint i)

// (format "шаблон ~a и ~s" x y ...) — ~a — display (строки без кавычек), ~s — write, ~% — перевод строки,
// ~~ — тильда; лишние значения игнорируются, без значения тильда-код остаётся как есть
let bFormat (args: LispValue list) : LispValue =
    match args with
    | LispStr tmpl :: vals ->
        let sb = System.Text.StringBuilder()
        let mutable vi = 0
        let disp (v: LispValue) = match v with LispStr s -> s | other -> Printer.prettyPrint other
        let mutable i = 0
        while i < tmpl.Length do
            let c = tmpl.[i]
            if c = '~' && i + 1 < tmpl.Length then
                match tmpl.[i + 1] with
                | 'a' when vi < vals.Length -> sb.Append (disp vals.[vi]) |> ignore; vi <- vi + 1
                | 's' when vi < vals.Length -> sb.Append (Printer.prettyPrint vals.[vi]) |> ignore; vi <- vi + 1
                | '%' -> sb.Append '\n' |> ignore
                | '~' -> sb.Append '~' |> ignore
                | other -> sb.Append c |> ignore; sb.Append other |> ignore
                i <- i + 2
            else
                sb.Append c |> ignore
                i <- i + 1
        LispStr (sb.ToString())
    | _ -> failwith "format: первый аргумент — строка-шаблон"

// --- LANG.1: хеш-таблицы с ключами по equal? ---

// Ключ хеша: структурное равенство structEqual и согласованный хеш. Рационалы приходят
// нормализованными (ридер и makeRational сокращают), поэтому 1/2 и 2/4 — один ключ;
// 1 и 1.0 — разные (как equal?). Значения с изменяемым состоянием (хеш-таблицы) ключами не бывают.

type HashKey(v: LispValue) =
    let rec hashOf (x: LispValue) : int =
        match x with
        | LispInteger n -> 17 * n.GetHashCode()
        | LispRational (p, q) ->
            // p/q могут прийти несокращёнными — нормализуем, чтобы 1/2 и 2/4 дали один хеш
            let np, nq = ratNorm (p, q)
            31 * np.GetHashCode() + nq.GetHashCode()
        | LispFloat f -> 19 * f.GetHashCode()
        | LispBool b -> if b then 23 else 29
        | LispStr s -> 37 * s.GetHashCode()
        | LispSym s -> 41 * s.GetHashCode()
        | LispNil -> 43
        | LispList xs -> xs |> List.fold (fun acc it -> acc * 47 + hashOf it) 53
        | LispVector a -> a |> Array.fold (fun acc it -> acc * 59 + hashOf it) 61
        | LispPair (a, b) -> 67 * hashOf a + hashOf b
        | LispObject o -> o.Type.GetHashCode() + (o.Fields |> Array.fold (fun acc it -> acc * 71 + hashOf it) 73)
        | _ -> 79
    member _.Value = v
    override _.Equals(other: obj) =
        match other with
        | :? HashKey as k -> structEqual v k.Value
        | _ -> false
    override _.GetHashCode() = hashOf v

// Хеш-таблица — LispObject {Type="hash"}; словарь живёт в Fields.[0] как builtin-замыкание:
// вызов с ('get k) / ('set k v) / ('has k) / ('remove k) / ('keys) / ('count) выполняет операцию
let private newHash () : LispValue =
    let d = System.Collections.Generic.Dictionary<HashKey, LispValue>()
    let core (args: LispValue list) : LispValue =
        match args with
        | [LispSym "get"; k] ->
            (match d.TryGetValue (HashKey k) with
             | true, v -> v
             | _ -> LispNil)
        | [LispSym "set"; k; v] -> d.[HashKey k] <- v; v
        | [LispSym "has"; k] -> LispBool (d.ContainsKey (HashKey k))
        | [LispSym "remove"; k] -> LispBool (d.Remove (HashKey k))
        | [LispSym "keys"] -> if d.Count = 0 then LispNil else LispList (List.ofSeq d.Keys |> List.map (fun kk -> kk.Value))
        | [LispSym "count"] -> LispInteger (bigint d.Count)
        | _ -> failwith "hash: внутренняя операция"
    LispObject { Type = "hash"; Fields = [| LispBuiltin (BuiltinFunction.Builtin core) |] }

// извлечь словарь-замыкание из таблицы
let private hashCore (who: string) (h: LispValue) : LispValue list -> LispValue =
    match h with
    | LispObject { Type = "hash"; Fields = [| LispBuiltin (BuiltinFunction.Builtin f) |] } -> f
    | _ -> failwithf "%s: ожидается хеш-таблица (make-hash), получено %s" who (Printer.prettyPrint h)

let bMakeHash (args: LispValue list) : LispValue =
    match args with
    | [] -> newHash ()
    | _ -> failwith "make-hash: без аргументов"

// (hash-ref h k [умолчание]) — значение или умолчание (по умолчанию #f)
let bHashRef (args: LispValue list) : LispValue =
    match args with
    | [h; k] ->
        match hashCore "hash-ref" h [LispSym "get"; k] with
        | LispNil -> LispBool false
        | v -> v
    | [h; k; dflt] ->
        match hashCore "hash-ref" h [LispSym "get"; k] with
        | LispNil -> dflt
        | v -> v
    | _ -> failwith "hash-ref: таблица, ключ [умолчание]"

// (hash-set! h k v) — записать значение по ключу
let bHashSet (args: LispValue list) : LispValue =
    match args with
    | [h; k; v] -> hashCore "hash-set!" h [LispSym "set"; k; v]
    | _ -> failwith "hash-set!: таблица, ключ, значение"

let bHashHas (args: LispValue list) : LispValue =
    match args with
    | [h; k] -> hashCore "hash-has?" h [LispSym "has"; k]
    | _ -> failwith "hash-has?: таблица и ключ"

let bHashRemove (args: LispValue list) : LispValue =
    match args with
    | [h; k] -> hashCore "hash-remove!" h [LispSym "remove"; k]
    | _ -> failwith "hash-remove!: таблица и ключ"

let bHashKeys (args: LispValue list) : LispValue =
    match args with
    | [h] -> hashCore "hash-keys" h [LispSym "keys"]
    | _ -> failwith "hash-keys: таблица"

let bHashCount (args: LispValue list) : LispValue =
    match args with
    | [h] -> hashCore "hash-count" h [LispSym "count"]
    | _ -> failwith "hash-count: таблица"

// --- LANG.1: числа ---

// (^ q n) для рационального q и целого n (в т.ч. отрицательного) — точно; остальное — как раньше (символьно)
let bPowExact (args: LispValue list) : LispValue =
    match args with
    | [a; b] ->
        let ratOf (v: LispValue) : (BigInteger * BigInteger) option =
            match v with
            | LispInteger n -> Some (n, 1I)
            | LispRational (p, q) -> Some (p, q)
            | _ -> None
        let fitsInt (n: BigInteger) = n.ToByteArray().Length <= 4
        match a, b with
        | LispInteger x, LispInteger e when e >= 0I && fitsInt e -> LispInteger (BigInteger.Pow(x, int e))
        | _, LispInteger ep when fitsInt ep && (ratOf a).IsSome ->
            let p, q = ratOf a |> Option.get
            let e = int ep
            if e >= 0 then makeRational (BigInteger.Pow(p, e)) (BigInteger.Pow(q, e))
            else
                if p.IsZero then failwith "^: ноль в отрицательной степени"
                makeRational (BigInteger.Pow(q, -e)) (BigInteger.Pow(p, -e))
        | _ -> LispList [LispSym "^"; a; b]
    | _ -> failwith "^: требуется два аргумента"

// abs на дроби — точная дробь (раньше — float)
let bAbsExact (args: LispValue list) : LispValue =
    match args with
    | [LispInteger n] -> LispInteger (abs n)
    | [LispRational (p, q)] -> LispRational (abs p, q)   // q > 0 по инварианту
    | [v] when isNumber v -> LispFloat (abs (toDouble v))
    | [v] -> LispList [LispSym "abs"; v]
    | _ -> failwith "abs: требуется один аргумент"

// round — к ближайшему целому (половина — от нуля, как в Scheme); truncate — к нулю; ceiling/floor уже есть
let bRound (args: LispValue list) : LispValue =
    match args with
    | [LispInteger n] -> LispInteger n
    | [LispRational (p, q)] ->
        // ближайшее целое; p/q с q > 0; |остаток|*2 >= q — от нуля
        let quot = BigInteger.Divide(p, q)
        let r = p - quot * q
        let away = (BigInteger.Abs(r) * 2I) >= q
        LispInteger (if away && not r.IsZero then (if p.Sign < 0 then quot - 1I else quot + 1I) else quot)
    | [LispFloat f] when not (System.Double.IsNaN f || System.Double.IsInfinity f) ->
        LispInteger (BigInteger (System.Math.Round(f, System.MidpointRounding.AwayFromZero)))
    | _ -> failwith "round: ожидается конечное число"

let bTruncate (args: LispValue list) : LispValue =
    match args with
    | [LispInteger n] -> LispInteger n
    | [LispRational (p, q)] -> LispInteger (BigInteger.Divide(p, q))
    | [LispFloat f] when not (System.Double.IsNaN f || System.Double.IsInfinity f) ->
        LispInteger (BigInteger (System.Math.Truncate f))
    | _ -> failwith "truncate: ожидается конечное число"

let bExactToInexact (args: LispValue list) : LispValue =
    match args with
    | [v] when isNumber v -> LispFloat (toDouble v)
    | _ -> failwith "exact->inexact: один аргумент — число"

let bEven (args: LispValue list) : LispValue =
    match args with
    | [LispInteger n] -> LispBool (n.IsEven)
    | _ -> failwith "even?: один целый аргумент"

let bOdd (args: LispValue list) : LispValue =
    match args with
    | [LispInteger n] -> LispBool ((not n.IsEven))
    | _ -> failwith "odd?: один целый аргумент"

let bZeroQ (args: LispValue list) : LispValue =
    match args with
    | [v] when isNumber v -> LispBool (numEqual v (LispInteger 0I))
    | _ -> failwith "zero?: один числовой аргумент"

// positive-number? — истина для вещественного числа > 0 (positive? занят трёхзначным предикатом CAS)
let bPositiveNumber (args: LispValue list) : LispValue =
    match args with
    | [v] when (match v with LispInteger _ | LispRational _ | LispFloat _ -> true | _ -> false) ->
        LispBool (numGreater v (LispInteger 0I))
    | _ -> failwith "positive-number?: один вещественный аргумент"

// цепочечные сравнения: (< a b c ...) — все пары соседей удовлетворяют
let private chainCompare (who: string) (op: LispValue -> LispValue -> bool) (args: LispValue list) : LispValue =
    if args.Length < 2 then failwithf "%s: требуется хотя бы два аргумента" who
    args |> List.pairwise |> List.forall (fun (a, b) -> op a b) |> LispBool

let bLessChain (args: LispValue list) : LispValue = chainCompare "<" numLess args
let bGreaterChain (args: LispValue list) : LispValue = chainCompare ">" numGreater args
let bLessEqChain (args: LispValue list) : LispValue = chainCompare "<=" numLessEq args
let bGreaterEqChain (args: LispValue list) : LispValue = chainCompare ">=" numGreaterEq args
let bNumEqChain (args: LispValue list) : LispValue = chainCompare "=" numEqual args

// --- Список всех встроенных функций ---

// Арифметика (+ - * / ^), сравнения (= < >) и sqrt регистрируются в CasBuiltins.fs:
// им нужны упроститель и алгебраические числа (каждое имя — ровно в одном месте)
let allBuiltins : (string * LispValue) list = [
    builtin "mod" bMod
    // Шаг 21c
    builtin "quotient" bQuotient
    builtin "remainder" bRemainder
    builtin "modulo" bModulo
    builtin "gcd" bGcd
    builtin "lcm" bLcm
    builtin "min" bMin
    builtin "max" bMax
    builtin "<=" bLessEqChain
    builtin ">=" bGreaterEqChain
    builtin "car" bCar
    builtin "cdr" bCdr
    builtin "cons" bCons
    builtin "assoc" bAssoc
    builtin "list" bList
    builtin "null?" bNull
    builtin "not" bNot
    builtin "display" bDisplay
    builtin "newline" bNewline
    builtin "string-append" bStrAppendStrict
    builtin "string-contains?" bStrContains
    builtin "equal?" bEqual
    builtin "sin" bSin
    builtin "cos" bCos
    builtin "tan" bTan
    builtin "cot" bCot
    builtin "sec" bSec
    builtin "csc" bCsc
    builtin "sinh" bSinh
    builtin "cosh" bCosh
    builtin "tanh" bTanh
    builtin "coth" bCoth
    builtin "sech" bSech
    builtin "csch" bCsch
    builtin "asin" bAsin
    builtin "acos" bAcos
    builtin "atan" bAtan
    builtin "acot" bAcot
    builtin "asec" bAsec
    builtin "acsc" bAcsc
    builtin "asinh" bAsinh
    builtin "acosh" bAcosh
    builtin "atanh" bAtanh
    builtin "acoth" bAcoth
    builtin "asech" bAsech
    builtin "acsch" bAcsch
    builtin "exp" bExp
    builtin "log" bLog
    builtin "ln" bLn
    builtin "abs" bAbsExact
    builtin "floor" (roundToInteger "floor" true)
    builtin "ceiling" (roundToInteger "ceiling" false)
    builtin "round" bRound
    builtin "truncate" bTruncate
    builtin "exact->inexact" bExactToInexact
    builtin "even?" bEven
    builtin "odd?" bOdd
    builtin "zero?" bZeroQ
    builtin "positive-number?" bPositiveNumber
    // Шаг 15
    builtin "length" bLength
    builtin "append" bAppend
    builtin "apply" bApply
    builtin "call-with-time-limit" bCallWithTimeLimit
    builtin "error" bError
    builtin "cadr" bCadr
    builtin "caddr" bCaddr
    builtin "cddr" bCddr
    builtin "nth" bNth
    predicate "number?" isNumber
    predicate "symbol?" (function LispSym _ -> true | _ -> false)
    predicate "list?" (function LispList _ | LispNil -> true | _ -> false)
    // Шаг 21d: pair? — точечная пара или непустой список (как в Scheme)
    predicate "pair?" (function LispPair _ | LispList (_ :: _) -> true | _ -> false)
    predicate "integer?" (function LispInteger _ -> true | _ -> false)
    // LANG.1: строки
    builtin "string-length" bStringLength
    builtin "substring" bSubstring
    builtin "string-ref" bStringRef
    builtin "string->list" bStringToList
    builtin "list->string" bListToString
    builtin "string->number" bStringToNumber
    builtin "number->string" bNumberToString
    builtin "symbol->string" bSymbolToString
    builtin "string?" bStringQ
    builtin "string=?" bStringEq
    builtin "string<?" bStringLess
    builtin "string-split" bStringSplit
    builtin "string-join" bStringJoin
    builtin "string-upcase" bStringUpcase
    builtin "string-downcase" bStringDowncase
    builtin "string-index" bStringIndex
    builtin "format" bFormat
    // LANG.1: хеш-таблицы
    builtin "make-hash" bMakeHash
    builtin "hash-ref" bHashRef
    builtin "hash-set!" bHashSet
    builtin "hash-has?" bHashHas
    builtin "hash-remove!" bHashRemove
    builtin "hash-keys" bHashKeys
    builtin "hash-count" bHashCount
]
