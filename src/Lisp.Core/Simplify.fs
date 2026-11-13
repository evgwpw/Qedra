// Упрощение символьных выражений (CAS-примитив) — КАНОНИЧЕСКАЯ ФОРМА в стиле muMath/Derive (Шаг 13)
//
// Результат simplify — каноническая форма (simplify идемпотентен: simplify (simplify e) = simplify e):
//   * только n-арные `+` и `*`, вложенные сплющены: (+ a (+ b c)) → (+ a b c)
//   * вычитание: (- a b) → (+ a (* -1 b)); унарный минус и (- 0 x) → (* -1 x)
//   * деление: (/ a b) → (* a (^ b -1)); числовые деления — сразу в рациональные числа
//   * числовая константа в сумме и числовой коэффициент в произведении стоят ПЕРВЫМИ
//     (1 + x + x^2; 2*x*y), нулевые/единичные убираются, числа свёрнуты
//   * остальные аргументы `+` и `*` отсортированы по полному порядку orderCompare/orderp
//     (числа < символы < составные; степени сравниваются по основанию, затем по показателю;
//      поэтому многочлены идут по ВОЗРАСТАНИЮ степени: 1 + x + x^2 + x^3)
//   * сбор подобных: c1*t + c2*t → (c1+c2)*t; t^a * t^b → t^(a+b) (x*x → x^2, x*x^-1 → 1)
//   * (* -1 (+ a b)) раскрывается в (+ (* -1 a) (* -1 b)) — иначе (a+b)-(a+b) не сократить;
//     прочие числовые коэффициенты на суммы НЕ распределяются (это делает expand)
//   * степени: (^ (^ x a) n) → (^ x (* a n)) для целого n; (^ (* a b) n) → (* (^ a n) (^ b n))
//     для целого n; числа: точные корни (4^(1/2) → 2), иначе символьно
//   * некоммутативные множители (объекты некоммутативных типов, векторы-массивы — isCommutative = false) не
//     переставляются друг относительно друга; коммутативные выносятся вперёд и сортируются
//   * сумма sin²u и cos²u с равными коэффициентами → константа (Пифагор), 1 - cos² → sin²
module Simplify

open System
open System.Numerics
open Types
open Numeric
open PatternMatching
open Order

// Коммутативен ли объект относительно умножения: всё, кроме LispVector и объектов
// некоммутативных типов (Шаг 14; тензоры — объекты типа tensor, Шаг 15).
// Обычные списки (в т.ч. «(a b c)») — просто выражения, никакой векторной семантики (Шаг 15)
let isCommutative (v: LispValue) : bool =
    match v with
    | LispObject o -> Objects.isCommutativeType o.Type
    | LispVector _ -> false
    | _ -> true

// Число, с которым simplify умеет считать (алгебраические числа — непрозрачные атомы:
// арифметика Numeric на них бросает исключение)
let isFoldable (v: LispValue) : bool =
    match v with
    | LispInteger _ | LispRational _ | LispFloat _ | LispComplex _ -> true
    | _ -> false

let isMinusOne (v: LispValue) : bool =
    match v with LispInteger n -> n.Equals BigInteger.MinusOne | _ -> false

let minusOne = LispInteger -1I

// Шаг 21h: упрощение (root-sum t Q E) — сумма по корням многочлена Q; реализация в RootSum.fs (нужна факторизация,
// которая собирается после Simplify.fs), поэтому хук. Устанавливается RootSum.install () при создании окружения.
let mutable rootSumHook : LispValue list -> LispValue =
    fun args -> LispList (LispSym "root-sum" :: args)


// --- Числовые степени ---

// Целый корень k-й степени из n >= 0 (floor) — бинарный поиск
let private iroot (n: BigInteger) (k: int) : BigInteger =
    if n.IsZero || n.IsOne then n
    else
        let bits = int (n.GetBitLength())
        let mutable lo = 0I
        let mutable hi = BigInteger.One <<< (bits / k + 1)
        while lo < hi do
            let mid = (lo + hi + 1I) / 2I
            if BigInteger.Pow(mid, k) <= n then lo <- mid else hi <- mid - 1I
        lo

// Рациональное число в целой степени k (база ненулевая при k < 0)
let private ratPowInt (b: LispValue) (k: int) : LispValue option =
    match b with
    | LispInteger bi when k >= 0 -> Some (LispInteger (BigInteger.Pow(bi, k)))
    | LispInteger bi -> if bi.IsZero then None else Some (makeRational 1I (BigInteger.Pow(bi, -k)))
    | LispRational (p, q) ->
        if k >= 0 then Some (makeRational (BigInteger.Pow(p, k)) (BigInteger.Pow(q, k)))
        else Some (makeRational (BigInteger.Pow(q, -k)) (BigInteger.Pow(p, -k)))
    | _ -> None

// Число в числовой степени; None — «оставить символьно»
let private numPow (b: LispValue) (e: LispValue) : LispValue option =
    let isReal v = match v with LispComplex _ -> false | _ -> true
    match b, e with
    | _, LispInteger n when BigInteger.Abs n <= 100000I ->
        let k = int n
        match b with
        | LispInteger _ | LispRational _ -> ratPowInt b k
        | LispFloat f -> if f = 0.0 && k < 0 then None else Some (LispFloat (Math.Pow(f, float k)))
        | LispComplex _ ->
            if k >= 0 then Some (List.fold (fun acc _ -> mul acc b) (LispInteger 1I) [1 .. k])
            elif isZero b then None
            else Some (div (LispInteger 1I) (List.fold (fun acc _ -> mul acc b) (LispInteger 1I) [1 .. -k]))
        | _ -> None
    | (LispInteger _ | LispRational _), LispRational (p, q) when q <= 1000I && BigInteger.Abs p <= 100000I ->
        // точный корень: (n/d)^(p/q) = ((n/d)^(1/q))^p, если и n, и d — точные q-е степени
        let n, d = match b with
                   | LispInteger bi -> bi, 1I
                   | LispRational (x, y) -> x, y
                   | _ -> 0I, 1I
        if n.Sign <= 0 then None
        else
            let qi = int q
            let rn, rd = iroot n qi, iroot d qi
            if BigInteger.Pow(rn, qi) = n && BigInteger.Pow(rd, qi) = d then
                ratPowInt (makeRational rn rd) (int p)
            else None
    | _ when isReal b && isReal e && (match b, e with
                                      | LispFloat _, _ | _, LispFloat _ -> true
                                      | _ -> false) ->
        let bf, ef = toFloat b, toFloat e
        if bf < 0.0 && ef <> Math.Floor ef then None
        else
            let r = Math.Pow(bf, ef)
            if Double.IsNaN r || Double.IsInfinity r then None else Some (LispFloat r)
    | _ -> None

// Шаг 21c: разложение на простые пробным делением — только для n <= 10^12 (≤ 10^6 делений);
// больше — None («не раскладывать гигантские числа»)
let private factorLimit = 1_000_000_000_000I

let private factorSmall (n: BigInteger) : (BigInteger * int) list option =
    if n.Sign <= 0 || n > factorLimit then None
    else
        let mutable r = uint64 n
        let res = ResizeArray<BigInteger * int>()
        let mutable d = 2UL
        while d * d <= r do
            if r % d = 0UL then
                let mutable c = 0
                while r % d = 0UL do
                    r <- r / d
                    c <- c + 1
                res.Add (BigInteger d, c)
            d <- if d = 2UL then 3UL else d + 2UL
        if r > 1UL then res.Add (BigInteger r, 1)
        Some (List.ofSeq res)

// Положительное рациональное n/d в рациональной степени p/q (q > 1, p/q несократима, дробная):
//   (n/d)^(p/q) = (n/d)^k · (n/d)^(p'/q),  k = floor(p/q), 0 < p' < q;
//   (n/d)^(p'/q) = (1/d) · (n^p' · d^(q-p'))^(1/q)   — знаменатель рационализирован;
// из подкоренного N вынесены все полные q-е степени, затем показатель корня и степени простых
// сокращены на общий НОД: 4^(1/4) → 2^(1/2). Результат: (рациональный множитель, None | Some (m, q'))
// означает множитель · m^(1/q'), где m > 1 — целое, q' > 1. None — раскладывать нельзя (числа велики)
let private extractRoot (n: BigInteger) (d: BigInteger) (p: BigInteger) (q: BigInteger)
        : (LispValue * (BigInteger * BigInteger) option) option =
    match factorSmall n, factorSmall d with
    | Some fn, Some fd ->
        let k = BigInteger.Divide(p - (if p.Sign < 0 then q - 1I else 0I), q)
        let p1 = p - k * q
        // показатели простых в N = n^p1 · d^(q-p1)
        let exps = Collections.Generic.Dictionary<BigInteger, BigInteger>()
        let addExp (pr: BigInteger) (e: BigInteger) =
            exps.[pr] <- (match exps.TryGetValue pr with | true, x -> x + e | _ -> e)
        for (pr, a) in fn do addExp pr (BigInteger a * p1)
        for (pr, b) in fd do addExp pr (BigInteger b * (q - p1))
        let mutable outside = LispInteger 1I      // множитель вне корня
        let mutable g = q                          // НОД q и остатков показателей
        let rems = ResizeArray<BigInteger * BigInteger>()
        for kv in exps do
            let u = BigInteger.Divide(kv.Value, q)
            let v = kv.Value - u * q
            if not u.IsZero then outside <- mul outside (LispInteger (BigInteger.Pow(kv.Key, int u)))
            if not v.IsZero then
                rems.Add (kv.Key, v)
                g <- BigInteger.GreatestCommonDivisor(g, v)
        // 1/d и (n/d)^k
        let baseR = makeRational n d
        let withK = match ratPowInt baseR (int k) with Some r -> r | None -> LispInteger 1I
        let outside2 = mul (mul outside (makeRational 1I d)) withK
        if rems.Count = 0 then Some (outside2, None)
        else
            let m = rems |> Seq.fold (fun acc (pr, v) -> acc * BigInteger.Pow(pr, int (v / g))) 1I
            Some (outside2, Some (m, q / g))
    | _ -> None

// Вызов метода op по типам аргументов (Objects.findMethod): сырой результат или None.
// Используется ТОЛЬКО когда среди аргументов есть объект/вектор (Шаг 14)
let private callMethod (op: string) (args: LispValue list) : LispValue option =
    match Objects.findMethod op (args |> List.map Objects.typeOf) with
    | Some fn ->
        let r = Objects.applyHook fn args
        if Debug.simpTracing then Debug.simpStep ("method:" + op) (LispList (LispSym op :: args)) r
        Some r
    | None -> None

// Триг-переписывание: правила до фикспоинта, затем повторное упрощение,
// если что-то изменилось (обратных правил нет — цикл завершается)
let rec rewriteTrig (e: LispValue) : LispValue =
    let rewritten = rewriteUntilFixpoint trigRules e
    if structEqual rewritten e then e
    else
        if Debug.simpTracing then Debug.simpStep "trig-rules" e rewritten
        simplify rewritten

// Рекурсивное упрощение одного выражения → каноническая форма
and simplify (expr: LispValue) : LispValue =
    // Шаг 15b: защита от переполнения стека — исключение вместо падения процесса (eval превратит в LispError)
    Debug.checkStack ()
    match expr with
    | LispList (head :: args) ->
        let simpArgs = List.map simplify args
        let result =
            match head with
            | LispSym "+" -> simplifySum simpArgs
            | LispSym "-" -> simplifySub simpArgs
            | LispSym "*" -> simplifyMul simpArgs
            | LispSym "/" -> simplifyDiv simpArgs
            | LispSym "^" -> simplifyPow simpArgs
            // ln → log (нормализация)
            | LispSym "ln" ->
                let r =
                    match simpArgs with
                    | [u] -> LispList [LispSym "log"; u]
                    | _ -> LispList (LispSym "log" :: simpArgs)
                if Debug.simpTracing then Debug.simpStep "ln-to-log" (LispList (head :: simpArgs)) r
                r
            // Шаг 18: sqrt отрицательного рационального числа → %i · sqrt|a| (точный корень, если он есть)
            | LispSym "sqrt" when (match simpArgs with
                                   | [(LispInteger _ | LispRational _) as a] -> compareNum a (LispInteger 0I) < 0
                                   | _ -> false) ->
                let pos = simplifyMul [minusOne; simpArgs.Head]
                let r = simplifyMul [LispSym "%i"; simplifyPow [pos; makeRational 1I 2I]]
                if Debug.simpTracing then Debug.simpStep "sqrt-negative" (LispList (head :: simpArgs)) r
                r
            // Шаг 21c: sqrt положительного рационального числа — как (^ a 1/2) (точный корень, вынос квадратов)
            | LispSym "sqrt" when (match simpArgs with
                                   | [(LispInteger _ | LispRational _) as a] -> compareNum a (LispInteger 0I) >= 0
                                   | _ -> false) ->
                let r = simplifyPow [simpArgs.Head; makeRational 1I 2I]
                if Debug.simpTracing then Debug.simpStep "sqrt-rational" (LispList (head :: simpArgs)) r
                r
            // Шаг 21h: сумма по корням многочлена — каноническая форма (RootSum.fs)
            | LispSym "root-sum" when simpArgs.Length = 3 -> rootSumHook simpArgs
            // Шаг 14: прочие операторы над объектами — диспетчеризация по типам всех аргументов;
            // нет метода — символьная форма (никаких исключений)
            | LispSym op when simpArgs |> List.exists Objects.needsDispatch ->
                match callMethod op simpArgs with
                | Some r -> simplify r
                | None -> LispList (head :: simpArgs)
            // Шаг 21l.0: комбинаторные головы — точные значения на числовых аргументах
            | LispSym op when (match op with "binomial" | "gamma" | "rf" | "ff" | "harmonic" | "bernoulli" -> true | _ -> false) ->
                let r = combinatorValue op simpArgs
                if Debug.simpTracing then
                    (match r with Some v -> Debug.simpStep "combinatorial-value" (LispList (head :: simpArgs)) v | None -> ())
                (match r with Some v -> v | None -> LispList (head :: simpArgs))
            // Шаг 21c: точные значения элементарных функций в особых точках
            | LispSym f ->
                match simpArgs with
                | [a] ->
                    match exactValue f a with
                    | Some v -> v
                    | None -> LispList (head :: simpArgs)
                | _ -> LispList (head :: simpArgs)
            | _ -> LispList (simplify head :: simpArgs)
        applyUserRules (rewriteTrig result)
    | LispList [] -> LispNil
    | LispAlgebraic _ -> expr  // алгебраические числа уже упрощены
    // Шаг 14: объект — метод (simplify type), иначе как есть; вектор — поэлементно
    | LispObject o ->
        match Objects.findMethod "simplify" [o.Type] with
        | Some fn -> Objects.applyHook fn [expr]
        | None -> expr
    | LispVector items -> LispVector (Array.map simplify items)
    | _ -> expr

// Шаг 16: пользовательские условные правила (defrule). Нет правил для оператора — только проверка
// словаря. Первое сработавшее правило → замена упрощается заново; глубина цепочки переписываний
// ограничена (Rules.enter), иначе правила a→b, b→a зациклились бы
and private applyUserRules (e: LispValue) : LispValue =
    match e with
    | LispList (LispSym op :: _) when Rules.hasRules op ->
        match Rules.tryRewrite op e with
        | Some (rule, replaced, b) ->
            if Rules.tracing then Rules.traceFired rule e replaced
            if Debug.simpTracing then
                Debug.simpStepT ("rule:" + rule.Name) rule.Title (if rule.Ac then Rules.acComment rule.Pattern b else "") e replaced
            Rules.enter rule
            try simplify replaced
            finally Rules.leave ()
        | None -> e
    | _ -> e

// --- Сумма ---

// Терм → (числовой коэффициент, остаток): (* 3 x y) → (3, (* x y)); x → (1, x)
and private splitCoeff (t: LispValue) : LispValue * LispValue =
    match t with
    | LispList (LispSym "*" :: n :: rest) when isFoldable n && not rest.IsEmpty ->
        (n, (match rest with [r] -> r | _ -> LispList (LispSym "*" :: rest)))
    | _ -> (LispInteger 1I, t)

// Коэффициент × остаток → терм (остаток уже канонический и не число)
and private attach (c: LispValue) (r: LispValue) : LispValue =
    if isOne c then r
    else
        match r with
        | LispList (LispSym "+" :: _) when isMinusOne c -> simplifyMul [c; r]
        | LispList (LispSym "*" :: xs) -> LispList (LispSym "*" :: c :: xs)
        | _ -> LispList [LispSym "*"; c; r]

// Пифагоровы свёртки в сумме: c*sin²u + c*cos²u → c; k - k*cos²u → k*sin²u; k - k*sin²u → k*cos²u.
// Работает на разобранной сумме (константа, [(коэффициент, остаток)]); None — ничего не сделано
and private pythag (c0: LispValue) (groups: (LispValue * LispValue) list)
        : (LispValue * (LispValue * LispValue) list) option =
    let trigSq (fn: string) (r: LispValue) : LispValue option =
        match r with
        | LispList [LispSym "^"; LispList [LispSym f; u]; LispInteger two] when f = fn && two = 2I -> Some u
        | _ -> None
    let find fn u =
        groups |> List.tryFind (fun (_, r) ->
            match trigSq fn r with Some v -> structEqual u v | None -> false)
    let without (items: (LispValue * LispValue) list) =
        groups |> List.filter (fun g -> not (items |> List.exists (fun i -> obj.ReferenceEquals(i, g))))
    let sinGroups = groups |> List.choose (fun ((_, r) as g) -> trigSq "sin" r |> Option.map (fun u -> (u, g)))
    // 1) sin² и cos² с равными коэффициентами
    let rule1 =
        sinGroups |> List.tryPick (fun (u, sg) ->
            match find "cos" u with
            | Some cg when structEqual (fst sg) (fst cg) -> Some (add c0 (fst sg), without [sg; cg])
            | _ -> None)
    match rule1 with
    | Some r -> Some r
    | None ->
        if isZero c0 then None
        else
            let sq fn u = LispList [LispSym "^"; LispList [LispSym fn; u]; LispInteger 2I]
            // 2) константа k и -k*cos²u → k*sin²u (и наоборот)
            let conv (fromFn: string) (toFn: string) =
                groups |> List.tryPick (fun ((c, r) as g) ->
                    match trigSq fromFn r with
                    | Some u when isZero (add c0 c) ->
                        Some (LispInteger 0I,
                              (c0, sq toFn u) :: (groups |> List.filter (fun x -> not (obj.ReferenceEquals(x, g)))))
                    | _ -> None)
            match conv "cos" "sin" with
            | Some r -> Some r
            | None -> conv "sin" "cos"

and simplifySum (args: LispValue list) : LispValue =
    let flat0 = args |> List.collect (fun a ->
                    match a with LispList (LispSym "+" :: xs) -> xs | _ -> [a])
    // Шаг 14: сворачивание объектов по методам (+ t1 t2); может сразу дать итог
    match (if flat0 |> List.exists Objects.needsDispatch then reduceObjectSum flat0 else Choice2Of2 flat0) with
    | Choice1Of2 final -> final
    | Choice2Of2 flat -> simplifySumPlain flat

// Свёртка объектов в сумме: пары (i, j) с методом (+ ti tj) заменяются результатом;
// затем скаляр + единственный объект по методу (+ tскаляра t). Нет метода — термы остаются
and private reduceObjectSum (flat: LispValue list) : Choice<LispValue, LispValue list> =
    let mutable items = flat
    let mutable changed = true
    while changed do
        changed <- false
        let arr = Array.ofList items
        let objs = [ for i in 0 .. arr.Length - 1 do if Objects.needsDispatch arr.[i] then yield i ]
        let pair =
            [ for i in objs do for j in objs do if i < j then yield (i, j) ]
            |> List.tryPick (fun (i, j) ->
                match callMethod "+" [arr.[i]; arr.[j]] with
                | Some r -> Some (i, j, r)
                | None ->
                    match callMethod "+" [arr.[j]; arr.[i]] with
                    | Some r -> Some (i, j, r)
                    | None -> None)
        match pair with
        | Some (i, j, r) ->
            let rs = simplify r
            let rest = arr |> Array.indexed |> Array.filter (fun (k, _) -> k <> i && k <> j) |> Array.map snd |> List.ofArray
            let rsItems = match rs with LispList (LispSym "+" :: xs) -> xs | _ -> [rs]
            items <- rest @ rsItems
            changed <- true
        | None -> ()
    let objs, others = items |> List.partition Objects.needsDispatch
    match objs with
    | [o] when not others.IsEmpty ->
        let s = simplifySum others
        if isFoldable s && isZero s then Choice2Of2 items
        else
            match callMethod "+" [s; o] with
            | Some r -> Choice1Of2 (simplify r)
            | None ->
                match callMethod "+" [o; s] with
                | Some r -> Choice1Of2 (simplify r)
                | None -> Choice2Of2 items
    | _ -> Choice2Of2 items

and private simplifySumPlain (flat: LispValue list) : LispValue =
    let nums, others = flat |> List.partition isFoldable
    let c0 = nums |> List.fold add (LispInteger 0I)
    // группировка подобных: (коэффициент, остаток), порядок первого появления
    let groups = ResizeArray<LispValue * LispValue>()
    let mutable merged = false      // Шаг 21d: сработал сбор подобных (трассировка)
    for t in others do
        let c, r = splitCoeff t
        match groups |> Seq.tryFindIndex (fun (_, r2) -> structEqual r r2) with
        | Some i ->
            merged <- true
            groups.[i] <- (add (fst groups.[i]) c, snd groups.[i])
        | None -> groups.Add (c, r)
    let live = groups |> Seq.filter (fun (c, _) -> not (isZero c)) |> List.ofSeq
    let result =
        match pythag c0 live with
        | Some (c1, live2) ->
            let r = simplifySum (c1 :: (live2 |> List.map (fun (c, r) -> attach c r)))
            if Debug.simpTracing then Debug.simpStep "pythagorean" (LispList (LispSym "+" :: flat)) r
            r
        | None ->
            let sorted = live |> List.sortWith (fun (_, r1) (_, r2) -> orderCompare r1 r2)
            let terms = sorted |> List.map (fun (c, r) -> attach c r)
            if terms |> List.exists (fun t -> match t with LispList (LispSym "+" :: _) -> true | _ -> false) then
                simplifySum (c0 :: terms)   // распределение -1 дало суммы — пересобрать
            else
                let items = (if isZero c0 then [] else [c0]) @ terms
                match items with
                | [] -> LispInteger 0I
                | [single] -> single
                | _ -> LispList (LispSym "+" :: items)
    if merged && Debug.simpTracing then Debug.simpStep "collect-terms" (LispList (LispSym "+" :: flat)) result
    result

// (- a b c) → a + (-1)*b + (-1)*c; (- a) → (-1)*a
and simplifySub (args: LispValue list) : LispValue =
    match args with
    | [] -> LispInteger 0I
    | [single] -> simplifyMul [minusOne; single]
    | a :: rest -> simplifySum (a :: (rest |> List.map (fun b -> simplifyMul [minusOne; b])))

// --- Произведение ---

and simplifyMul (args: LispValue list) : LispValue =
    let flat = args |> List.collect (fun a ->
                    match a with LispList (LispSym "*" :: xs) -> xs | _ -> [a])
    // Шаг 14: свёртка по методам (* t1 t2) только если среди множителей есть объект/вектор
    let reduced = if flat |> List.exists Objects.needsDispatch then reduceObjectMul flat else None
    match reduced with
    | Some r -> r
    | None -> simplifyMulPlain flat

// Свёртка объектов в произведении. Некоммутативные множители сохраняют порядок:
// 1) соседние некоммутативные (и любые пары коммутативных объектов) по методу (* ta tb);
// 2) скаляр S (произведение необъектных коммутативных) × первый объект по методу (* tS t).
// None — подходящих методов нет, остаётся символьная форма
and private reduceObjectMul (flat: LispValue list) : LispValue option =
    if flat |> List.exists (fun a -> isFoldable a && isZero a) then None
    else
        let comm, noncomm = flat |> List.partition isCommutative
        let carr = Array.ofList comm
        let cobjs = [ for i in 0 .. carr.Length - 1 do if Objects.needsDispatch carr.[i] then yield i ]
        let commPair =
            [ for i in cobjs do for j in cobjs do if i < j then yield (i, j) ]
            |> List.tryPick (fun (i, j) ->
                match callMethod "*" [carr.[i]; carr.[j]] with
                | Some r -> Some (i, j, r)
                | None ->
                    match callMethod "*" [carr.[j]; carr.[i]] with
                    | Some r -> Some (i, j, r)
                    | None -> None)
        match commPair with
        | Some (i, j, r) ->
            let rest = carr |> Array.indexed |> Array.filter (fun (k, _) -> k <> i && k <> j) |> Array.map snd |> List.ofArray
            Some (simplifyMul (simplify r :: rest @ noncomm))
        | None ->
            let narr = Array.ofList noncomm
            let adj =
                [ 0 .. narr.Length - 2 ]
                |> List.tryPick (fun p ->
                    if Objects.needsDispatch narr.[p] || Objects.needsDispatch narr.[p + 1] then
                        callMethod "*" [narr.[p]; narr.[p + 1]] |> Option.map (fun r -> (p, r))
                    else None)
            match adj with
            | Some (p, r) ->
                let before = List.take p noncomm
                let after = List.skip (p + 2) noncomm
                Some (simplifyMul (comm @ before @ [simplify r] @ after))
            | None ->
                // скаляр × первый объект
                let scalars = comm |> List.filter (fun a -> not (Objects.needsDispatch a))
                let keep = comm |> List.filter Objects.needsDispatch
                match narr |> Array.tryFindIndex Objects.needsDispatch with
                | Some k when not scalars.IsEmpty ->
                    let s = simplifyMul scalars
                    if isFoldable s && isOne s then None
                    else
                        match callMethod "*" [s; narr.[k]] with
                        | Some r ->
                            let nc = noncomm |> List.mapi (fun idx v -> if idx = k then simplify r else v)
                            Some (simplifyMul (keep @ nc))
                        | None -> None
                // Шаг 15a: нет некоммутативных объектов — скаляр × первый КОММУТАТИВНЫЙ объект
                // (так сворачиваются (* 2 alg), (* -1 alg) для алгебраических чисел)
                | None when not scalars.IsEmpty && not keep.IsEmpty ->
                    let s = simplifyMul scalars
                    if isFoldable s && isOne s then None
                    else
                        match callMethod "*" [s; keep.Head] with
                        | Some r -> Some (simplifyMul (simplify r :: keep.Tail @ noncomm))
                        | None -> None
                | _ -> None

and private simplifyMulPlain (flat: LispValue list) : LispValue =
    if flat |> List.exists (fun a -> isFoldable a && isZero a) then LispInteger 0I
    else
        let comm, noncomm = flat |> List.partition isCommutative
        let nums, others = comm |> List.partition isFoldable
        let coeff = nums |> List.fold mul (LispInteger 1I)
        if isZero coeff then LispInteger 0I
        else
            // Шаг 21c: exp(a)·exp(b) → exp(a+b)
            let isExp f = match f with LispList [LispSym "exp"; _] -> true | _ -> false
            if (others |> List.filter isExp |> List.length) >= 2 then
                let expArgs = others |> List.choose (fun f -> match f with LispList [LispSym "exp"; u] -> Some u | _ -> None)
                let rest = others |> List.filter (fun f -> not (isExp f))
                let merged = makeFun "exp" (simplifySum expArgs)
                if Debug.simpTracing then
                    Debug.simpStep "exp-merge" (LispList (LispSym "*" :: (others |> List.filter isExp))) merged
                simplifyMul (coeff :: merged :: rest @ noncomm)
            else mulGrouped coeff others noncomm

// Шаг TIDY.3: множители m^(p/q) (m > 1 целое, дробный рациональный показатель), у которых есть общие простые
// делители, пересобираются: показатели простых складываются, целая часть уходит в рациональный множитель,
// дробные части с одним знаменателем собираются под один корень (2^(1/2)·8^(1/4) → 2·2^(1/4)).
// Без общих простых (√2·√3) и при невозможности разложить — None (форма не меняется)
and private mergeRadicals (others: LispValue list) : (LispValue * LispValue list * LispValue list) option =
    let isRad f =
        match f with
        | LispList [LispSym "^"; LispInteger m; LispRational _] when m > 1I -> true
        | _ -> false
    let rads = others |> List.filter isRad
    if rads.Length < 2 then None
    else
        let facs =
            rads |> List.map (fun f ->
                match f with
                | LispList [LispSym "^"; LispInteger m; LispRational (p, q)] ->
                    factorSmall m |> Option.map (fun fm -> fm |> List.map (fun (pr, c) -> pr, BigInteger c * p, q))
                | _ -> None)
        if facs |> List.exists Option.isNone then None
        else
            let facs = facs |> List.map Option.get
            let seen = Collections.Generic.HashSet<BigInteger>()
            let overlap =
                facs |> List.exists (fun fm ->
                    fm |> List.exists (fun (pr, _, _) -> not (seen.Add pr)))
            // повторный простой внутри одного множителя невозможен (разложение), так что seen.Add ловит только пересечения
            if not overlap then None
            else
                // суммируем показатели: простое -> (числитель, знаменатель)
                let tot = Collections.Generic.SortedDictionary<BigInteger, BigInteger * BigInteger>()
                for fm in facs do
                    for (pr, n, d) in fm do
                        match tot.TryGetValue pr with
                        | true, (n0, d0) ->
                            let nn, dd = n0 * d + n * d0, d0 * d
                            let g = BigInteger.GreatestCommonDivisor(nn, dd)
                            let g = if g.IsZero then 1I else g
                            tot.[pr] <- (nn / g, dd / g)
                        | _ -> tot.[pr] <- (n, d)
                let mutable coef = LispInteger 1I
                let byDen = Collections.Generic.SortedDictionary<BigInteger, BigInteger>()   // знаменатель -> произведение p^a
                for kv in tot do
                    let pr = kv.Key
                    let (n, d) = kv.Value
                    let k = BigInteger.Divide(n - (if n.Sign < 0 then d - 1I else 0I), d)   // floor
                    let a = n - k * d
                    if not k.IsZero then
                        coef <- mul coef (numPow (LispInteger pr) (LispInteger k) |> Option.defaultValue (LispInteger 1I))
                    if a.Sign > 0 then
                        let cur = match byDen.TryGetValue d with | true, v -> v | _ -> 1I
                        byDen.[d] <- cur * BigInteger.Pow(pr, int a)
                let radFactors = byDen |> Seq.map (fun kv -> simplifyPow [LispInteger kv.Value; makeRational 1I kv.Key]) |> List.ofSeq
                Some (coef, radFactors, others |> List.filter (fun f -> not (isRad f)))

and private mulGrouped (coeff: LispValue) (others: LispValue list) (noncomm: LispValue list) : LispValue =
    match mergeRadicals others with
    | Some (c, radFactors, rest) -> simplifyMul (coeff :: c :: radFactors @ rest @ noncomm)
    | None ->
            // группировка по основанию: t^a * t^b → t^(a+b)
            let groups = ResizeArray<LispValue * LispValue list * LispValue>()  // (основание, показатели, исходный множитель)
            for f in others do
                let b, e =
                    match f with
                    | LispList [LispSym "^"; b; e] -> b, e
                    | _ -> f, LispInteger 1I
                match groups |> Seq.tryFindIndex (fun (b2, _, _) -> structEqual b b2) with
                | Some i -> (let (b2, es, f2) = groups.[i] in groups.[i] <- (b2, es @ [e], f2))
                | None -> groups.Add (b, [e], f)
            let merged = groups |> Seq.exists (fun (_, es, _) -> es.Length > 1)
            if merged then
                let factors =
                    groups |> Seq.map (fun (b, es, f) ->
                        match es with
                        | [_] -> f
                        | _ -> simplifyPow [b; simplifySum es]) |> List.ofSeq
                let r = simplifyMul (coeff :: factors @ noncomm)
                if Debug.simpTracing then Debug.simpStep "merge-powers" (LispList (LispSym "*" :: others)) r
                r
            else
                let sorted = others |> List.sortWith orderCompare
                match noncomm, sorted with
                | [], [LispList (LispSym "+" :: ts) as s] when isMinusOne coeff ->
                    let r = simplifySum (ts |> List.map (fun t -> simplifyMul [minusOne; t]))
                    if Debug.simpTracing then Debug.simpStep "distribute-minus" (LispList [LispSym "*"; minusOne; s]) r
                    r
                | _ ->
                    let items = (if isOne coeff then [] else [coeff]) @ sorted @ noncomm
                    match items with
                    | [] -> LispInteger 1I
                    | [single] -> single
                    | _ -> LispList (LispSym "*" :: items)

// (/ a b c) → a * b^-1 * c^-1
and simplifyDiv (args: LispValue list) : LispValue =
    match args with
    | [] -> LispInteger 1I
    | [single] -> simplifyPow [single; minusOne]
    | a :: rest -> simplifyMul (a :: (rest |> List.map (fun b -> simplifyPow [b; minusOne])))

// --- Точные значения элементарных функций (Шаг 21c) ---
// Числовые значения — здесь, в ядре; параметрические (n целое по декларации: sin(nπ)) — правила lib\rules.lisp.
// Полюса (tan(π/2), cot(0), sec(π/2), csc(0)) и log(0) не трогаются.

// a = r·π (r рационально; a = 0 даёт r = 0) → r
and private piMultiple (a: LispValue) : LispValue option =
    match a with
    | LispSym "pi" -> Some (LispInteger 1I)
    | LispInteger z when z.IsZero -> Some a
    | LispList [LispSym "*"; (LispInteger _ | LispRational _) as r; LispSym "pi"] -> Some r
    | _ -> None

// sin и cos угла j·15° (j = 0..23; допустимы кратные 30° и 45°): значения в канонической форме
and private sinCosAt (j: int) : LispValue * LispValue =
    let half = makeRational 1I 2I
    let baseSin (a: int) =   // sin угла a градусов из {0, 30, 45, 60, 90}
        match a with
        | 0 -> LispInteger 0I
        | 30 -> half
        | 45 -> simplifyMul [half; simplifyPow [LispInteger 2I; half]]
        | 60 -> simplifyMul [half; simplifyPow [LispInteger 3I; half]]
        | _ -> LispInteger 1I
    let sinDeg (a0: int) =
        let a = ((a0 % 360) + 360) % 360
        if a <= 90 then baseSin a
        elif a <= 180 then baseSin (180 - a)
        elif a <= 270 then simplifyMul [minusOne; baseSin (a - 180)]
        else simplifyMul [minusOne; baseSin (360 - a)]
    let deg = 15 * j
    sinDeg deg, sinDeg (deg + 90)

and private exactValue (f: string) (a: LispValue) : LispValue option =
    // быстрый выход: подходят только целые, pi, r·pi и (exp c)
    match a with
    | LispInteger _ | LispSym "pi" | LispList [LispSym "*"; (LispInteger _ | LispRational _); LispSym "pi"]
    | LispList [LispSym "exp"; _] ->
        let r = exactValueSlow f a
        (match r with
         | Some v when Debug.simpTracing -> Debug.simpStep "exact-value" (LispList [LispSym f; a]) v
         | _ -> ())
        r
    | _ -> None

and private exactValueSlow (f: string) (a: LispValue) : LispValue option =
    let some v = Some v
    let zero = LispInteger 0I
    let one = LispInteger 1I
    let pi = LispSym "pi"
    let isNum n = match a with LispInteger x -> x = BigInteger (n: int) | _ -> false
    match f with
    | "exp" -> if isNum 0 then some one else None
    | "log" ->
        match a with
        | LispInteger x when x.IsOne -> some zero
        // log(exp(c)) = c для вещественного рационального c (ветвь не затрагивается)
        | LispList [LispSym "exp"; ((LispInteger _ | LispRational _) as c)] -> some c
        | _ -> None
    | "sinh" | "tanh" | "asin" | "atan" | "asinh" | "atanh" ->
        if isNum 0 then
            some zero
        else
            match f, a with
            | "atan", LispInteger x when x.IsOne -> some (simplifyMul [makeRational 1I 4I; pi])
            | "atan", LispInteger x when x = -1I -> some (simplifyMul [makeRational -1I 4I; pi])
            | "asin", LispInteger x when x.IsOne -> some (simplifyMul [makeRational 1I 2I; pi])
            | "asin", LispInteger x when x = -1I -> some (simplifyMul [makeRational -1I 2I; pi])
            | _ -> None
    | "cosh" | "sech" -> if isNum 0 then some one else None
    | "acos" ->
        if isNum 0 then some (simplifyMul [makeRational 1I 2I; pi])
        elif isNum 1 then some zero
        elif isNum -1 then some pi
        else None
    | "acot" -> if isNum 0 then some (simplifyMul [makeRational 1I 2I; pi]) else None
    | "acosh" -> if isNum 1 then some zero else None
    | "sin" | "cos" | "tan" | "cot" | "sec" | "csc" ->
        match piMultiple a with
        | None -> None
        | Some r ->
            let num, den = match r with
                           | LispInteger n -> n, 1I
                           | LispRational (n, d) -> n, d
                           | _ -> 0I, 1I
            // угол в единицах 15°: 12·r (по модулю 24); допустимы знаменатели 1, 2, 3, 4, 6
            let t = 12I * num
            if not (BigInteger.Remainder(t, den)).IsZero then None
            else
                let j = int (((BigInteger.Divide(t, den) % 24I) + 24I) % 24I)
                if j % 2 <> 0 && j % 3 <> 0 then None
                else
                    let s, c = sinCosAt j
                    let isZ v = isFoldable v && isZero v
                    let ratio x y = if isZ y then None else some (simplifyMul [x; simplifyPow [y; minusOne]])
                    match f with
                    | "sin" -> some s
                    | "cos" -> some c
                    | "tan" -> ratio s c
                    | "cot" -> ratio c s
                    | "sec" -> ratio one c
                    | _ -> ratio one s
    | _ -> None

// --- Шаг 21l.0: комбинаторные головы (binomial, gamma, rf/ff, harmonic, bernoulli, psi) ---
// Точные значения на целых/рациональных аргументах; None — оставить символьную форму.
// ψ точных значений не имеет (входит константа Эйлера γ) — только числа в eval-num (SolveNum).

// Целое/рациональное → (числитель, знаменатель); None — не число
and private ratParts (v: LispValue) : (BigInteger * BigInteger) option =
    match v with
    | LispInteger n -> Some (n, 1I)
    | LispRational (p, q) -> Some (p, q)
    | _ -> None

// C(n, k) для целых 0 ≤ k ≤ n — BigInteger
and private binomInt (n: BigInteger) (k: BigInteger) : BigInteger =
    let k = if k > n - k then n - k else k
    let mutable r = 1I
    for i in 1I .. k do r <- r * (n - k + i) / i
    r

// Факториал BigInteger (n ≥ 0)
and factorialBig (n: BigInteger) : BigInteger =
    let mutable r = 1I
    for i in 2I .. n do r <- r * i
    r

// Числа Бернулли B_0..B_60 (рекуррентность; B_1 = −1/2, нечётные > 1 — нули в таблицу не пишем)
and private bernoulliTable : Lazy<Map<int, BigInteger * BigInteger>> =
    lazy (
        let res = ResizeArray<BigInteger * BigInteger>()
        for n in 0 .. 60 do
            if n = 0 then res.Add (1I, 1I)
            elif n = 1 then res.Add (-1I, 2I)
            else
                let mutable acc = 0I, 1I       // дробь (p, q)
                // Σ_{m=0}^{n−1} C(n+1, m)·B_m = 0  →  B_n = −Σ/(n+1)
                for m in 0 .. n - 1 do
                    let c = binomInt (BigInteger (n + 1)) (BigInteger m)
                    let bp, bq = res.[m]
                    acc <- (fst acc * bq + bp * c * snd acc, snd acc * bq)
                let p, q = acc
                let a, b = -p, BigInteger (n + 1) * q
                let g = BigInteger.GreatestCommonDivisor (BigInteger.Abs a, b)
                let a, b = if g.IsZero then a, b else a / g, b / g
                res.Add (if b < 0I then -a, -b else a, b)
        Map.ofList [ for i in 0 .. res.Count - 1 -> i, res.[i] ])

// Гармонические числа H_{n,m} = Σ 1/k^m — точный рационал; предел по росту знаменателя
and private harmonicLimit = 120

and private harmonicRat (n: BigInteger) (m: BigInteger) : LispValue =
    let mutable p, q = 0I, 1I
    for k in 1I .. n do
        let kp = BigInteger.Pow (k, int m)
        p <- p * kp + q
        q <- q * kp
        let g = BigInteger.GreatestCommonDivisor (BigInteger.Abs p, q)
        if g > 1I then p <- p / g; q <- q / g
    makeRational p q

// Точные значения комбинаторных голов; None — символьная форма
and private combinatorValue (op: string) (args: LispValue list) : LispValue option =
    let intArg (v: LispValue) = match v with LispInteger n -> Some n | _ -> None
    match op, args with
    // C(n, k): целые n, k; k < 0 или k > n → 0
    | "binomial", [n; k] ->
        (match intArg n, intArg k with
         | Some _, Some k' when k'.Sign < 0 -> Some (LispInteger 0I)
         // n < 0 (обобщённый биномиальный коэффициент): C(n, k) = (−1)^k·C(k − n − 1, k)
         | Some n', Some k' when n'.Sign < 0 ->
             let c = binomInt (k' - n' - 1I) k'
             Some (LispInteger (if k'.IsEven then c else -c))
         | Some n', Some k' when k' > n' -> Some (LispInteger 0I)
         | Some n', Some k' -> Some (LispInteger (binomInt n' k'))
         | _ -> None)
    // Γ(n) = (n−1)! для целых n ≥ 1 (n ≤ 5001); полюсы и прочее — символьно
    | "gamma", [x] ->
        (match intArg x with
         | Some n when n >= 1I && n <= 5001I -> Some (LispInteger (factorialBig (n - 1I)))
         | _ -> None)
    // (a)_k (rf) и (a)‾k (ff): k — целое 0 ≤ k ≤ 200, a — целое или рациональное → точный рационал
    | ("rf" | "ff"), [a; k] ->
        (match intArg k with
         | Some k' when k' >= 0I && k' <= 200I ->
             (match ratParts a with
              | Some (p, q) ->
                  let down = op = "ff"
                  let mutable num, den = 1I, 1I
                  for i in 0I .. k' - 1I do
                      let s = if down then p - i * q else p + i * q
                      num <- num * s
                      den <- den * q
                  if den.IsZero then None else Some (makeRational num den)
              | None -> None)
         | _ -> None)
    // H_n / H_{n,m}: точные рационалы для целых n ≥ 0 (n ≤ 120), m ≥ 1
    | "harmonic", [n] ->
        (match intArg n with
         | Some n' when n'.Sign >= 0 && n' <= BigInteger harmonicLimit -> Some (harmonicRat n' 1I)
         | _ -> None)
    | "harmonic", [n; m] ->
        (match intArg n, intArg m with
         | Some n', Some m' when n'.Sign >= 0 && n' <= BigInteger harmonicLimit && m' >= 1I ->
             Some (harmonicRat n' m')
         | _ -> None)
    // Число Бернулли B_n, n ≤ 60: нечётные n > 1 → 0 (B_1 = −1/2)
    | "bernoulli", [n] ->
        (match intArg n with
         | Some nn when nn >= 0I && nn <= 60I ->
             let i = int nn
             let b = bernoulliTable.Force().[i]
             if i > 1 && i % 2 = 1 then Some (LispInteger 0I)
             else Some (makeRational (fst b) (snd b))
         | _ -> None)
    // Многочлен Бернулли B_n(x) = Σ C(n,k)·B_k·x^{n−k}, n ≤ 30 — раскрываем в сумму
    | "bernoulli", [n; x] ->
        (match intArg n with
         | Some n' when n' >= 0I && n' <= 30I ->
             let i = int n'
             let terms =
                 [ for k in 0 .. i do
                     let bp, bq = if k > 1 && k % 2 = 1 then 0I, 1I else bernoulliTable.Force().[k]
                     let c = binomInt (BigInteger i) (BigInteger k)
                     let coef = makeRational (bp * c) bq
                     if not (isFoldable coef && isZero coef) then
                         let pow = i - k
                         if pow = 0 then coef
                         else
                             let xp = if pow = 1 then x else LispList [LispSym "^"; x; LispInteger (BigInteger pow)]
                             if isOne coef then xp else LispList [LispSym "*"; coef; xp] ]
             match terms with
             | [] -> Some (LispInteger 0I)
             | _ -> Some (simplify (simplifySum terms))
         | _ -> None)
    | _ -> None

// Функция одного аргумента: точное значение либо форма (f a) с пользовательскими правилами
and private makeFun (f: string) (a: LispValue) : LispValue =
    match exactValue f a with
    | Some v -> v
    | None -> applyUserRules (LispList [LispSym f; a])

// --- Степень ---

and simplifyPow (args: LispValue list) : LispValue =
    // Шаг 14: (^ obj e) — метод (^ t te), иначе символьная форма
    let viaMethod =
        match args with
        | [b; e] when Objects.needsDispatch b || Objects.needsDispatch e -> callMethod "^" [b; e]
        | _ -> None
    match viaMethod with
    // метод вернул ту же форму (^ b e) — «не применим» (например, ^ алгебраического с отрицательной степенью)
    | Some r when (match r, args with
                   | LispList [LispSym "^"; b; e], [b2; e2] -> structEqual b b2 && structEqual e e2
                   | _ -> false) -> simplifyPowBase args
    | Some r -> simplify r
    | None -> simplifyPowBase args

and private simplifyPowBase (args: LispValue list) : LispValue =
    match args with
    | [bse; exp] ->
        if isFoldable exp && isZero exp then LispInteger 1I
        elif isFoldable exp && isOne exp then bse
        elif isFoldable bse && isOne bse then LispInteger 1I
        // Шаг 21c: 0^p = 0 при вещественном p > 0 (в т.ч. дробном: 0^(1/2) = 0)
        elif isFoldable bse && isZero bse && isFoldable exp
             && (match exp with LispComplex _ -> false | _ -> compareNum exp (LispInteger 0I) > 0) then
            LispInteger 0I
        elif isFoldable bse && isFoldable exp then
            match numPow bse exp with
            | Some r ->
                // точный корень из числа (4^(1/2) → 2); целые степени — обычная арифметика, не трассируются
                if Debug.simpTracing && (match exp with LispRational _ -> true | _ -> false) then
                    Debug.simpStep "exact-root" (LispList [LispSym "^"; bse; exp]) r
                r
            | None ->
                match bse, exp with
                // Шаг 18: (-a)^(p/2) = %i^p · a^(p/2) для отрицательного рационального основания
                // (главная ветвь: sqrt(-4) = 2%i, (-2)^(1/2) = %i·2^(1/2))
                | (LispInteger _ | LispRational _), LispRational (p, q) when q = 2I && compareNum bse (LispInteger 0I) < 0 ->
                    simplifyMul [simplifyPow [LispSym "%i"; LispInteger p]; simplifyPow [simplifyMul [minusOne; bse]; exp]]
                // Шаг 18/21c: положительное рациональное число в дробной рациональной степени — вынос полных
                // q-х степеней и рационализация знаменателя: 8^(1/2) → 2·2^(1/2), 12^(1/2) → 2·3^(1/2),
                // (1/2)^(1/2) → 1/2·2^(1/2), 2^(3/2) → 2·2^(1/2), 2^(-1/2) → 1/2·2^(1/2), 4^(1/4) → 2^(1/2)
                // (канонический вид: рациональный множитель · m^(1/q), m > 1 целое; числа > 10^12 не раскладываются)
                | (LispInteger _ | LispRational _), LispRational (p, q)
                    when q <= 100I && BigInteger.Abs p <= 10000I && compareNum bse (LispInteger 0I) > 0 ->
                    let n, d = match bse with
                               | LispInteger bi -> bi, 1I
                               | LispRational (x, y) -> x, y
                               | _ -> 1I, 1I
                    let r =
                        match extractRoot n d p q with
                        | None -> LispList [LispSym "^"; bse; exp]
                        | Some (outside, None) -> outside
                        | Some (outside, Some (m, q1)) ->
                            simplifyMul [outside; LispList [LispSym "^"; LispInteger m; makeRational 1I q1]]
                    if Debug.simpTracing then
                        (match r with
                         | LispList [LispSym "^"; b2; e2] when structEqual b2 bse && structEqual e2 exp -> ()   // не изменилось
                         | _ -> Debug.simpStep "extract-root" (LispList [LispSym "^"; bse; exp]) r)
                    r
                | _ -> LispList [LispSym "^"; bse; exp]
        else
            match bse, exp with
            // (^ (* a b) n) → (* (^ a n) (^ b n)) для целого n (все множители коммутативны)
            | LispList (LispSym "*" :: fs), LispInteger _ when fs |> List.forall isCommutative ->
                let r = simplifyMul (fs |> List.map (fun f -> simplifyPow [f; exp]))
                if Debug.simpTracing then
                    // отрицательный n — «раскрытие отрицательной степени»: (a b)^-1 → a^-1 b^-1
                    Debug.simpStep "power-of-product" (LispList [LispSym "^"; bse; exp]) r
                r
            // Шаг 21c: (^ (exp u) n) → exp(n·u) для целого n (в т.ч. 1/exp(u) → exp(-u))
            | LispList [LispSym "exp"; u], LispInteger _ ->
                let r = makeFun "exp" (simplifyMul [exp; u])
                if Debug.simpTracing then Debug.simpStep "exp-power" (LispList [LispSym "^"; bse; exp]) r
                r
            // (^ (^ x a) n) → (^ x (* a n)) для целого n
            | LispList [LispSym "^"; c; a], LispInteger _ ->
                let r = simplifyPow [c; simplifyMul [a; exp]]
                if Debug.simpTracing then Debug.simpStep "power-of-power" (LispList [LispSym "^"; bse; exp]) r
                r
            // Шаг 18: мнимая единица %i^n для целого n: 1, %i, -1, -%i по n mod 4
            | LispSym "%i", LispInteger n ->
                let r =
                    match int (((n % 4I) + 4I) % 4I) with
                    | 0 -> LispInteger 1I
                    | 1 -> bse
                    | 2 -> minusOne
                    | _ -> LispList [LispSym "*"; minusOne; bse]
                if Debug.simpTracing then Debug.simpStep "imaginary-power" (LispList [LispSym "^"; bse; exp]) r
                r
            | _ -> LispList [LispSym "^"; bse; exp]
    | _ -> LispList (LispSym "^" :: args)
