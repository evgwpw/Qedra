// Многочлены от нескольких переменных (Шаг 17) — вычислительное ядро на F#
//
// Представление — РЕКУРСИВНОЕ ПЛОТНОЕ: многочлен = константа (рациональное число) |
// (номер главной переменной v, массив коэффициентов от младшей степени к старшей), где каждый
// коэффициент — многочлен от переменных с МЕНЬШИМИ номерами (v-1, ...). Инварианты (поддерживает `mk`):
// массив не заканчивается нулём и содержит минимум 2 элемента (иначе это просто коэффициент).
// Массивы после создания не изменяются (разделяются между многочленами).
//
// Переменные — «ядра» выражения: символы и всё, что не является многочленом от символов —
// (sin x), (^ x 1/2), (sqrt 2), (log y), алгебраические числа, float и комплексные числа.
// Структурно равные ядра — одна переменная. Целая отрицательная степень — знаменатель
// (рациональная функция). Float в коэффициентах НЕ поддерживается: float — ядро (отдельная переменная).
// Порядок переменных (Ctx) — по orderCompare; чем больше номер, тем «главнее» переменная.
//
// Шаг 21h' (архитектура): файл — только ядро (арифметика, деление, псевдоделение, преобразования).
// Остальное, что раньше жило здесь: Subresultant.fs (субрезультантная PRS), ModArith.fs (арифметика по модулю p),
// ModGcd.fs (модулярный НОД Брауна и проба одной точкой), Zippel.fs (LINZIP), PolyGcd.fs (gcd/lcm/дроби),
// PolyExpr.fs (мост «выражение Lisp ↔ многочлен»).
module MPoly

open System.Numerics
open Rational

type Q = BigInteger * BigInteger

type MPoly =
    | Const of Q
    | Poly of int * MPoly[]

let zero = Const (0I, 1I)
let one = Const (1I, 1I)
let ofInt (n: BigInteger) : MPoly = Const (n, 1I)
let ofRat (q: Q) : MPoly = Const (ratNorm q)

let isZero (p: MPoly) = match p with Const (n, _) -> n.IsZero | _ -> false
let isOne (p: MPoly) = match p with Const (n, d) -> n.IsOne && d.IsOne | _ -> false
let isConst (p: MPoly) = match p with Const _ -> true | _ -> false
// Номер главной переменной; -1 для константы
let mainVar (p: MPoly) : int = match p with Const _ -> -1 | Poly (v, _) -> v

// Конструктор с нормализацией (отбрасывает старшие нули; коэффициенты должны быть «ниже» v)
let mk (v: int) (cs: MPoly[]) : MPoly =
    let mutable n = cs.Length
    while n > 0 && isZero cs.[n - 1] do n <- n - 1
    if n = 0 then zero
    elif n = 1 then cs.[0]
    elif n = cs.Length then Poly (v, cs)
    else Poly (v, Array.sub cs 0 n)

let var (v: int) : MPoly = Poly (v, [| zero; one |])

let rec add (a: MPoly) (b: MPoly) : MPoly =
    match a, b with
    | Const x, Const y -> Const (ratAdd x y)
    | Poly (v, ca), Poly (w, cb) when v = w ->
        let n = max ca.Length cb.Length
        mk v (Array.init n (fun i ->
            if i >= ca.Length then cb.[i]
            elif i >= cb.Length then ca.[i]
            else add ca.[i] cb.[i]))
    | Poly (v, ca), _ when v > mainVar b ->
        let cs = Array.copy ca
        cs.[0] <- add cs.[0] b
        mk v cs
    | _, Poly (w, cb) when w > mainVar a ->
        let cs = Array.copy cb
        cs.[0] <- add a cs.[0]
        mk w cs
    | _ -> failwith "MPoly.add: нарушен инвариант порядка переменных"

let rec neg (p: MPoly) : MPoly =
    match p with
    | Const (n, d) -> Const (-n, d)
    | Poly (v, cs) -> Poly (v, Array.map neg cs)

let sub (a: MPoly) (b: MPoly) : MPoly = add a (neg b)

let rec mulConst (q: Q) (p: MPoly) : MPoly =
    match p with
    | Const x -> Const (ratMul x q)
    | Poly (v, cs) -> if ratIsZero q then zero else mk v (Array.map (mulConst q) cs)

let rec mul (a: MPoly) (b: MPoly) : MPoly =
    match a, b with
    | Const x, Const y -> Const (ratMul x y)
    | Poly (v, ca), Poly (w, cb) when v = w ->
        let res = Array.create (ca.Length + cb.Length - 1) zero
        for i in 0 .. ca.Length - 1 do
            if not (isZero ca.[i]) then
                for j in 0 .. cb.Length - 1 do
                    if not (isZero cb.[j]) then
                        res.[i + j] <- add res.[i + j] (mul ca.[i] cb.[j])
        mk v res
    | Poly (v, ca), _ when v > mainVar b -> mk v (Array.map (fun c -> mul c b) ca)
    | _, Poly (w, cb) when w > mainVar a -> mk w (Array.map (fun c -> mul a c) cb)
    | _ -> failwith "MPoly.mul: нарушен инвариант порядка переменных"

let pow (p: MPoly) (n: int) : MPoly =
    if n < 0 then failwith "MPoly.pow: отрицательная степень"
    let rec go (b: MPoly) (k: int) (acc: MPoly) =
        if k = 0 then acc
        elif k &&& 1 = 1 then go (if k = 1 then b else mul b b) (k >>> 1) (mul acc b)
        else go (mul b b) (k >>> 1) acc
    go p n one

// Степень по главной переменной (0 для ненулевой константы, -1 для нуля)
let degMain (p: MPoly) : int =
    match p with
    | Const _ -> if isZero p then -1 else 0
    | Poly (_, cs) -> cs.Length - 1

// Старший коэффициент по главной переменной (сам многочлен, если он константа)
let lcMain (p: MPoly) : MPoly =
    match p with
    | Const _ -> p
    | Poly (_, cs) -> cs.[cs.Length - 1]

// Степень по переменной v (не обязательно главной)
let rec degIn (v: int) (p: MPoly) : int =
    match p with
    | Const _ -> if isZero p then -1 else 0
    | Poly (w, cs) when w = v -> cs.Length - 1
    | Poly (w, cs) when w > v -> cs |> Array.map (degIn v) |> Array.max
    | _ -> 0

// Коэффициент при v^k (многочлен от переменных, отличных от v)
let rec coeffIn (v: int) (k: int) (p: MPoly) : MPoly =
    match p with
    | Const _ -> if k = 0 then p else zero
    | Poly (w, cs) when w = v -> if k < cs.Length then cs.[k] else zero
    | Poly (w, cs) when w > v -> mk w (Array.map (coeffIn v k) cs)
    | _ -> if k = 0 then p else zero

// Производная по переменной v
let rec deriv (v: int) (p: MPoly) : MPoly =
    match p with
    | Const _ -> zero
    | Poly (w, cs) when w = v ->
        mk w (Array.init (cs.Length - 1) (fun i -> mulConst (BigInteger (i + 1), 1I) cs.[i + 1]))
    | Poly (w, cs) when w > v -> mk w (Array.map (deriv v) cs)
    | _ -> zero

// Подстановка многочлена value вместо переменной v (общий случай — через add/mul)
let rec subst (v: int) (value: MPoly) (p: MPoly) : MPoly =
    match p with
    | Const _ -> p
    | Poly (w, cs) when w < v -> p
    | Poly (w, cs) when w = v ->
        // схема Горнера
        let mutable acc = zero
        for i in cs.Length - 1 .. -1 .. 0 do
            acc <- add (mul acc value) cs.[i]
        acc
    | Poly (w, cs) ->
        let x = var w
        let mutable acc = zero
        for i in cs.Length - 1 .. -1 .. 0 do
            acc <- add (mul acc x) (subst v value cs.[i])
        acc

// --- рациональные листья ---

let rec iterConsts (f: Q -> unit) (p: MPoly) : unit =
    match p with
    | Const q -> f q
    | Poly (_, cs) -> for c in cs do iterConsts f c

let rec leadConst (p: MPoly) : Q =
    match p with
    | Const q -> q
    | Poly (_, cs) -> leadConst cs.[cs.Length - 1]

// p = c * pp, pp — с целыми взаимно простыми коэффициентами и положительным старшим;
// для нуля — (0, 0)
let primitiveInt (p: MPoly) : Q * MPoly =
    if isZero p then ((0I, 1I), zero)
    else
        let mutable l = 1I
        iterConsts (fun (_, d) -> l <- l / gcd l d * d) p
        let scaled = if l.IsOne then p else mulConst (l, 1I) p
        let mutable g = 0I
        iterConsts (fun (n, _) -> g <- gcd g n) scaled
        let g = if (fst (leadConst scaled)).Sign < 0 then -g else g
        let pp = if g.IsOne then scaled else mulConst (1I, g) scaled
        (ratNorm (g, l), pp)

// «Единичная нормировка»: целые взаимно простые коэффициенты, положительный старший (0 → 0)
let unitNormal (p: MPoly) : MPoly = snd (primitiveInt p)

// Множество номеров переменных, входящих в многочлен (добавляются к acc)
let rec varsOf (p: MPoly) (acc: Set<int>) : Set<int> =
    match p with
    | Const _ -> acc
    | Poly (v, cs) -> cs |> Array.fold (fun s c -> varsOf c s) (Set.add v acc)

// --- точное деление ---

// a / b, если делится нацело (в ℚ[x1..xn]); иначе None
let rec divExact (a: MPoly) (b: MPoly) : MPoly option =
    if isZero b then None
    elif isZero a then Some zero
    else
        match b with
        | Const (n, d) -> Some (mulConst (d, n) a)
        | Poly (w, cb) ->
            match a with
            | Const _ -> None
            | Poly (v, _) when v < w -> None
            | Poly (v, ca) when v > w ->
                let res = ca |> Array.map (fun c -> divExact c b)
                if res |> Array.forall Option.isSome then Some (mk v (res |> Array.map Option.get)) else None
            | Poly (v, ca) ->
                let da, db = ca.Length - 1, cb.Length - 1
                if da < db then None
                else
                    let r = Array.copy ca
                    let q = Array.create (da - db + 1) zero
                    let lcb = cb.[db]
                    let mutable ok = true
                    let mutable k = da - db
                    while ok && k >= 0 do
                        match divExact r.[k + db] lcb with
                        | None -> ok <- false
                        | Some c ->
                            q.[k] <- c
                            if not (isZero c) then
                                for j in 0 .. db do
                                    r.[k + j] <- sub r.[k + j] (mul c cb.[j])
                            k <- k - 1
                    if ok && (r |> Array.forall isZero) then Some (mk v q) else None

// Исход деления нацело в терминах единого контракта (Outcome): «не делится» — доказано самим делением (NoSolution)
let divExactOutcome (a: MPoly) (b: MPoly) : Outcome.Outcome<MPoly> =
    match divExact a b with
    | Some q -> Outcome.Answer q
    | None -> Outcome.NoSolution "делимое не делится нацело на делитель (ненулевой остаток или делитель нулевой)"

let divExactExn (a: MPoly) (b: MPoly) : MPoly =
    match divExactOutcome a b with
    | Outcome.Answer q -> q
    | _ -> failwith "MPoly: деление нацело невозможно"

// --- псевдоделение по главной переменной ---

// Псевдоостаток: lc(b)^(δ+1) · a = q·b + r, δ = deg a - deg b. Обе — многочлены с одной главной
// переменной; если deg a < deg b — возвращается a. Возвращает (r, число использованных lc(b) = δ+1)
let private pdivCore (a: MPoly) (b: MPoly) : MPoly * MPoly * int =
    match a, b with
    | Poly (v, ca), Poly (w, cb) when v = w && ca.Length >= cb.Length ->
        let da, db = ca.Length - 1, cb.Length - 1
        let lcb = cb.[db]
        let r = Array.copy ca
        let q = Array.create (da - db + 1) zero
        let mutable skipped = 0
        for k in da - db .. -1 .. 0 do
            let top = k + db
            let c = r.[top]
            if isZero c then skipped <- skipped + 1
            else
                for j in 0 .. top - 1 do
                    r.[j] <- mul lcb r.[j]
                for j in 0 .. db - 1 do
                    r.[k + j] <- sub r.[k + j] (mul c cb.[j])
                r.[top] <- zero
                for j in k + 1 .. da - db do
                    q.[j] <- mul lcb q.[j]
                q.[k] <- c
        let rem = mk v (Array.sub r 0 db)
        let extra = if skipped = 0 then one else pow lcb skipped
        // q: в каждый шаг умножался на lcb уже накопленный q; пропущенные шаги — общий множитель
        (mul extra rem, mul extra (mk v q), da - db + 1)
    // деление на ненулевую константу: c·a = a·c + 0
    | _, Const _ when not (isZero b) -> (zero, a, 1)
    | _ -> (a, zero, 0)

// Псевдоостаток prem(a, b)
let prem (a: MPoly) (b: MPoly) : MPoly = let (r, _, _) = pdivCore a b in r

// Псевдочастное и остаток: lc(b)^e · a = q·b + r; возвращает (q, r, e)
let pseudoDivMod (a: MPoly) (b: MPoly) : MPoly * MPoly * int =
    let (r, q, e) = pdivCore a b
    (q, r, e)

// Многочлен → список термов (коэффициент, [(переменная, степень)])
let monomials (p: MPoly) : (Q * (int * int) list) list =
    let out = ResizeArray<Q * (int * int) list>()
    let rec go (p: MPoly) (acc: (int * int) list) =
        match p with
        | Const q -> if not (ratIsZero q) then out.Add (q, acc)
        | Poly (v, cs) ->
            for i in 0 .. cs.Length - 1 do
                go cs.[i] (if i = 0 then acc else (v, i) :: acc)
    go p []
    List.ofSeq out
