// Изоляция корней по Штурму и рациональные корни (Шаг 12; вынесено из Algebraic.fs в Шаге 15a)
// Рациональная арифметика (ratAdd, ratMul, ...) и isqrtBigint — в Numeric.fs
module Sturm

open System.Numerics
open Rational

// --- Минимальные операции над bigint list (формат данных LispAlgebraic: от старшей степени к младшей) ---
// (Шаг 17a: бывший Polynomial.fs удалён, общие многочлены — MPoly; здесь только то, что нужно Штурму)

// Нормализация: убрать ведущие нули; пустой список → [0]
let rec normalize (cs: bigint list) : bigint list =
    match cs with
    | [] -> [0I]
    | c :: rest when c = 0I && rest <> [] -> normalize rest
    | _ -> cs

// Степень многочлена
let degree (cs: bigint list) : int =
    (normalize cs).Length - 1

// Производная
let derivative (cs: bigint list) : bigint list =
    match normalize cs with
    | [_] -> [0I]
    | cs' ->
        let n = cs'.Length - 1
        [ for i in 0 .. n - 1 -> (bigint (n - i)) * cs'.[i] ] |> normalize

// --- Полиномиальные операции в рациональных точках ---

// Оценка многочлена в рациональной точке (схема Горнера)
let evalPolyRat (poly: bigint list) (x: bigint * bigint) : bigint * bigint =
    let rec loop acc cs =
        match cs with
        | [] -> acc
        | c :: rest -> loop (ratAdd (ratMul acc x) (c, 1I)) rest
    loop (0I, 1I) (normalize poly)

// Знак многочлена в рациональной точке
let signPolyRat (poly: bigint list) (x: bigint * bigint) : int =
    ratSign (evalPolyRat poly x)

// --- Sturm-последовательность ---

// Псевдо-остаток с положительным масштабированием (сохранение знаков для Sturm):
//   r_new = |lc(b)| * r - lc(r)*sign(lc(b)) * b * x^shift = |lc(b)| * (r mod b)
// Все промежуточные значения целые, главный коэффициент сокращается (степень падает)
let signedRemainder (a: bigint list) (b: bigint list) : bigint list =
    let b' = normalize b
    let db = degree b'
    let leadB = List.head b'
    let lcb = abs leadB
    let signB = if leadB < 0I then -1I else 1I
    let mutable r = normalize a
    while degree r >= db && r <> [0I] do
        let shift = r.Length - 1 - db
        let lcr = List.head r
        // scaled = lcb * r (положительное масштабирование)
        let scaled = r |> List.map (fun c -> c * lcb)
        // вычитаем кратный b, чтобы обнулить старший коэффициент
        let factor = lcr * signB
        let subtr = (b' |> List.map (fun c -> factor * c)) @ [for _ in 1 .. shift -> 0I]
        let len = max scaled.Length subtr.Length
        let pad (cs: bigint list) = [for _ in 1 .. (len - cs.Length) -> 0I] @ cs
        r <- normalize ((pad scaled, pad subtr) ||> List.map2 (-))
    r

// Sturm: [p, p', -rem(p,p'), -rem(p',p₂), ...]
let sturmSequence (poly: bigint list) : bigint list list =
    let p0 = normalize poly
    let p1 = normalize (derivative p0)
    // seq хранит элементы в порядке «последний — в голове»
    let rec loop (seq: bigint list list) =
        match seq with
        | b :: a :: _ when degree b > 0 ->
            let rem = signedRemainder a b
            // деление на положительное содержимое не меняет знаков, но не даёт коэффициентам расти экспоненциально
            // (шаг 21i'' (3′): без него цепочка для многочлена степени 20 не считалась минутами)
            let g = rem |> List.fold (fun acc c -> BigInteger.GreatestCommonDivisor(acc, c)) 0I
            let rem' = if g.IsZero || g.IsOne then rem else rem |> List.map (fun c -> c / g)
            let next = normalize (rem' |> List.map (fun c -> -c))
            loop (next :: seq)
        | _ -> List.rev seq
    loop [p1; p0]

// Подсчёт перемен знака Sturm-последовательности в рациональной точке (нули игнорируем)
let signChanges (seq: bigint list list) (a: bigint * bigint) : int =
    seq
    |> List.map (fun p -> signPolyRat p a)
    |> List.filter (fun s -> s <> 0)
    |> fun signs ->
        let rec count prev rest =
            match rest with
            | [] -> 0
            | s :: tl -> (if prev <> s then 1 else 0) + count s tl
        match signs with
        | [] -> 0
        | s :: tl -> count s tl

// Число различных корней в (lo, hi) — разность перемен знака на границах
let rootsInInterval (seq: bigint list list) (lo: bigint * bigint) (hi: bigint * bigint) : int =
    signChanges seq lo - signChanges seq hi

// Середина интервала; если середина — корень, немного сдвигаем (чтобы не попасть в корень)
let ratMid (poly: bigint list) (lo: bigint * bigint) (hi: bigint * bigint) : bigint * bigint =
    let m = ratMul (ratAdd lo hi) (1I, 2I)
    if signPolyRat poly m = 0 then
        // (lo + 2*hi)/3 — точка внутри интервала, как правило не корень
        ratMul (ratAdd lo (ratMul hi (2I, 1I))) (1I, 3I)
    else m

// --- Изоляция корней (бисекция с Sturm) ---

// Изолировать все действительные корни poly → список (poly, lo, hi)
// Каждый интервал содержит ровно один корень
let isolateRoots (poly: bigint list) : (bigint list * (bigint * bigint) * (bigint * bigint)) list =
    // Шаг 18: многочлен приводится к примитивной части с положительным старшим коэффициентом
    // (корни те же; root(4 0 -8) → root(1 0 -2))
    let p0 = normalize poly
    let g = p0 |> List.fold (fun acc c -> BigInteger.GreatestCommonDivisor(acc, c)) 0I
    let g = if g.IsZero then 1I else (if p0.Head.Sign < 0 then -g else g)
    let p = if g.IsOne then p0 else p0 |> List.map (fun c -> c / g)
    if degree p <= 0 then []
    else
        let sturm = sturmSequence p
        // Граница Коши (округление вверх): все корни |x| < B = 1 + M/|a_m|
        let lead = abs (List.head p)
        let m = p.Tail |> List.fold (fun acc c -> max acc (abs c)) 1I
        let bound = 1I + (m + lead - 1I) / lead
        // Бисекция: интервал с ≤1 корнем → готов; иначе делим пополам
        let rec bisect (lo: bigint * bigint) (hi: bigint * bigint) depth =
            let cnt = rootsInInterval sturm lo hi
            if cnt = 0 then []
            elif cnt = 1 || depth > 200 then [(p, lo, hi)]
            else
                let mid = ratMid p lo hi
                bisect lo mid (depth + 1) @ bisect mid hi (depth + 1)
        bisect (-bound, 1I) (bound, 1I) 0

// Уточнение интервала: один шаг бисекции (оставляем половину, где лежит корень)
let refineInterval (poly: bigint list) (lo: bigint * bigint) (hi: bigint * bigint) : (bigint * bigint) * (bigint * bigint) =
    let sturm = sturmSequence poly
    let mid = ratMid poly lo hi
    let cnt = rootsInInterval sturm lo mid
    if cnt = 1 then (lo, mid) else (mid, hi)

// k шагов уточнения интервала
let refineN (poly: bigint list) (lo: bigint * bigint) (hi: bigint * bigint) (k: int) : (bigint * bigint) * (bigint * bigint) =
    let rec loop l h n =
        if n = 0 then (l, h)
        else
            let l', h' = refineInterval poly l h
            loop l' h' (n - 1)
    loop lo hi k

// --- Рациональные корни (теорема о рациональных корнях) ---

// Все рациональные корни poly: pn/q, где pn | a_0, q | a_m (перебор делителей)
let rationalRoots (poly: bigint list) : (bigint * bigint) list =
    let p = normalize poly
    if degree p <= 0 then []
    else
        let a0 = List.last p
        let am = List.head p
        let divisors (x: bigint) : bigint list =
            let x = abs x
            if x = 0I then [0I]
            else
                let lim = isqrtBigint x
                let mutable acc = []
                let mutable d = 1I
                while d <= lim do
                    if x % d = 0I then
                        acc <- d :: (x / d) :: acc
                    d <- d + 1I
                acc |> List.distinct
        let ps = divisors a0
        let qs = divisors am
        [ for q in qs do
            for pn in ps do
                let cand = ratNorm (pn, q)
                if signPolyRat p cand = 0 then yield cand
                if pn <> 0I then
                    let candN = ratNorm (-pn, q)
                    if signPolyRat p candN = 0 then yield candN ]
        |> List.distinct

