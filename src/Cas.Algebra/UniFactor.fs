// Разложение на множители одномерных многочленов над ℤ (Шаг 17, коммит 2) — алгоритм Цассенхауза
//
// 1) рациональные корни → линейные множители (быстрый путь);
// 2) выбор простого p (старший коэффициент не делится, f mod p бесквадратен; пробуется несколько простых,
//    берётся то, где меньше всего множителей);
// 3) разложение mod p: distinct-degree + equal-degree (Кантор–Цассенхауз, детерминированный seed);
// 4) подъём Хензеля (квадратичный, деревом) до p^(2^j) > 2·|lc|·B, B — граница Миньотта;
// 5) перебор комбинаций модулярных множителей (по возрастанию размера) с отсечением по свободному члену
//    и пробным делением.
// Многочлены над ℤ — массивы BigInteger от младшей степени к старшей (без старших нулей);
// над F_p — массивы int.
module UniFactor

open System
open System.Numerics
open Rational

type ZPoly = BigInteger[]

let private trimZ (a: BigInteger[]) : ZPoly =
    let mutable n = a.Length
    while n > 0 && a.[n - 1].IsZero do n <- n - 1
    if n = a.Length then a else Array.sub a 0 n

let degZ (a: ZPoly) = a.Length - 1

// --- арифметика над F_p (p — небольшое простое) ---

let trimP (a: int[]) : int[] =
    let mutable n = a.Length
    while n > 0 && a.[n - 1] = 0 do n <- n - 1
    if n = a.Length then a else Array.sub a 0 n

let private modI (p: int) (x: int64) : int =
    let r = x % int64 p
    int (if r < 0L then r + int64 p else r)

let private addP (p: int) (a: int[]) (b: int[]) : int[] =
    trimP (Array.init (max a.Length b.Length) (fun i ->
        modI p ((if i < a.Length then int64 a.[i] else 0L) + (if i < b.Length then int64 b.[i] else 0L))))

let private subP (p: int) (a: int[]) (b: int[]) : int[] =
    trimP (Array.init (max a.Length b.Length) (fun i ->
        modI p ((if i < a.Length then int64 a.[i] else 0L) - (if i < b.Length then int64 b.[i] else 0L))))

let mulP (p: int) (a: int[]) (b: int[]) : int[] =
    if a.Length = 0 || b.Length = 0 then [||]
    else
        let r = Array.zeroCreate<int64> (a.Length + b.Length - 1)
        for i in 0 .. a.Length - 1 do
            if a.[i] <> 0 then
                for j in 0 .. b.Length - 1 do
                    r.[i + j] <- (r.[i + j] + int64 a.[i] * int64 b.[j]) % int64 p
        trimP (r |> Array.map int)

let private powModInt (b: int) (e: int) (p: int) : int =
    let mutable r = 1L
    let mutable x = int64 b % int64 p
    let mutable k = e
    while k > 0 do
        if k &&& 1 = 1 then r <- r * x % int64 p
        x <- x * x % int64 p
        k <- k >>> 1
    int r

let private invP (p: int) (a: int) : int = powModInt a (p - 2) p

let monicP (p: int) (a: int[]) : int[] =
    if a.Length = 0 then a
    else
        let inv = invP p a.[a.Length - 1]
        a |> Array.map (fun c -> int (int64 c * int64 inv % int64 p))

// Деление с остатком над F_p
let divModP (p: int) (a: int[]) (b: int[]) : int[] * int[] =
    let db = b.Length - 1
    if a.Length - 1 < db then ([||], a)
    else
        let r = Array.map int64 a
        let q = Array.zeroCreate<int> (a.Length - db)
        let inv = int64 (invP p b.[db])
        for k in a.Length - 1 - db .. -1 .. 0 do
            let c = r.[k + db] % int64 p * inv % int64 p
            q.[k] <- int c
            if c <> 0L then
                for j in 0 .. db do
                    r.[k + j] <- ((r.[k + j] - c * int64 b.[j]) % int64 p + int64 p) % int64 p
        (trimP q, trimP (Array.sub r 0 db |> Array.map int))

let gcdP (p: int) (a: int[]) (b: int[]) : int[] =
    let mutable x = a
    let mutable y = b
    while y.Length > 0 do
        let (_, r) = divModP p x y
        x <- y
        y <- r
    monicP p x

let derivP (p: int) (a: int[]) : int[] =
    if a.Length <= 1 then [||]
    else trimP (Array.init (a.Length - 1) (fun i -> modI p (int64 a.[i + 1] * int64 (i + 1))))

// a^e mod m над F_p
let private powModP (p: int) (a: int[]) (e: BigInteger) (m: int[]) : int[] =
    let mutable result = [| 1 |]
    let mutable b = snd (divModP p a m)
    let mutable k = e
    while not k.IsZero do
        if not k.IsEven then result <- snd (divModP p (mulP p result b) m)
        b <- snd (divModP p (mulP p b b) m)
        k <- k >>> 1
    result

// Расширенный Евклид над F_p: (g, s, t), s·a + t·b = g (g унитарен)
let extGcdP (p: int) (a: int[]) (b: int[]) : int[] * int[] * int[] =
    let mutable r0, r1 = a, b
    let mutable s0, s1 = [| 1 |], [||]
    let mutable t0, t1 = [||], [| 1 |]
    while r1.Length > 0 do
        let (q, r2) = divModP p r0 r1
        r0 <- r1
        r1 <- r2
        let s2 = subP p s0 (mulP p q s1)
        s0 <- s1
        s1 <- s2
        let t2 = subP p t0 (mulP p q t1)
        t0 <- t1
        t1 <- t2
    let inv = invP p r0.[r0.Length - 1]
    let sc (x: int[]) = x |> Array.map (fun c -> int (int64 c * int64 inv % int64 p))
    (sc r0, sc s0, sc t0)

// --- разложение над F_p ---

// Distinct-degree: унитарный бесквадратный f → [(произведение неприводимых степени d, d)]
let private ddf (p: int) (f: int[]) : (int[] * int) list =
    let mutable fs = f
    let mutable h = [| 0; 1 |]
    let mutable d = 0
    let res = ResizeArray<int[] * int>()
    while fs.Length - 1 >= 2 * (d + 1) do
        d <- d + 1
        h <- snd (divModP p (powModP p h (BigInteger p) fs) fs)
        let g = gcdP p (subP p h [| 0; 1 |]) fs
        if g.Length - 1 > 0 then
            res.Add (g, d)
            fs <- fst (divModP p fs g)
            h <- snd (divModP p h fs)
    if fs.Length - 1 > 0 then res.Add (fs, fs.Length - 1)
    List.ofSeq res

// Equal-degree (Кантор–Цассенхауз, p нечётное): g — произведение неприводимых одной степени d
let rec private edf (p: int) (d: int) (rnd: Random) (g: int[]) : int[] list =
    let n = g.Length - 1
    if n <= d then [g]
    else
        let e = (BigInteger.Pow(BigInteger p, d) - 1I) / 2I
        let rec attempt () =
            let a = trimP (Array.init n (fun _ -> rnd.Next p))
            if a.Length <= 1 then attempt ()
            else
                let b = powModP p a e g
                let h = gcdP p (subP p b [| 1 |]) g
                if h.Length - 1 > 0 && h.Length - 1 < n then h else attempt ()
        let h = attempt ()
        edf p d rnd h @ edf p d rnd (monicP p (fst (divModP p g h)))

// Разложение унитарного бесквадратного f над F_p на унитарные неприводимые
let private factorModP (p: int) (f: int[]) : int[] list =
    let rnd = Random 20271012
    ddf p f |> List.collect (fun (g, d) -> edf p d rnd g)

// --- арифметика над ℤ/M ---

let private modM (m: BigInteger) (x: BigInteger) : BigInteger =
    let r = BigInteger.Remainder(x, m)
    if r.Sign < 0 then r + m else r

let private reduceM (m: BigInteger) (a: BigInteger[]) : ZPoly = trimZ (Array.map (modM m) a)

let private addM m (a: ZPoly) (b: ZPoly) : ZPoly =
    reduceM m (Array.init (max a.Length b.Length) (fun i ->
        (if i < a.Length then a.[i] else 0I) + (if i < b.Length then b.[i] else 0I)))

let private subM m (a: ZPoly) (b: ZPoly) : ZPoly =
    reduceM m (Array.init (max a.Length b.Length) (fun i ->
        (if i < a.Length then a.[i] else 0I) - (if i < b.Length then b.[i] else 0I)))

let private mulM m (a: ZPoly) (b: ZPoly) : ZPoly =
    if a.Length = 0 || b.Length = 0 then [||]
    else
        let r = Array.create (a.Length + b.Length - 1) 0I
        for i in 0 .. a.Length - 1 do
            if not a.[i].IsZero then
                for j in 0 .. b.Length - 1 do
                    r.[i + j] <- r.[i + j] + a.[i] * b.[j]
        reduceM m r

// Деление на унитарный (mod M) многочлен h: (q, r)
let private divModMonicM (m: BigInteger) (a: ZPoly) (h: ZPoly) : ZPoly * ZPoly =
    let dh = h.Length - 1
    if a.Length - 1 < dh then ([||], a)
    else
        let r = Array.copy a
        let q = Array.create (a.Length - dh) 0I
        for k in a.Length - 1 - dh .. -1 .. 0 do
            let c = modM m r.[k + dh]
            q.[k] <- c
            if not c.IsZero then
                for j in 0 .. dh do
                    r.[k + j] <- modM m (r.[k + j] - c * h.[j])
        (reduceM m q, reduceM m (Array.sub r 0 dh))

// Обратное по модулю m (m, a взаимно просты)
let private modInverse (a: BigInteger) (m: BigInteger) : BigInteger =
    let mutable r0, r1 = m, modM m a
    let mutable t0, t1 = 0I, 1I
    while not r1.IsZero do
        let q = BigInteger.Divide(r0, r1)
        let r2 = r0 - q * r1
        r0 <- r1
        r1 <- r2
        let t2 = t0 - q * t1
        t0 <- t1
        t1 <- t2
    modM m t0

// --- подъём Хензеля ---

// fM — унитарный mod M многочлен, f ≡ g0·h0 (mod p); s·g0 + t·h0 ≡ 1 (mod p).
// Квадратичный подъём пары p → p^2 → p^4 → ... → M; результат — унитарные G, H mod M.
// M — любая степень p (Шаг 21f): последний шаг поднимает до min(m^2, M), формулы верны по любому модулю p^k, k <= 2l
let private liftPair (fM: ZPoly) (g0: int[]) (h0: int[]) (p: int) (bigM: BigInteger) : ZPoly * ZPoly =
    let (_, s0, t0) = extGcdP p g0 h0
    let toZ (a: int[]) : ZPoly = a |> Array.map BigInteger
    let mutable g = toZ g0
    let mutable h = toZ h0
    let mutable s = toZ s0
    let mutable t = toZ t0
    let mutable m = BigInteger p
    while m < bigM do
        let m2 = BigInteger.Min (m * m, bigM)
        let f = reduceM m2 fM
        let e = subM m2 f (mulM m2 g h)
        let (q, r) = divModMonicM m2 (mulM m2 s e) h
        let g1 = addM m2 (addM m2 g (mulM m2 t e)) (mulM m2 q g)
        let h1 = addM m2 h r
        let b = subM m2 (addM m2 (mulM m2 s g1) (mulM m2 t h1)) [| 1I |]
        let (c, d) = divModMonicM m2 (mulM m2 s b) h1
        let s1 = subM m2 s d
        let t1 = subM m2 (subM m2 t (mulM m2 t b)) (mulM m2 c g1)
        g <- g1
        h <- h1
        s <- s1
        t <- t1
        m <- m2
    (g, h)

// Подъём разложения f̃ ≡ Π facs (mod p) до модуля M: деревом из пар
let rec liftAll (fM: ZPoly) (facs: int[] list) (p: int) (bigM: BigInteger) : ZPoly list =
    match facs with
    | [] -> []
    | [_] -> [fM]
    | _ ->
        let half = facs.Length / 2
        let left, right = List.take half facs, List.skip half facs
        let prod (l: int[] list) = l |> List.fold (mulP p) [| 1 |]
        let (g, h) = liftPair fM (prod left) (prod right) p bigM
        liftAll g left p bigM @ liftAll h right p bigM

// --- вспомогательные операции над ℤ[x] ---

let private contentZ (a: ZPoly) : BigInteger = a |> Array.fold gcd 0I

// Примитивная часть с положительным старшим коэффициентом
let primitiveZ (a: ZPoly) : ZPoly =
    if a.Length = 0 then a
    else
        let c = contentZ a
        let c = if a.[a.Length - 1].Sign < 0 then -c else c
        a |> Array.map (fun x -> x / c)

// Точное деление над ℤ: None, если не делится
let divExactZ (a: ZPoly) (b: ZPoly) : ZPoly option =
    let db = b.Length - 1
    if a.Length - 1 < db then (if a.Length = 0 then Some [||] else None)
    else
        let r = Array.copy a
        let q = Array.create (a.Length - db) 0I
        let lb = b.[db]
        let mutable ok = true
        let mutable k = a.Length - 1 - db
        while ok && k >= 0 do
            let (c, rem) = BigInteger.DivRem(r.[k + db], lb)
            if not rem.IsZero then ok <- false
            else
                q.[k] <- c
                if not c.IsZero then
                    for j in 0 .. db do
                        r.[k + j] <- r.[k + j] - c * b.[j]
                k <- k - 1
        if ok && (Array.forall (fun (x: BigInteger) -> x.IsZero) r) then Some (trimZ q) else None

let private mulZ (a: ZPoly) (b: ZPoly) : ZPoly =
    if a.Length = 0 || b.Length = 0 then [||]
    else
        let r = Array.create (a.Length + b.Length - 1) 0I
        for i in 0 .. a.Length - 1 do
            for j in 0 .. b.Length - 1 do
                r.[i + j] <- r.[i + j] + a.[i] * b.[j]
        r

// Границы Миньотта: |коэффициенты любого делителя| <= C(n, n/2) · ‖f‖₂
let private mignotte (f: ZPoly) : BigInteger =
    let n = f.Length - 1
    let norm2 = f |> Array.fold (fun acc c -> acc + c * c) 0I
    let nrm = isqrtBigint norm2 + 1I
    let mutable binom = 1I
    let k = n / 2
    for i in 1 .. k do
        binom <- binom * BigInteger (n - k + i) / BigInteger i
    binom * nrm

// --- быстрый путь: рациональные корни ---

// Делители |n| (пробным делением; None — слишком большое число)
let private divisorsOf (n: BigInteger) : BigInteger list option =
    let n = BigInteger.Abs n
    if n.IsZero then None
    elif n > 1000000000000I then None
    else
        let nn = int64 n
        let res = ResizeArray<BigInteger>()
        let mutable i = 1L
        while i * i <= nn do
            if nn % i = 0L then
                res.Add (BigInteger i)
                if i * i <> nn then res.Add (BigInteger (nn / i))
            i <- i + 1L
        Some (List.ofSeq res)

// Вычисление f(d/e)·e^n
let private evalScaled (f: ZPoly) (d: BigInteger) (e: BigInteger) : BigInteger =
    let n = f.Length - 1
    let mutable acc = 0I
    for i in n .. -1 .. 0 do
        acc <- acc * d + f.[i] * BigInteger.Pow(e, n - i)
    acc

// Линейные множители (ex - d) по рациональным корням; (список множителей, остаток)
let private rationalRootFactors (f0: ZPoly) : ZPoly list * ZPoly =
    let mutable f = f0
    let found = ResizeArray<ZPoly>()
    let mutable go = true
    while go && f.Length > 2 do
        match divisorsOf f.[0], divisorsOf f.[f.Length - 1] with
        | Some ds, Some es when ds.Length * es.Length <= 20000 ->
            let cand =
                [ for d in ds do
                    for e in es do
                        if (gcd d e).IsOne then
                            yield (d, e)
                            yield (-d, e) ]
                |> List.tryFind (fun (d, e) -> (evalScaled f d e).IsZero)
            match cand with
            | Some (d, e) ->
                let lin : ZPoly = [| -d; e |]
                found.Add lin
                f <- (divExactZ f lin).Value
            | None -> go <- false
        | _ -> go <- false
    (List.ofSeq found, f)

// --- простые числа ---

let private smallPrimes : int list =
    let limit = 3000
    let sieve = Array.create (limit + 1) true
    [ for i in 2 .. limit do
        if sieve.[i] then
            yield i
            let mutable j = i * i
            while j <= limit do
                sieve.[j] <- false
                j <- j + i ]

// --- Цассенхауз ---

// Суммы подмножеств степеней (a.[t] = true, если существует подмножество с суммой t) — степени, которые
// может иметь делитель f, исходя из разложения mod p (Шаг 21f)
let private degreeSums (degs: int list) (n: int) : bool[] =
    let a = Array.create (n + 1) false
    a.[0] <- true
    for d in degs do
        for t in n .. -1 .. d do
            if a.[t - d] then a.[t] <- true
    a

// Оценка модуля корней f (Fujiwara: 2·max |a_{n−k}/a_n|^{1/k}, свободный член с множителем 1/2), double с запасом;
// +∞ — оценка недоступна (тест Эбботта отключается)
let private rootBound (f: ZPoly) : float =
    let n = degZ f
    let lcl = BigInteger.Log (BigInteger.Abs f.[n])
    let mutable best = Double.NegativeInfinity
    for k in 1 .. n do
        let c = BigInteger.Abs f.[n - k]
        if not c.IsZero then
            let l = (BigInteger.Log c - lcl - (if k = n then Math.Log 2.0 else 0.0)) / float k
            if l > best then best <- l
    let r = if Double.IsNegativeInfinity best then 1.0 else 2.0 * Math.Exp best
    if Double.IsInfinity r || Double.IsNaN r then Double.PositiveInfinity else r * 1.001 + 1e-9

// Перебор подмножеств размера s индексов idxs; возвращает первое, чьё произведение даёт делитель frem.
// Отсечения до умножения и пробного деления (Шаг 21f): степень суммы должна быть в allowed (пересечение
// множеств возможных степеней по нескольким простым); тест Эбботта d−1: коэффициент при x^(d−1) делителя
// степени d с lc(frem)·(монический) есть −lc·Σ корней, значит |g_{d−1}| <= lc·d·R (R — оценка корней frem)
let private tryCombinations (m: BigInteger) (lifted: ZPoly[]) (degs: int[]) (allowed: bool[]) (idxs: int[]) (s: int)
                            (frem: ZPoly) : (ZPoly * int list) option =
    let lc = frem.[frem.Length - 1]
    let f0 = frem.[0]
    let n = idxs.Length
    let rbLazy = lazy (rootBound frem)
    let absLc = BigInteger.Abs lc
    let symmetric (a: ZPoly) : ZPoly =
        let half = m / 2I
        a |> Array.map (fun c -> if c > half then c - m else c)
    let rec search (start: int) (left: int) (prod: ZPoly) (chosen: int list) : (ZPoly * int list) option =
        if left = 0 then
            Cancel.check ()     // подшаг 22.4: перебор подмножеств экспоненциален — прерывание по проверке на кандидата
            let g = symmetric (mulM m [| lc |] prod)
            let d = g.Length - 1
            // тест Эбботта d−1
            let abbottFails =
                d >= 1
                && (let rb = rbLazy.Force ()
                    not (Double.IsInfinity rb)
                    && BigInteger.Abs g.[d - 1] > BigInteger (Math.Ceiling (float d * rb)) * absLc)
            if abbottFails then None
            // отсечение по свободному члену: g(0) должен делить lc·f(0)
            elif g.Length = 0 || g.[0].IsZero then None
            elif not (BigInteger.Remainder(lc * f0, g.[0])).IsZero then None
            else
                let u = primitiveZ g
                if u.Length < 2 then None
                else
                    match divExactZ frem u with
                    | Some _ -> Some (u, chosen)
                    | None -> None
        else
            let rec loop (i: int) =
                if i > n - left then None
                else
                    let li = idxs.[i]
                    // последний выбор: степень итогового произведения известна до умножения
                    if left = 1 && not allowed.[(prod.Length - 1) + degs.[li]] then loop (i + 1)
                    else
                        let p2 = mulM m prod lifted.[li]
                        match search (i + 1) (left - 1) p2 (li :: chosen) with
                        | Some r -> Some r
                        | None -> loop (i + 1)
            loop start
    search 0 s [| 1I |] []

// Число подмножеств размера s из m (с отсечением: > cap → cap + 1)
let private binomCapped (m: int) (s: int) (cap: BigInteger) : BigInteger =
    let mutable c = 1I
    let mutable i = 0
    while i < s && c <= cap do
        c <- c * BigInteger (m - i) / BigInteger (i + 1)
        i <- i + 1
    c

// Предел перебора: подмножеств одного размера не более 2^22 — для неприводимого остатка это r <= 24
// модулярных множителей (C(24,12) < 2^22 < C(25,12)); иначе остаток возвращается «как есть»
let private maxSubsetsPerSize = BigInteger 4194304

// Разложение примитивного бесквадратного f (положительный старший, deg >= 1) на неприводимые над ℤ
let factorSquarefree (f: ZPoly) : ZPoly list =
    let n = degZ f
    if n <= 1 then [f]
    else
        let lc = f.[n]
        // кандидаты простых
        let candidates =
            smallPrimes
            |> List.filter (fun p -> p > 2 && not (BigInteger.Remainder(lc, BigInteger p)).IsZero)
        let tryPrime (p: int) : (int[] list) option =
            let fp = trimP (f |> Array.map (fun c -> int (modM (BigInteger p) c)))
            if fp.Length - 1 <> n then None
            else
                let g = gcdP p fp (derivP p fp)
                if g.Length - 1 > 0 then None
                else Some (factorModP p (monicP p fp))
        let mutable best : (int * int[] list) option = None
        let mutable tried = 0
        let mutable rest = candidates
        // пересечение множеств возможных степеней делителей по нескольким простым (Шаг 21f):
        // 5 простых, если разложение уже мелкое, до 7 — иначе
        let allowed = Array.create (n + 1) true
        // (малая степень — 3 простых: раскладывается за пару подмножеств; 5 — обычно; до 7, когда
        // перебор подмножеств обещает быть дорогим — модулярных множителей уже 16 и больше)
        while tried < (if n <= 8 then 3 else match best with Some (_, bf) when bf.Length >= 16 -> 7 | _ -> 5) && not rest.IsEmpty && (match best with Some (_, fs) when fs.Length = 1 -> false | _ -> true) do
            let p = rest.Head
            rest <- rest.Tail
            match tryPrime p with
            | Some fs ->
                tried <- tried + 1
                let sums = degreeSums (fs |> List.map (fun g -> g.Length - 1)) n
                for t in 0 .. n do
                    if not sums.[t] then allowed.[t] <- false
                match best with
                | Some (_, bf) when bf.Length <= fs.Length -> ()
                | _ -> best <- Some (p, fs)
            | None -> ()
        // ни одна промежуточная степень не допустима — f неприводим
        let hasProperDegree = Seq.exists (fun t -> allowed.[t]) (seq { 1 .. n - 1 })
        match best with
        | None -> failwith "factor: не найдено подходящее простое"
        | Some (_, [_]) -> [f]
        | Some _ when not hasProperDegree -> [f]
        | Some (p, modFactors) ->
            // модуль M = p^(2^j) > 2·|lc|·B
            let bound = 2I * lc * mignotte f
            let mutable bigM = BigInteger p
            while bigM <= bound do bigM <- bigM * bigM
            let fM = reduceM bigM (Array.map (fun c -> c * modInverse lc bigM) f)
            let lifted = liftAll fM modFactors p bigM |> Array.ofList
            let degs = lifted |> Array.map (fun g -> g.Length - 1)
            let mutable idxs = [| 0 .. lifted.Length - 1 |]
            let mutable frem = f
            let result = ResizeArray<ZPoly>()
            let mutable s = 1
            while 2 * s <= idxs.Length do
                // слишком много подмножеств — остаток «как есть» (возможно, приводимый)
                if s >= 2 && binomCapped idxs.Length s maxSubsetsPerSize > maxSubsetsPerSize then
                    s <- idxs.Length
                else
                    match tryCombinations bigM lifted degs allowed idxs s frem with
                    | Some (u, chosen) ->
                        result.Add u
                        frem <- primitiveZ (divExactZ frem u).Value
                        idxs <- idxs |> Array.filter (fun i -> not (List.contains i chosen))
                    | None -> s <- s + 1
            if frem.Length > 1 then result.Add (primitiveZ frem)
            List.ofSeq result

// Полное разложение бесквадратного примитивного f (положительный старший): свободный член,
// рациональные корни, затем Цассенхауз. Линейные множители отдельно не специализируются
let factorSquarefreeFull (f: ZPoly) : ZPoly list =
    if f.Length <= 1 then []
    else
        let (lins, rest) = rationalRootFactors f
        let restFactors = if rest.Length > 1 then factorSquarefree (primitiveZ rest) else []
        lins @ restFactors
