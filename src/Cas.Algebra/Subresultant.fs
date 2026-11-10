// Субрезультантные последовательности остатков и результант многочленов от нескольких переменных (шаг 21h').
// Общая схема Брауна–Коллинза (Bronstein §1.5; Cohen 3.3.7) для НОД (primitivePrs, бывший MPoly.fs) и для
// результанта/ЛРТ (subResultant, бывший RatInt.fs): R_{i+1} = prem(R_{i−1}, R_i)/(g·h^δ), g = lc(R_i),
// h = h^{1−δ}·g^δ — точные деления, без дробей. Шаг рекуррентности (nextTerm / nextH) — общий.
module Subresultant

open MPoly

// Очередной член: prem / (g·h^δ) (деление точное)
let private nextTerm (r: MPoly) (g: MPoly) (h: MPoly) (delta: int) : MPoly =
    divExactExn r (mul g (pow h delta))

// Новое h после смены (a, b): g — старший коэффициент нового a, delta — скачок степени
let private nextH (g: MPoly) (h: MPoly) (delta: int) : MPoly =
    if delta = 0 then h
    elif delta = 1 then g
    else divExactExn (pow g delta) (pow h (delta - 1))

// Субрезультантная последовательность остатков для примитивных a, b с общей главной переменной: НОД (с точностью до
// содержания). Нулевой остаток → последний ненулевой член; остаток «ниже» главной переменной → 1
let primitivePrs (a0: MPoly) (b0: MPoly) : MPoly =
    let a1, b1 = if degMain a0 >= degMain b0 then a0, b0 else b0, a0
    let mutable a = a1
    let mutable b = b1
    let mutable g = one
    let mutable h = one
    let mutable result : MPoly option = None
    while result.IsNone do
        let delta = degMain a - degMain b
        let r = prem a b
        if isZero r then result <- Some b
        elif mainVar r < mainVar b then result <- Some one
        else
            a <- b
            b <- nextTerm r g h delta
            g <- lcMain a
            h <- nextH g h delta
    result.Value

// A, B ∈ R[x] (R = ℚ[параметры, t] — целостное кольцо), x — главная переменная. Алгоритм Брауна–Коллинза.
// Возвращает (результант, [R_0 = A; R_1 = B; R_2; …; R_k]) (R_k — последний ненулевой; нулевой результант — когда deg R_k > 0).
// Дефектные скачки степени (deg R_i − deg R_{i+1} > 1) обрабатываются самой схемой: степени членов PRS не обязаны идти подряд —
// для каждого i, при котором S_i ≠ 0 тождественно, в PRS есть член ровно степени i (см. RatInt.lrt).
let subResultant (x: int) (a0: MPoly) (b0: MPoly) : MPoly * MPoly list =
    if isZero a0 || isZero b0 then (zero, [])
    else
        let mutable a, b = a0, b0
        let mutable sgn = 1
        let odd (n: int) = n &&& 1 = 1
        if degIn x a < degIn x b then
            let tmp = a
            a <- b
            b <- tmp
            if odd (degIn x a) && odd (degIn x b) then sgn <- -sgn
        let prs = ResizeArray<MPoly>()
        prs.Add a
        prs.Add b
        if degIn x b = 0 then
            let r = pow b (degIn x a)
            ((if sgn < 0 then neg r else r), List.ofSeq prs)
        else
            let mutable g = one
            let mutable h = one
            let mutable result : MPoly option = None
            while result.IsNone do
                let delta = degIn x a - degIn x b
                if odd (degIn x a) && odd (degIn x b) then sgn <- -sgn
                let r = prem a b
                if isZero r then result <- Some zero
                else
                    let bnew = nextTerm r g h delta
                    a <- b
                    g <- lcMain a
                    h <- nextH g h delta
                    b <- bnew
                    prs.Add b
                    if degIn x b = 0 then
                        let da = degIn x a
                        let hh = if da <= 1 then mul (pow h (1 - da)) (pow b da) else divExactExn (pow b da) (pow h (da - 1))
                        result <- Some (if sgn < 0 then neg hh else hh)
            (result.Value, List.ofSeq prs)

// --- результант через матрицу Сильвестра ---

// Определитель методом Барейса без дробей (точные деления в MPoly); при нулевом ведущем элементе — перестановка строк
let private detBareiss (m: MPoly[][]) : MPoly =
    let n = m.Length
    let mutable sign = 1
    let mutable prev = one
    let mutable zeroDet = false
    let mutable k = 0
    while not zeroDet && k < n - 1 do
        if isZero m.[k].[k] then
            match [ k + 1 .. n - 1 ] |> List.tryFind (fun r -> not (isZero m.[r].[k])) with
            | Some r ->
                let tmp = m.[k]
                m.[k] <- m.[r]
                m.[r] <- tmp
                sign <- -sign
            | None -> zeroDet <- true
        if not zeroDet then
            for i in k + 1 .. n - 1 do
                for j in k + 1 .. n - 1 do
                    m.[i].[j] <- divExactExn (sub (mul m.[i].[j] m.[k].[k]) (mul m.[i].[k] m.[k].[j])) prev
            prev <- m.[k].[k]
        k <- k + 1
    if zeroDet then zero
    else (if sign < 0 then neg m.[n - 1].[n - 1] else m.[n - 1].[n - 1])

// Результант двух многочленов по переменной с номером xi: определитель матрицы Сильвестра
let resultantPoly (xi: int) (a: MPoly) (b: MPoly) : MPoly =
    let m, n = degIn xi a, degIn xi b
    if isZero a || isZero b then zero
    elif m = 0 && n = 0 then one
    elif m = 0 then pow a n
    elif n = 0 then pow b m
    else
        let ca = Array.init (m + 1) (fun k -> coeffIn xi (m - k) a)   // от старшей степени к младшей
        let cb = Array.init (n + 1) (fun k -> coeffIn xi (n - k) b)
        let size = m + n
        let mat = Array.init size (fun _ -> Array.create size zero)
        for i in 0 .. n - 1 do
            for k in 0 .. m do mat.[i].[i + k] <- ca.[k]
        for i in 0 .. m - 1 do
            for k in 0 .. n do mat.[n + i].[i + k] <- cb.[k]
        detBareiss mat
