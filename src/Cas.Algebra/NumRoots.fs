// Численные методы для корней многочленов (шаг 21h'; вынесено из SolveNum.fs): метод Аберта в double, уточнение
// корней методом Ньютона в многоразрядной фиксированной точке, точное двоичное представление double, степень Complex.
// Без типов Lisp: выражения разбирает SolveNum (Lisp.Core).
module NumRoots

open System
open System.Numerics
open MPoly
open Rational

// Многочлены с double-коэффициентами (по возрастанию степени)
let padd (a: double[]) (b: double[]) : double[] =
    Array.init (max a.Length b.Length) (fun i ->
        (if i < a.Length then a.[i] else 0.0) + (if i < b.Length then b.[i] else 0.0))

let pmul (a: double[]) (b: double[]) : double[] =
    let r = Array.zeroCreate (a.Length + b.Length - 1)
    for i in 0 .. a.Length - 1 do
        for j in 0 .. b.Length - 1 do
            r.[i + j] <- r.[i + j] + a.[i] * b.[j]
    r

// Корни многочлена (коэффициенты по возрастанию, старший ненулевой, степень >= 1): метод Аберта
let aberth (c: double[]) : Complex[] =
    let n = c.Length - 1
    let a = c |> Array.map (fun v -> Complex(v / c.[n], 0.0))
    // радиус начальной окружности: оценка Фудзивары
    let mutable r = 0.0
    for k in 1 .. n do
        r <- max r (Math.Pow(Complex.Abs a.[n - k] / (if k = n then 2.0 else 1.0), 1.0 / double k))
    let r = max (2.0 * r) 1e-3
    let z = Array.init n (fun k -> Complex.FromPolarCoordinates(r, 2.0 * Math.PI * double k / double n + 0.4))
    let mutable iter = 0
    let mutable converged = false
    while not converged && iter < 500 do
        converged <- true
        for i in 0 .. n - 1 do
            // схема Горнера: значение и производная
            let mutable p = a.[n]
            let mutable dp = Complex.Zero
            for k in n - 1 .. -1 .. 0 do
                dp <- dp * z.[i] + p
                p <- p * z.[i] + a.[k]
            if p <> Complex.Zero then
                let w = p / dp
                let mutable s = Complex.Zero
                for j in 0 .. n - 1 do
                    if j <> i then s <- s + Complex.One / (z.[i] - z.[j])
                let step = w / (Complex.One - w * s)
                z.[i] <- z.[i] - step
                if Complex.Abs step > 1e-15 * (1.0 + Complex.Abs z.[i]) then converged <- false
        iter <- iter + 1
    z

// Все комплексные корни по коэффициентам (по возрастанию степени); нулевые младшие коэффициенты — корень 0.
// Кратные корни находятся с пониженной точностью (~ eps^(1/кратность))
let rootsOfCoeffs (cs: double[]) : Complex list =
    let zeros = cs |> Array.takeWhile (fun v -> v = 0.0) |> Array.length
    let rest = Array.sub cs zeros (cs.Length - zeros)
    let found = if rest.Length > 1 then List.ofArray (aberth rest) else []
    (List.replicate zeros Complex.Zero) @ found

// Уточнение корней многочлена с ЦЕЛЫМИ коэффициентами методом Ньютона в арифметике с фиксированной точкой (320 бит):
// приближения Аберта в double теряют точность при большом разбросе коэффициентов (корни плохо обусловлены)
let refineRoots (cs: BigInteger[]) (roots: Complex list) : Complex list =
    let prec = 320
    let n = cs.Length - 1
    let fixOf (d: double) : BigInteger = (BigInteger (d * 4503599627370496.0)) <<< (prec - 52)
    let back (v: BigInteger) : double = double (v >>> (prec - 80)) / 1.2089258196146292e24    // 2^80
    let refine (z0: Complex) : Complex =
        let mutable zr = fixOf z0.Real
        let mutable zi = fixOf z0.Imaginary
        let mutable ok = true
        let mutable iter = 0
        while ok && iter < 12 do
            let mutable pr, pi = 0I, 0I
            let mutable dr, di = 0I, 0I
            for k in n .. -1 .. 0 do
                let ndr = ((dr * zr - di * zi) >>> prec) + pr
                let ndi = ((dr * zi + di * zr) >>> prec) + pi
                dr <- ndr
                di <- ndi
                let npr = ((pr * zr - pi * zi) >>> prec) + (cs.[k] <<< prec)
                let npi = (pr * zi + pi * zr) >>> prec
                pr <- npr
                pi <- npi
            let den = dr * dr + di * di
            if den.IsZero then ok <- false
            else
                let qr = ((pr * dr + pi * di) <<< prec) / den
                let qi = ((pi * dr - pr * di) <<< prec) / den
                zr <- zr - qr
                zi <- zi - qi
                if BigInteger.Abs qr + BigInteger.Abs qi < (1I <<< (prec - 200)) then ok <- false
            iter <- iter + 1
        Complex(back zr, back zi)
    roots |> List.map (fun z ->
        let r = refine z
        // защита: уточнение не должно уйти далеко от приближения (кластер корней)
        if Complex.Abs (r - z) <= 1e-2 * (1.0 + Complex.Abs z) then r else z)

// Степень комплексного числа с целым показателем (быстрое возведение; точнее, чем Complex.Pow)
let ipow (b: Complex) (n: int) : Complex =
    let rec go (b: Complex) (k: int) (acc: Complex) =
        if k = 0 then acc
        elif k &&& 1 = 1 then go (b * b) (k >>> 1) (acc * b)
        else go (b * b) (k >>> 1) acc
    if n >= 0 then go b n Complex.One else Complex.One / go b (-n) Complex.One

// double → точное рациональное число
let ratOfDouble (d: double) : Q =
    if d = 0.0 then (0I, 1I)
    else
        let bits = BitConverter.DoubleToInt64Bits d
        let sign = if bits < 0L then -1I else 1I
        let expo = int ((bits >>> 52) &&& 0x7FFL)
        let frac = bits &&& 0xFFFFFFFFFFFFFL
        let m, e = if expo = 0 then BigInteger frac, -1074 else BigInteger (frac ||| 0x10000000000000L), expo - 1075
        if e >= 0 then (sign * m * BigInteger.Pow(2I, e), 1I) else ratNorm (sign * m, BigInteger.Pow(2I, -e))
