// Арифметика по модулю простого p < 2^31 на int64 (общая для модулярного НОД Брауна, Зиппеля и разложения):
// степень/обращение, одномерный НОД над Z_p, список больших простых, детерминированный генератор точек.
// Шаг 21h': вынесено из MPoly.fs.
module ModArith

let powModL (b: int64) (e: int64) (p: int64) : int64 =
    let mutable r = 1L
    let mutable bb = b % p
    let mutable ee = e
    while ee > 0L do
        if ee &&& 1L = 1L then r <- r * bb % p
        bb <- bb * bb % p
        ee <- ee >>> 1
    r

let invModL (a: int64) (p: int64) : int64 = powModL a (p - 2L) p

// Одномерный НОД над Z_p (массивы коэффициентов от младшего), результат — унитарный
let gcdArr (p: int64) (a0: int64[]) (b0: int64[]) : int64[] =
    let trim (a: int64[]) =
        let mutable n = a.Length
        while n > 0 && a.[n - 1] = 0L do n <- n - 1
        if n = a.Length then a else Array.sub a 0 n
    let rem (a: int64[]) (b: int64[]) : int64[] =
        let r = Array.copy a
        let db = b.Length - 1
        let inv = invModL b.[db] p
        for k in r.Length - 1 .. -1 .. db do
            let c = r.[k]
            if c <> 0L then
                let f = c * inv % p
                for j in 0 .. db do
                    let t = (r.[k - db + j] - f * b.[j]) % p
                    r.[k - db + j] <- if t < 0L then t + p else t
        trim (Array.sub r 0 (min db r.Length))
    let mutable a = trim a0
    let mutable b = trim b0
    while b.Length > 0 do
        let r = rem a b
        a <- b
        b <- r
    let inv = invModL a.[a.Length - 1] p
    a |> Array.map (fun c -> c * inv % p)

// Детерминированный генератор (xorshift64*): воспроизводимые точки для тестов и отладки
type Rng(seed: uint64) =
    let mutable s = if seed = 0UL then 0x9E3779B97F4A7C15UL else seed
    // значение в [lo, hi]
    member _.Range (lo: int64, hi: int64) : int64 =
        s <- s ^^^ (s >>> 12)
        s <- s ^^^ (s <<< 25)
        s <- s ^^^ (s >>> 27)
        let r = (s * 0x2545F4914F6CDD1DUL) >>> 11
        lo + int64 (r % uint64 (hi - lo + 1L))

// Простые чуть меньше 2^31 (произведение двух вычетов помещается в int64)
let modPrimes : Lazy<int64[]> =
    lazy (
        let isPrime (n: int64) =
            let mutable ok = true
            let mutable d = 3L
            while ok && d * d <= n do
                if n % d = 0L then ok <- false
                d <- d + 2L
            ok
        let res = ResizeArray<int64>()
        let mutable c = 2147483647L
        while res.Count < 120 do
            if isPrime c then res.Add c
            c <- c - 2L
        res.ToArray())
