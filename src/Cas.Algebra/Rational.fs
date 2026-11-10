// Рациональная арифметика на кортежах (числитель, знаменатель > 0) — Шаг 21h': вынесено из Numeric.fs, чтобы алгебра
// (Cas.Algebra) не зависела от типов Lisp. Обёртки «кортеж ↔ значение Lisp» (ratToValue, makeRational) — Numeric.fs (Lisp.Core).
module Rational

open System.Numerics

// Наибольший общий делитель (GCD) — для BigInteger
// Шаг 21i: BigInteger.GreatestCommonDivisor вместо цикла Евклида с остатками (неотрицательный, gcd(0, 0) = 0 — как раньше)
let gcd (a: BigInteger) (b: BigInteger) : BigInteger = BigInteger.GreatestCommonDivisor(a, b)

// --- Рациональная арифметика на кортежах (числитель, знаменатель > 0) ---
// Единственная реализация: арифметика LispRational (Numeric.fs) и Sturm/Algebraic используют её же

// Нормализация: сокращение и положительный знаменатель
// Шаг 21i: целые (d = 1) — без НОД и делений; знаки — через Sign (операторы F# < > на BigInteger — обобщённое
// сравнение с упаковкой аргументов)
let ratNorm ((n, d): BigInteger * BigInteger) : BigInteger * BigInteger =
    if d.IsOne then (n, d)
    elif d.IsZero then failwith "Деление на ноль при создании рационального числа"
    else
        let g = gcd n d
        let n' = if g.IsOne then n else n / g
        let d' = if g.IsOne then d else d / g
        if d'.Sign < 0 then (-n', -d') else (n', d')

let ratAdd (a: BigInteger * BigInteger) (b: BigInteger * BigInteger) : BigInteger * BigInteger =
    let (an, ad), (bn, bd) = a, b
    ratNorm (an * bd + bn * ad, ad * bd)

let ratSub (a: BigInteger * BigInteger) (b: BigInteger * BigInteger) : BigInteger * BigInteger =
    let (an, ad), (bn, bd) = a, b
    ratNorm (an * bd - bn * ad, ad * bd)

let ratMul (a: BigInteger * BigInteger) (b: BigInteger * BigInteger) : BigInteger * BigInteger =
    let (an, ad), (bn, bd) = a, b
    ratNorm (an * bn, ad * bd)

let ratDiv (a: BigInteger * BigInteger) (b: BigInteger * BigInteger) : BigInteger * BigInteger =
    let (an, ad), (bn, bd) = a, b
    if bn.IsZero then failwith "Деление на ноль"
    ratNorm (an * bd, ad * bn)

// Знаменатели положительные: p1/q1 vs p2/q2 → p1*q2 vs p2*q1
let ratCompare (a: BigInteger * BigInteger) (b: BigInteger * BigInteger) : int =
    let (an, ad), (bn, bd) = a, b
    if ad.IsOne && bd.IsOne then BigInteger.Compare(an, bn) else BigInteger.Compare(an * bd, bn * ad)

let ratSign (a: BigInteger * BigInteger) : int =
    let (n, _) = a
    n.Sign

let ratIsZero (a: BigInteger * BigInteger) : bool = ratSign a = 0

// Длина числителя + знаменателя в битах (по модулю; 0 — 0 бит) — диагностика роста коэффициентов (Groebner.fs)
let ratBits (a: BigInteger * BigInteger) : int64 =
    let (n, d) = a
    (if n.Sign < 0 then BigInteger.Negate(n).GetBitLength() else n.GetBitLength()) + d.GetBitLength()

// Целочисленный квадратный корень (метод Ньютона, округление вниз)
let isqrtBigint (n: BigInteger) : BigInteger =
    if n < 0I then failwith "isqrt: отрицательное число"
    elif n < 2I then n
    else
        let rec loop x =
            let nx = (x + n / x) / 2I
            if nx >= x then x else loop nx
        let start = 1I <<< (int (n.GetBitLength()) / 2 + 1)
        loop (start + 1I)
