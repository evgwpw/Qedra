// Числовая башня: арифметика, GCD, type promotion
// Integer → Rational → Float → Complex
module Numeric

open System.Numerics
open Types

// Шаг 21h': рациональная арифметика на кортежах (gcd, ratNorm, ratAdd, ..., isqrtBigint) живёт в Cas.Algebra (модуль
// Rational: алгебра не зависит от типов Lisp). Здесь — тонкие переадресации, чтобы код Lisp.Core и тесты, открывающие
// Numeric, работали без изменений.
let inline gcd (a: BigInteger) (b: BigInteger) : BigInteger = Rational.gcd a b
let inline ratNorm (q: BigInteger * BigInteger) : BigInteger * BigInteger = Rational.ratNorm q
let inline ratAdd (a: BigInteger * BigInteger) (b: BigInteger * BigInteger) : BigInteger * BigInteger = Rational.ratAdd a b
let inline ratSub (a: BigInteger * BigInteger) (b: BigInteger * BigInteger) : BigInteger * BigInteger = Rational.ratSub a b
let inline ratMul (a: BigInteger * BigInteger) (b: BigInteger * BigInteger) : BigInteger * BigInteger = Rational.ratMul a b
let inline ratDiv (a: BigInteger * BigInteger) (b: BigInteger * BigInteger) : BigInteger * BigInteger = Rational.ratDiv a b
let inline ratCompare (a: BigInteger * BigInteger) (b: BigInteger * BigInteger) : int = Rational.ratCompare a b
let inline ratSign (a: BigInteger * BigInteger) : int = Rational.ratSign a
let inline ratIsZero (a: BigInteger * BigInteger) : bool = Rational.ratIsZero a
let inline isqrtBigint (n: BigInteger) : BigInteger = Rational.isqrtBigint n

// Кортеж → значение башни: знаменатель 1 → целое
let ratToValue ((n, d): BigInteger * BigInteger) : LispValue =
    if d.IsOne then LispInteger n else LispRational (n, d)

// Создаём рациональное число, сокращая дробь и нормализуя знак
let makeRational (num: BigInteger) (den: BigInteger) : LispValue =
    ratToValue (ratNorm (num, den))

// Определение типа числа — для promotion
type NumberKind =
    | KindInteger
    | KindRational
    | KindAlgebraic
    | KindFloat
    | KindComplex

let kindOf (v: LispValue) : NumberKind =
    match v with
    | LispInteger _ -> KindInteger
    | LispRational _ -> KindRational
    | LispAlgebraic _ -> KindAlgebraic
    | LispFloat _ -> KindFloat
    | LispComplex _ -> KindComplex
    | _ -> failwith "Не число"

// Старший тип из двух — определяет promotion
let higherKind (a: NumberKind) (b: NumberKind) : NumberKind =
    match a, b with
    | KindComplex, _ | _, KindComplex -> KindComplex
    | KindFloat, _ | _, KindFloat -> KindFloat
    | KindAlgebraic, _ | _, KindAlgebraic -> KindAlgebraic
    | KindRational, _ | _, KindRational -> KindRational
    | KindInteger, KindInteger -> KindInteger

// Приводим значение к указанному типу (повышение)
let promoteTo (kind: NumberKind) (v: LispValue) : LispValue =
    match kind, v with
    | KindInteger, LispInteger _ -> v
    | KindRational, LispInteger n -> LispRational (n, 1I)
    | KindRational, LispRational _ -> v
    | KindAlgebraic, LispAlgebraic _ -> v
    | KindFloat, LispInteger n -> LispFloat (double n)
    | KindFloat, LispRational (p, q) -> LispFloat (double p / double q)
    | KindFloat, LispFloat _ -> v
    | KindFloat, LispAlgebraic (_, (loN, loD), (hiN, hiD)) ->
        // Средняя точка изолирующего интервала
        LispFloat ((double loN / double loD + double hiN / double hiD) / 2.0)
    | KindComplex, LispInteger _ -> LispComplex (v, LispInteger 0I)
    | KindComplex, LispRational _ -> LispComplex (v, LispInteger 0I)
    | KindComplex, LispFloat _ -> LispComplex (v, LispFloat 0.0)
    | KindComplex, LispAlgebraic _ -> LispComplex (v, LispInteger 0I)
    | KindComplex, LispComplex _ -> v
    // уже нужный тип — возвращаем как есть
    | _, _ -> v

// Приводим два числа к общему (старшему) типу
let align (a: LispValue) (b: LispValue) : LispValue * LispValue =
    let ka = kindOf a
    let kb = kindOf b
    let target = higherKind ka kb
    promoteTo target a, promoteTo target b

// --- Арифметика (взаимно-рекурсивна из-за комплексных чисел) ---

let rec add (a: LispValue) (b: LispValue) : LispValue =
    let a', b' = align a b
    match a', b' with
    | LispInteger x, LispInteger y -> LispInteger (x + y)
    | LispRational (p1, q1), LispRational (p2, q2) ->

        ratToValue (ratAdd (p1, q1) (p2, q2))
    | LispFloat x, LispFloat y -> LispFloat (x + y)
    | LispComplex (r1, i1), LispComplex (r2, i2) ->
        LispComplex (add r1 r2, add i1 i2)
    | LispAlgebraic _, _ | _, LispAlgebraic _ ->
        failwith "add: алгебраическая арифметика — используйте algebraic builtins"
    | _ -> failwith "add: несогласованные типы"

and sub (a: LispValue) (b: LispValue) : LispValue =
    let a', b' = align a b
    match a', b' with
    | LispInteger x, LispInteger y -> LispInteger (x - y)
    | LispRational (p1, q1), LispRational (p2, q2) ->
        ratToValue (ratSub (p1, q1) (p2, q2))
    | LispFloat x, LispFloat y -> LispFloat (x - y)
    | LispComplex (r1, i1), LispComplex (r2, i2) ->
        LispComplex (sub r1 r2, sub i1 i2)
    | LispAlgebraic _, _ | _, LispAlgebraic _ ->
        failwith "sub: алгебраическая арифметика — используйте algebraic builtins"
    | _ -> failwith "sub: несогласованные типы"

and mul (a: LispValue) (b: LispValue) : LispValue =
    let a', b' = align a b
    match a', b' with
    | LispInteger x, LispInteger y -> LispInteger (x * y)
    | LispRational (p1, q1), LispRational (p2, q2) ->
        ratToValue (ratMul (p1, q1) (p2, q2))
    | LispFloat x, LispFloat y -> LispFloat (x * y)
    | LispComplex (r1, i1), LispComplex (r2, i2) ->
        // (r1 + i1i)(r2 + i2i) = (r1r2 - i1i2) + (r1i2 + i1r2)i
        LispComplex (sub (mul r1 r2) (mul i1 i2),
                     add (mul r1 i2) (mul i1 r2))
    | LispAlgebraic _, _ | _, LispAlgebraic _ ->
        failwith "mul: алгебраическая арифметика — используйте algebraic builtins"
    | _ -> failwith "mul: несогласованные типы"

and div (a: LispValue) (b: LispValue) : LispValue =
    let a', b' = align a b
    match a', b' with
    | LispInteger x, LispInteger y ->
        if y.IsZero then failwith "Деление на ноль"
        // Пробуем точное деление; если не делится — рациональное
        if (x % y).IsZero then LispInteger (x / y)
        else makeRational x y
    | LispRational (p1, q1), LispRational (p2, q2) ->
        // (p1/q1) / (p2/q2) = (p1*q2) / (p2*q1)
        ratToValue (ratDiv (p1, q1) (p2, q2))
    | LispFloat x, LispFloat y ->
        if y = 0.0 then failwith "Деление на ноль"
        LispFloat (x / y)
    | LispComplex (r1, i1), LispComplex (r2, i2) ->
        // Деление комплексных: умножаем на сопряжённое
        // (r1+i1i) / (r2+i2i) = (r1+i1i)(r2-i2i) / (r2²+i2²)
        let denom = add (mul r2 r2) (mul i2 i2)
        let numerR = sub (mul r1 r2) (mul i1 i2)
        let numerI = add (mul i1 r2) (mul r1 i2)
        LispComplex (div numerR denom, div numerI denom)
    | LispAlgebraic _, _ | _, LispAlgebraic _ ->
        failwith "div: алгебраическая арифметика — используйте algebraic builtins"
    | _ -> failwith "div: несогласованные типы"

// --- Сравнения (только для чисел, не комплексных) ---

let compareNum (a: LispValue) (b: LispValue) : int =
    let a', b' = align a b
    match a', b' with
    | LispInteger x, LispInteger y -> BigInteger.Compare(x, y)     // не compare: обобщённое сравнение упаковывает
    | LispRational (p1, q1), LispRational (p2, q2) ->
        // p1/q1 vs p2/q2 → p1*q2 vs p2*q1 (знаменатели положительные)
        ratCompare (p1, q1) (p2, q2)
    | LispFloat x, LispFloat y -> compare x y
    | LispComplex _, LispComplex _ -> failwith "Сравнение комплексных чисел не определено"
    | LispAlgebraic _, _ | _, LispAlgebraic _ ->
        failwith "compareNum: алгебраическое сравнение — используйте algCompare"
    | _ -> failwith "compareNum: несогласованные типы"

let numEqual (a: LispValue) (b: LispValue) : bool = compareNum a b = 0
let numLess (a: LispValue) (b: LispValue) : bool = compareNum a b < 0
let numGreater (a: LispValue) (b: LispValue) : bool = compareNum a b > 0
let numLessEq (a: LispValue) (b: LispValue) : bool = compareNum a b <= 0
let numGreaterEq (a: LispValue) (b: LispValue) : bool = compareNum a b >= 0

// --- Числовые предикаты (используются Builtins, Simplify, Differentiate) ---

// Является ли значение числом (любого типа из числовой башни)
let isNumber (v: LispValue) : bool =
    match v with
    | LispInteger _ | LispRational _ | LispFloat _ | LispComplex _ | LispAlgebraic _ -> true
    | _ -> false

// Равно нулю?
let isZero (v: LispValue) : bool =
    match v with
    | LispInteger n -> n.IsZero
    | LispFloat f -> f = 0.0
    | LispAlgebraic (poly, (loN, loD), (hiN, hiD)) ->
        // Свободный член = 0 и интервал содержит 0
        let constant = List.last poly
        constant = 0I && loN <= 0I && hiN >= 0I
    | _ -> false

// Равно единице?
let isOne (v: LispValue) : bool =
    match v with
    | LispInteger n -> n.IsOne
    | LispFloat f -> f = 1.0
    | LispAlgebraic (poly, (loN, loD), (hiN, hiD)) ->
        // poly(1) = 0 (сумма коэффициентов) и интервал содержит 1
        let sum = List.sum poly
        sum = 0I && loN <= loD && hiN >= hiD
    | _ -> false

// --- Структурное равенство (для simplify: a/a → 1, a-a → 0) ---

let rec structEqual (a: LispValue) (b: LispValue) : bool =
    match a, b with
    // Шаг 21i' (d): BigInteger.Equals вместо обобщённого «=» F# (оно упаковывает оба аргумента)
    | LispInteger x, LispInteger y -> x.Equals y
    | LispRational (p1, q1), LispRational (p2, q2) -> p1.Equals p2 && q1.Equals q2
    | LispFloat x, LispFloat y -> x = y
    | LispAlgebraic (p1, lo1, hi1), LispAlgebraic (p2, lo2, hi2) ->
        p1 = p2 && lo1 = lo2 && hi1 = hi2
    | LispBool x, LispBool y -> x = y
    | LispStr x, LispStr y -> x = y
    | LispSym x, LispSym y -> x = y
    | LispNil, LispNil -> true
    | LispList xs, LispList ys ->
        xs.Length = ys.Length && List.forall2 structEqual xs ys
    | LispObject o1, LispObject o2 ->
        o1.Type = o2.Type && o1.Fields.Length = o2.Fields.Length
        && Array.forall2 structEqual o1.Fields o2.Fields
    | LispVector v1, LispVector v2 ->
        v1.Length = v2.Length && Array.forall2 structEqual v1 v2
    | LispPair (a1, b1), LispPair (a2, b2) -> structEqual a1 a2 && structEqual b1 b2
    | _ -> false
