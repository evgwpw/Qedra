// НОД многочленов от нескольких переменных: драйвер (шаг 21h'; вынесено из MPoly.fs).
// Содержание (НОД коэффициентов по главной переменной) + примитивные части: модулярный НОД Брауна (ModGcd) с пробой одной
// точкой и разреженным путём Зиппеля (Zippel), при отказе или useMod = false — субрезультантный PRS (Subresultant).
// Здесь же НОК, содержание/примитивная часть и арифметика рациональных функций как пар (числитель, знаменатель).
module PolyGcd

open System.Numerics
open Rational
open MPoly
open ModArith
open ModGcd
open Subresultant
open Zippel

let modularPrimitiveGcd (gcdFn: MPoly -> MPoly -> MPoly) (contentFn: MPoly -> MPoly)
                        (pa0: MPoly) (pb0: MPoly) : MPoly option =
    let pa, pb = unitNormal pa0, unitNormal pb0
    let x = mainVar pa
    // gamma = НОД старших коэффициентов в Z[y]: примитивный НОД (gcdFn нормирует) × НОД целых содержаний
    // (лениво: проба одной точкой может доказать взаимную простоту раньше, чем понадобится рекурсивный НОД)
    let gamma =
        lazy (
            let la, lb = lcMain pa, lcMain pb
            let ia = fst (fst (primitiveInt la))
            let ib = fst (fst (primitiveInt lb))
            let gi = BigInteger.GreatestCommonDivisor (ia, ib)
            mulConst (gi, 1I) (if isConst la || isConst lb then one else gcdFn la lb))
    let ys = varsOf pb (varsOf pa Set.empty) |> Set.remove x |> Set.toList |> List.rev
    let la, lb = fst (leadConst pa), fst (leadConst pb)
    let primes = modPrimes.Force()
    let mutable g = zero
    let mutable m = 1I
    let mutable curDeg = -1
    let mutable result : MPoly option = None
    let mutable finished = false
    let mutable idx = 0
    let mutable probed = false
    let mutable bound = System.Int32.MaxValue
    while not finished && idx < primes.Length do
        let p = primes.[idx]
        idx <- idx + 1
        let bp = BigInteger p
        if not (la % bp).IsZero && not (lb % bp).IsZero then
            let za, zb = zpOfPoly p pa, zpOfPoly p pb
            if not probed && not ys.IsEmpty then
                // проба одной точкой (на первом пригодном простом): взаимная простота доказана → 1,
                // иначе — верхняя граница deg_x НОД для всех простых
                probed <- true
                let st = probeStats ()
                st.[0] <- st.[0] + 1
                match probeDegree p x ys za zb (Rng 20271014UL) 3 with
                | Some 0 ->
                    st.[1] <- st.[1] + 1
                    result <- Some one
                    finished <- true
                | Some d ->
                    st.[2] <- st.[2] + 1
                    bound <- d
                | None -> ()
                // разреженный путь Зиппеля (LINZIP); отказ — Браун ниже
                if not finished && zippelWanted ys bound then
                    match linzipM pa pb x ys bound (Rng 20271015UL) with
                    | Some r ->
                        result <- Some r
                        finished <- true
                    | None -> ()
            if not finished then
              match gcdPB bound p x ys za zb (zpOfPoly p (gamma.Force())) with
              | None -> ()
              | Some r ->
                let dr = degX x r
                if dr = 0 then
                    result <- Some one
                    finished <- true
                else
                    if curDeg < 0 || dr < curDeg then
                        curDeg <- dr
                        g <- zero
                        m <- 1I
                    if dr = curDeg then
                        let g2 = crtPoly p m g r
                        let stable = not m.IsOne && g2 = g
                        g <- g2
                        m <- m * bp
                        if stable then
                            let c = contentFn g
                            let cand = unitNormal (if isConst c then g else divExactExn g c)
                            if divExact pa cand |> Option.isSome && divExact pb cand |> Option.isSome then
                                result <- Some cand
                                finished <- true
    result

// Исход модулярного пути в терминах единого контракта (Outcome): Answer g — НОД найден и проверен точным делением;
// Unknown — простые исчерпаны без проверенного кандидата (вызывающий падает на субрезультантный PRS)
let modularPrimitiveGcdOutcome (gcdFn: MPoly -> MPoly -> MPoly) (contentFn: MPoly -> MPoly)
                               (pa0: MPoly) (pb0: MPoly) : Outcome.Outcome<MPoly> =
    Outcome.ofOption "модулярный алгоритм отказал: простые исчерпаны без проверенного кандидата"
        (modularPrimitiveGcd gcdFn contentFn pa0 pb0)

// Единственный экземпляр исхода «модулярный путь не нужен» (в горячем пути gcd — без выделений памяти)
let private modularSkipped : Outcome.Outcome<MPoly> =
    Outcome.Unknown "модулярный путь не нужен: мелкая задача (быстрее PRS) или режим только PRS"

// Когда включать модулярный путь: мелкие одномерные задачи быстрее решает PRS (нет накладных расходов
// на простые и интерполяцию), многомерные и одномерные высокой степени — модулярный алгоритм
let private modularWorthwhile (pa: MPoly) (pb: MPoly) : bool =
    let univ (p: MPoly) = match p with Poly (_, cs) -> cs |> Array.forall isConst | _ -> true
    let d = max (degMain pa) (degMain pb)
    if univ pa && univ pb then d >= 12 else d >= 2

// Многомерный НОД: рекурсивно по главной переменной; содержание — НОД коэффициентов,
// примитивные части — модулярный алгоритм Брауна (useMod = true), при отказе или useMod = false —
// субрезультантный PRS (коэффициенты не раздуваются).
// Результат нормирован (unitNormal): целые взаимно простые коэффициенты, положительный старший.
let rec private gcdImpl (useMod: bool) (a: MPoly) (b: MPoly) : MPoly =
    if isZero a then unitNormal b
    elif isZero b then unitNormal a
    else
        let va, vb = mainVar a, mainVar b
        if va < 0 && vb < 0 then one
        elif va > vb then gcdImpl useMod (contentMainImpl useMod a) b
        elif vb > va then gcdImpl useMod a (contentMainImpl useMod b)
        else
            let ca, cb = contentMainImpl useMod a, contentMainImpl useMod b
            let g = gcdImpl useMod ca cb
            let pa, pb = divExactExn a ca, divExactExn b cb
            let h =
                let viaMod =
                    if useMod && modularWorthwhile pa pb then
                        modularPrimitiveGcdOutcome (gcdImpl useMod) (contentMainImpl useMod) pa pb
                    else modularSkipped
                match viaMod with
                | Outcome.Answer h -> h
                | _ -> primitivePrs pa pb
            let h = if isConst h then h else divExactExn h (contentMainImpl useMod h)
            unitNormal (mul g h)

and private contentMainImpl (useMod: bool) (p: MPoly) : MPoly =
    match p with
    | Const _ -> if isZero p then zero else one
    | Poly (_, cs) ->
        let mutable g = zero
        for c in cs do
            if not (isOne g) then g <- gcdImpl useMod g c
        g

// Публичный НОД (модулярный с запасным PRS) и НОД только через PRS (для сверки в тестах)
let gcd (a: MPoly) (b: MPoly) : MPoly = gcdImpl true a b
let gcdPrs (a: MPoly) (b: MPoly) : MPoly = gcdImpl false a b
let contentMain (p: MPoly) : MPoly = contentMainImpl true p

// Только модулярный путь (для тестов): pa, pb примитивны по общей главной переменной;
// None — модулярный алгоритм отказал (тогда gcd падает на PRS)
let tryModularPrimitiveGcd (pa: MPoly) (pb: MPoly) : MPoly option =
    modularPrimitiveGcd (gcdImpl true) (contentMainImpl true) pa pb

// НОК (нормированный)
let lcm (a: MPoly) (b: MPoly) : MPoly =
    if isZero a || isZero b then zero
    else unitNormal (divExactExn (mul a b) (gcd a b))

// Примитивная часть и содержание по главной переменной: p = content * pp
let contentAndPrimitive (p: MPoly) : MPoly * MPoly =
    match p with
    | Const _ -> (p, one)
    | Poly _ ->
        let c = contentMain p
        (c, divExactExn p c)

// --- Рациональные функции как пары (числитель, знаменатель) ---

// Сокращение на НОД; знаменатель — целый примитивный положительный (рациональный
// множитель уходит в числитель)
let normalizeFrac ((n, d): MPoly * MPoly) : MPoly * MPoly =
    if isZero d then failwith "Деление на ноль"
    elif isZero n then (zero, one)
    else
        let g = if isConst d || isConst n then one else gcd n d
        let n1, d1 = (if isOne g then n else divExactExn n g), (if isOne g then d else divExactExn d g)
        let (c, dp) = primitiveInt d1
        (mulConst (ratDiv (1I, 1I) c) n1, dp)

// Сложение пар с НОД знаменателей (знаменатель — НОК, а не произведение)
let fracAdd ((n1, d1): MPoly * MPoly) ((n2, d2): MPoly * MPoly) : MPoly * MPoly =
    if d1 = d2 then (add n1 n2, d1)
    elif isOne d1 then (add (mul n1 d2) n2, d2)
    elif isOne d2 then (add n1 (mul n2 d1), d1)
    else
        let g = gcd d1 d2
        let d2g = divExactExn d2 g
        let d1g = divExactExn d1 g
        (add (mul n1 d2g) (mul n2 d1g), mul d1 d2g)

let fracMul ((n1, d1): MPoly * MPoly) ((n2, d2): MPoly * MPoly) : MPoly * MPoly =
    (mul n1 n2, mul d1 d2)
