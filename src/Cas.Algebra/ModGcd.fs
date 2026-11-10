// Модулярный НОД Брауна и проба одной точкой (шаги 21e, 21g); вынесено из MPoly.fs в шаге 21h'.
//
// Для примитивных по главной переменной x целочисленных pa, pb: по большим простым p (< 2^31)
// НОД считается в Z_p[y1..yk][x] рекурсивно — вычислением в точках (y_k = 0, 1, 2, ...), интерполяцией
// Ньютона по y_k; на листе (одна переменная x) — алгоритм Евклида над Z_p. Нормировка: старший по x
// коэффициент образа равен gamma = НОД(lc pa, lc pb) (взятому в Z_p), поэтому образы согласованы
// между точками и простыми. Образы по разным простым склеиваются КТО (симметричные вычеты); когда
// очередной простой не меняет результат, кандидат (примитивная часть) проверяется точным делением
// pa и pb — результат поэтому ВСЕГДА верен. Плохие простые/точки (падение степени, лишняя степень
// НОД) отбрасываются: берётся минимальная степень по x. Исчерпание простых → None (запасной PRS).
// Драйвер (выбор простых, Браун / Зиппель, проверка делением) — PolyGcd.modularPrimitiveGcd.
module ModGcd

open System.Numerics
open MPoly
open ModArith

// Образ многочлена над Z_p: рекурсивное плотное представление (как MPoly, но коэффициенты — int64)
type ZP =
    | ZC of int64
    | ZPoly of int * ZP[]

let zpVar (z: ZP) = match z with ZC _ -> -1 | ZPoly (v, _) -> v
let zpIsZero (z: ZP) = match z with ZC 0L -> true | _ -> false

let zpMk (v: int) (cs: ZP[]) : ZP =
    let mutable n = cs.Length
    while n > 0 && zpIsZero cs.[n - 1] do n <- n - 1
    if n = 0 then ZC 0L
    elif n = 1 then cs.[0]
    elif n = cs.Length then ZPoly (v, cs)
    else ZPoly (v, Array.sub cs 0 n)

let rec zpAdd (p: int64) (a: ZP) (b: ZP) : ZP =
    match a, b with
    | ZC x, ZC y -> let s = x + y in ZC (if s >= p then s - p else s)
    | ZPoly (v, ca), ZPoly (w, cb) when v = w ->
        let n = max ca.Length cb.Length
        zpMk v (Array.init n (fun i ->
            if i >= ca.Length then cb.[i]
            elif i >= cb.Length then ca.[i]
            else zpAdd p ca.[i] cb.[i]))
    | ZPoly (v, ca), _ when v > zpVar b ->
        let cs = Array.copy ca
        cs.[0] <- zpAdd p cs.[0] b
        zpMk v cs
    | _, ZPoly (w, cb) when w > zpVar a ->
        let cs = Array.copy cb
        cs.[0] <- zpAdd p a cs.[0]
        zpMk w cs
    | _ -> failwith "MPoly.zpAdd: нарушен порядок переменных"

let rec zpNeg (p: int64) (z: ZP) : ZP =
    match z with
    | ZC x -> ZC (if x = 0L then 0L else p - x)
    | ZPoly (v, cs) -> ZPoly (v, Array.map (zpNeg p) cs)

let zpSub (p: int64) (a: ZP) (b: ZP) : ZP = zpAdd p a (zpNeg p b)

// Умножение на скаляр l (1 <= l < p; p простое — старший коэффициент не обнуляется)
let rec zpScale (p: int64) (l: int64) (z: ZP) : ZP =
    match z with
    | ZC x -> ZC (x * l % p)
    | ZPoly (v, cs) -> ZPoly (v, Array.map (zpScale p l) cs)

// Степень по переменной y
let rec zpDegIn (y: int) (z: ZP) : int =
    match z with
    | ZC _ -> 0
    | ZPoly (w, cs) when w = y -> cs.Length - 1
    | ZPoly (w, cs) when w > y -> cs |> Array.map (zpDegIn y) |> Array.max
    | _ -> 0

// Значение в точке: подстановка w := alpha
let rec zpEval (p: int64) (w: int) (alpha: int64) (z: ZP) : ZP =
    match z with
    | ZC _ -> z
    | ZPoly (u, cs) when u = w ->
        let mutable acc = ZC 0L
        for i in cs.Length - 1 .. -1 .. 0 do
            acc <- zpAdd p (if zpIsZero acc then acc else zpScale p alpha acc) cs.[i]
        acc
    | ZPoly (u, cs) when u > w -> zpMk u (Array.map (zpEval p w alpha) cs)
    | _ -> z

let rec zpOfPoly (p: int64) (m: MPoly) : ZP =
    match m with
    | Const (n, _) -> ZC (int64 (((n % BigInteger p) + BigInteger p) % BigInteger p))
    | Poly (v, cs) -> zpMk v (Array.map (zpOfPoly p) cs)

let degX (x: int) (z: ZP) : int =
    match z with ZPoly (v, cs) when v = x -> cs.Length - 1 | _ -> 0

let zpToArr (x: int) (z: ZP) : int64[] =
    match z with
    | ZPoly (v, cs) when v = x -> cs |> Array.map (fun c -> match c with ZC k -> k | _ -> failwith "MPoly.zpToArr")
    | _ -> failwith "MPoly.zpToArr"

// Проверка взаимной простоты одной точкой (шаг 21g). a, b — примитивные по x. Случайная точка
// alpha из F_p^k (k = число переменных кроме x), в которой степени a и b по x сохраняются:
// deg gcd_x(a(alpha), b(alpha)) — верхняя граница deg_x НОД(a, b) над Z[y] (НОД образов делится на
// образ НОДа; старший коэффициент образа не ноль). Нулевая степень ДОКАЗЫВАЕТ взаимную простоту
// (НОД лежит в Z[y] и делит содержание, т.е. равен 1). Возвращает минимум степеней по успешным
// точкам (до tries штук; на нуле останавливается) либо None, если подходящих точек не нашлось.
let probeDegree (p: int64) (x: int) (ys: int list) (a: ZP) (b: ZP) (rng: Rng) (tries: int) : int option =
    let da, db = degX x a, degX x b
    let mutable best = -1
    let mutable good = 0
    let mutable attempts = 0
    while best <> 0 && good < tries && attempts < tries * 6 do
        attempts <- attempts + 1
        let mutable aa = a
        let mutable bb = b
        for y in ys do
            let alpha = rng.Range (1L, p - 1L)
            aa <- zpEval p y alpha aa
            bb <- zpEval p y alpha bb
        if degX x aa = da && degX x bb = db && da > 0 && db > 0 then
            good <- good + 1
            let g = gcdArr p (zpToArr x aa) (zpToArr x bb)
            let d = g.Length - 1
            if best < 0 || d < best then best <- d
    if best < 0 then None else Some best

// Счётчики проб (по потокам, для тестов; реестр AlgoStats, группа «gcd.probe»):
// [0] — вызовов, [1] — доказана взаимная простота, [2] — получена граница > 0
let private probeGroup = AlgoStats.register "gcd.probe" [| "calls"; "coprime-proved"; "bound-found" |]
let probeStats () : int[] = probeGroup.Values

// bound — верхняя граница deg_x НОД (из пробы одной точкой): образ с большей степенью — невезучая
// точка и пропускается (раньше невезучие отсеивались только «минимальной степенью»)
let rec gcdPB (bound: int) (p: int64) (x: int) (ys: int list) (a: ZP) (b: ZP) (gamma: ZP) : ZP option =
    let toArr (z: ZP) =
        match z with
        | ZPoly (v, cs) when v = x -> cs |> Array.map (fun c -> match c with ZC k -> k | _ -> failwith "MPoly.gcdP")
        | _ -> failwith "MPoly.gcdP"
    match ys with
    | [] ->
        let g = gcdArr p (toArr a) (toArr b)
        if g.Length = 1 then Some gamma
        else
            let gm = match gamma with ZC c -> c | _ -> failwith "MPoly.gcdP"
            Some (ZPoly (x, g |> Array.map (fun c -> ZC (c * gm % p))))
    | y :: rest ->
        let da, db = degX x a, degX x b
        let n = zpDegIn y gamma + min (zpDegIn y a) (zpDegIn y b) + 1
        let alphas = ResizeArray<int64>()
        let imgs = ResizeArray<ZP[]>()
        let mutable curDeg = -1
        let mutable coprime = false
        let mutable failed = false
        let mutable skipped = 0
        let mutable alpha = 0L
        while not coprime && not failed && alphas.Count < n do
            if alpha > 100000L then failed <- true
            else
                let aa = zpEval p y alpha a
                let bb = zpEval p y alpha b
                let gg = zpEval p y alpha gamma
                if degX x aa = da && degX x bb = db && not (zpIsZero gg) then
                    match gcdPB bound p x rest aa bb gg with
                    | None -> failed <- true
                    | Some r ->
                        let dr = degX x r
                        if dr = 0 then coprime <- true
                        elif dr > bound && skipped < n then
                            // невезучая точка: степень выше доказанной границы. Пропуск ограничен n точками:
                            // если невезучей оказалась внешняя точка (все образы этого уровня выше границы),
                            // подзадача должна завершиться образом степени > bound, а не бесконечным перебором —
                            // внешний уровень сам отбросит такой образ
                            skipped <- skipped + 1
                        else
                            if curDeg < 0 || dr < curDeg then
                                curDeg <- dr
                                alphas.Clear()
                                imgs.Clear()
                            if dr = curDeg then
                                match r with
                                | ZPoly (_, cs) -> alphas.Add alpha; imgs.Add cs
                                | _ -> failed <- true
                alpha <- alpha + 1L
        if failed then None
        elif coprime then Some gamma
        else
            let m = alphas.Count
            let newton (k: int) : ZP =
                let dd = Array.init m (fun i -> imgs.[i].[k])
                for j in 1 .. m - 1 do
                    for i in m - 1 .. -1 .. j do
                        let inv = invModL ((alphas.[i] - alphas.[i - j] + p) % p) p
                        dd.[i] <- zpScale p inv (zpSub p dd.[i] dd.[i - 1])
                let mutable poly : ZP[] = [| dd.[m - 1] |]
                for i in m - 2 .. -1 .. 0 do
                    let np = Array.create (poly.Length + 1) (ZC 0L)
                    for j in 0 .. poly.Length - 1 do
                        np.[j + 1] <- zpAdd p np.[j + 1] poly.[j]
                        if alphas.[i] <> 0L then
                            np.[j] <- zpSub p np.[j] (zpScale p alphas.[i] poly.[j])
                    np.[0] <- zpAdd p np.[0] dd.[i]
                    poly <- np
                zpMk y poly
            Some (zpMk x (Array.init (curDeg + 1) newton))

let gcdP (p: int64) (x: int) (ys: int list) (a: ZP) (b: ZP) (gamma: ZP) : ZP option =
    gcdPB System.Int32.MaxValue p x ys a b gamma

// КТО: склейка целочисленного G (по модулю M, симметричные вычеты) и образа g по модулю p
let crtPoly (p: int64) (m: BigInteger) (g0: MPoly) (z0: ZP) : MPoly =
    let bp = BigInteger p
    let minv = invModL (int64 (m % bp)) p
    let mp = m * bp
    let half = mp / 2I
    let scalar (n: BigInteger) (r: int64) : MPoly =
        let gm = int64 (((n % bp) + bp) % bp)
        let t = (((r - gm) % p + p) % p) * minv % p
        let v = n + m * BigInteger t
        ofInt (if v > half then v - mp else v)
    let rec go (g: MPoly) (z: ZP) : MPoly =
        match g, z with
        | Const (n, _), ZC r -> scalar n r
        | _ ->
            let top = max (mainVar g) (zpVar z)
            let cg = match g with Poly (v, cs) when v = top -> cs | _ -> [| g |]
            let cz = match z with ZPoly (v, cs) when v = top -> cs | _ -> [| z |]
            let n = max cg.Length cz.Length
            mk top (Array.init n (fun i ->
                go (if i < cg.Length then cg.[i] else zero) (if i < cz.Length then cz.[i] else ZC 0L)))
    go g0 z0

// Проба одной точкой для тестов: pa, pb примитивны по общей главной переменной; seed — детерминированный генератор;
// Some 0 — взаимная простота доказана, Some d — верхняя граница deg_x НОД, None — точка не найдена
let probeGcdDegree (pa: MPoly) (pb: MPoly) (seed: uint64) (tries: int) : int option =
    let pa, pb = unitNormal pa, unitNormal pb
    let x = mainVar pa
    let ys = varsOf pb (varsOf pa Set.empty) |> Set.remove x |> Set.toList |> List.rev
    let la, lb = fst (leadConst pa), fst (leadConst pb)
    let p = modPrimes.Force() |> Array.find (fun p -> not (la % BigInteger p).IsZero && not (lb % BigInteger p).IsZero)
    probeDegree p x ys (zpOfPoly p pa) (zpOfPoly p pb) (Rng seed) tries
