// Бесквадратное разложение и разложение многочленов на множители над ℤ (Шаг 17, коммит 2)
//
// Многочлен p = c · Π f_i^e_i, c — рациональная константа (со знаком), f_i — неприводимые
// примитивные (целые взаимно простые коэффициенты, положительный старший), попарно различные.
// Что умеем:
//   * содержание по главной переменной и по каждой другой переменной (рекурсивно);
//   * бесквадратное разложение — алгоритм Юна по главной переменной;
//   * одномерные — Цассенхауз (UniFactor.fs);
//   * однородные двумерные — подстановкой y = 1 и обратной гомогенизацией;
//   * многомерные (Шаг 21f) — полный EEZ Ванга: точка по условиям Ванга, предсказание старших
//     коэффициентов (`distributeLc`), p-адический подъём одномерных и многомерный Хензель mod p^l
//     (ModPoly.henselMulti) сразу для всех множителей; откаты — смена точки, рекомбинация подмножеств.
// Результат ВСЕГДА проверяется точным произведением в MPoly; при исчерпании лимита попыток (300),
// отсутствии подходящей точки или провале подъёма многочлен возвращается как есть — результат никогда
// не неверен, но может остаться приводимым.
module PolyFactor

open System.Numerics
open Rational
open MPoly
open PolyGcd

// Алгоритм Юна по главной переменной: примитивный (по главной переменной) нормированный f
// → [(a_i, i)], f = Π a_i^i, a_i бесквадратны и попарно взаимно просты
let sqfreeMain (f: MPoly) : (MPoly * int) list =
    let v = mainVar f
    let f' = deriv v f
    let a0 = gcd f f'
    let mutable b = divExactExn f a0
    let mutable c = divExactExn f' a0
    let mutable d = sub c (deriv v b)
    let res = ResizeArray<MPoly * int>()
    let mutable i = 1
    while not (isConst b) do
        let a = gcd b d
        if not (isConst a) then res.Add (a, i)
        b <- divExactExn b a
        c <- divExactExn d a
        d <- sub c (deriv v b)
        i <- i + 1
    List.ofSeq res

// Объединение списков множителей: равные складываются по кратности
let private merge (fs: (MPoly * int) list) : (MPoly * int) list =
    let res = ResizeArray<MPoly * int>()
    for (f, e) in fs do
        match res.FindIndex (fun (g, _) -> g = f) with
        | -1 -> res.Add (f, e)
        | i -> res.[i] <- (f, snd res.[i] + e)
    List.ofSeq res

// Номера переменных, входящих в многочлен
let rec private varsOf (p: MPoly) : Set<int> =
    match p with
    | Const _ -> Set.empty
    | Poly (v, cs) -> cs |> Array.fold (fun acc c -> Set.union acc (varsOf c)) (Set.singleton v)

// Содержание по переменной w: НОД коэффициентов при её степенях
let private contentWrt (w: int) (p: MPoly) : MPoly =
    let mutable g = zero
    for k in 0 .. degIn w p do
        if not (isOne g) then g <- gcd g (coeffIn w k p)
    g

// Одномерный многочлен (все коэффициенты — числа) → массив целых; p нормирован
let private toZPoly (p: MPoly) : BigInteger[] option =
    match p with
    | Poly (_, cs) ->
        let ints = cs |> Array.map (fun c -> match c with Const (n, d) when d.IsOne -> Some n | _ -> None)
        if ints |> Array.forall Option.isSome then Some (ints |> Array.map Option.get) else None
    | _ -> None

// Однородный ли многочлен (все мономы одной полной степени)
let private isHomogeneous (p: MPoly) : bool =
    let degs = monomials p |> List.map (fun (_, ms) -> ms |> List.sumBy snd) |> List.distinct
    degs.Length <= 1

// --- Многомерное разложение (Шаг 21e; с шага 21f — полный EEZ Ванга, см. ниже) ---

// Одномерный целочисленный многочлен (все коэффициенты — целые константы) → массив целых
let private intCoeffs (p: MPoly) : BigInteger[] option =
    match p with
    | Poly (_, cs) ->
        let ints = cs |> Array.map (fun c -> match c with Const (n, d) when d.IsOne -> Some n | _ -> None)
        if ints |> Array.forall Option.isSome then Some (ints |> Array.map Option.get) else None
    | _ -> None

// Подмножества индексов размера s из 0..r-1 (по возрастанию)
let rec private combos (r: int) (s: int) (start: int) : int list seq =
    if s = 0 then Seq.singleton []
    else
        seq {
            for i in start .. r - s do
                for rest in combos r (s - 1) (i + 1) do
                    yield i :: rest
        }

let private maxSplitAttempts = 300

// --- Шаг 21f: полный EEZ Ванга (Wang 1978; Geddes–Czapor–Labahn гл. 6) ---
//
// Для бесквадратного примитивного по x многочлена a с L = lc_x a ∈ ℤ[y]:
//  1. L = Ω · Π F_j^e_j (factorPoly); точка α подходит (условия Ванга), если deg_x сохраняется, образ бесквадратен
//     и у каждого F̃_j = F_j(α) ≠ 0 есть простой делитель, не делящий Ω, δ = cont a(x,α) и F̃_i, i < j;
//  2. образ раскладывается над ℤ: u_1..u_r; `distributeLc` предсказывает старшие коэффициенты C_i истинных
//     множителей (порядок j = k..1 важен), домножая u_i и a на степени δ при необходимости;
//  3. p-адический подъём: простое p, M = p^l > 2B (B — граница коэффициентов делителей), u_i поднимаются до M
//     (UniFactor.liftAll, унитарные; затем × C_i(α)), далее многомерный Хензель mod M (ModPoly.henselMulti)
//     по всем переменным сразу; симметричные вычеты, unitNormal, проверка точным произведением в MPoly.
module MM = ModPoly

// Значение целочисленного многочлена в точке (al.[v] — значение переменной v)
let rec private evalNum (al: BigInteger[]) (p: MPoly) : BigInteger =
    match p with
    | Const (n, _) -> n
    | Poly (v, cs) ->
        let a = al.[v]
        let mutable acc = 0I
        for i in cs.Length - 1 .. -1 .. 0 do
            acc <- acc * a + evalNum al cs.[i]
        acc

// Образ a(x, α): одномерный по x многочлен (или константа)
let private evalToUni (x: int) (al: BigInteger[]) (p: MPoly) : MPoly =
    match p with
    | Poly (v, cs) when v = x -> mk x (cs |> Array.map (fun c -> Const (evalNum al c, 1I)))
    | _ -> Const (evalNum al p, 1I)

let private pointValues (size: int) (ys: int[]) (alphas: int[]) : BigInteger[] =
    let al = Array.create size 0I
    Array.iter2 (fun (y: int) (a: int) -> al.[y] <- BigInteger a) ys alphas
    al

// Сдвиг y → y + sign·α по всем переменным (точка подъёма становится нулём)
let private shiftBy (ys: int[]) (alphas: int[]) (sign: int) (p: MPoly) : MPoly =
    Array.fold2 (fun (p: MPoly) (y: int) (al: int) ->
        if al = 0 then p else subst y (add (var y) (ofInt (BigInteger (sign * al)))) p) p ys alphas

// Подходящая точка: α, одномерные множители образа, δ = содержание образа (со знаком старшего)
type private Cand = { Alphas: int[]; Us: UniFactor.ZPoly list; Delta: BigInteger }

// Условие (iii) Ванга: у каждого F̃_j есть простой делитель, не делящий Ω, δ и F̃_i (i < j).
// Простой делитель w = F̃_j без простых из M' ищется «снятием» общих с M' множителей (факторизация не нужна)
let private hasFreshPrime (ft: BigInteger[]) (omega: BigInteger) (delta: BigInteger) : bool =
    let mutable ok = true
    let mutable bad = BigInteger.Abs omega * BigInteger.Abs delta
    for j in 0 .. ft.Length - 1 do
        if ok then
            let f = BigInteger.Abs ft.[j]
            if f.IsZero then ok <- false
            else
                let mutable w = f
                let mutable g = BigInteger.GreatestCommonDivisor (w, bad)
                while g > 1I do
                    w <- w / g
                    g <- BigInteger.GreatestCommonDivisor (w, bad)
                if w.IsOne then ok <- false
                bad <- bad * f
    ok

let private evalCandidate (a: MPoly) (x: int) (ys: int[]) (da: int) (omega: BigInteger)
                          (lfs: (MPoly * int) list) (alphas: int[]) : Cand option =
    let al = pointValues (x + 1) ys alphas
    let img = evalToUni x al a
    if mainVar img <> x || degMain img <> da then None
    else
        match intCoeffs img with
        | None -> None
        | Some zs ->
            let prim = UniFactor.primitiveZ zs
            let delta = zs.[zs.Length - 1] / prim.[prim.Length - 1]
            let ft = lfs |> List.map (fun (f, _) -> evalNum al f) |> Array.ofList
            if not (hasFreshPrime ft omega delta) then None
            elif not (isConst (gcd img (deriv x img))) then None
            else
                match (try Some (UniFactor.factorSquarefreeFull prim) with _ -> None) with
                | Some fs when not fs.IsEmpty -> Some { Alphas = alphas; Us = fs; Delta = delta }
                | _ -> None

// Предсказание старших коэффициентов (Wang 1978 §4).
// Вход: ys — переменные L; lcFactors — F_j с кратностями; omega — целое содержание L; alphas — точка;
// us — одномерные множители образа; delta — δ. Результат: C_i (в исходных координатах), скорректированные
// u_i (lc u_i = C_i(α)) и итоговое δ' (a следует домножить на δ'^(r−1)); None — точка несчастливая
// (F̃_j не делятся, кратности не сошлись, δ не делится, Π C_i ≠ δ'^(r−1)·L)
let distributeLc (ys: int[]) (lcFactors: (MPoly * int) list) (omega: BigInteger) (alphas: int[])
                 (us: UniFactor.ZPoly[]) (delta: BigInteger) : (MPoly[] * UniFactor.ZPoly[] * BigInteger) option =
    let r = us.Length
    let al = pointValues ((if ys.Length = 0 then 0 else Array.max ys) + 1) ys alphas
    let fl = Array.ofList lcFactors
    let k = fl.Length
    let ft = fl |> Array.map (fun (f, _) -> evalNum al f)
    if delta.IsZero || ft |> Array.exists (fun v -> v.IsZero || BigInteger.Abs(v).IsOne) then None
    else
        let total = Array.zeroCreate<int> k
        let cs = Array.create r one
        let mutable ok = true
        for i in 0 .. r - 1 do
            let li = us.[i].[us.[i].Length - 1]
            let mutable d = li * delta
            // от последнего F_j к первому — важно (простые q_j различают F̃_j только в таком порядке)
            for j in k - 1 .. -1 .. 0 do
                while ok && (BigInteger.Remainder (d, ft.[j])).IsZero do
                    d <- d / ft.[j]
                    cs.[i] <- mul cs.[i] (fst fl.[j])
                    total.[j] <- total.[j] + 1
                    if total.[j] > snd fl.[j] then ok <- false
        if not ok || (Array.exists2 (fun t (_, e) -> t <> e) total fl) then None
        else
            let us2 = Array.copy us
            let mutable delta2 = delta
            for i in 0 .. r - 1 do
                if ok then
                    let li = us.[i].[us.[i].Length - 1]
                    let ch = evalNum al cs.[i]
                    let g = BigInteger.GreatestCommonDivisor (li, ch)
                    let q = ch / g
                    if not (BigInteger.Remainder (delta2, q)).IsZero then ok <- false
                    else
                        cs.[i] <- mulConst (li / g, 1I) cs.[i]
                        us2.[i] <- us.[i] |> Array.map (fun c -> c * q)
                        delta2 <- delta2 / q
            if not ok then None
            else
                if not delta2.IsOne then
                    for i in 0 .. r - 1 do
                        cs.[i] <- mulConst (delta2, 1I) cs.[i]
                        us2.[i] <- us2.[i] |> Array.map (fun c -> c * delta2)
                // проверка: Π C_i = δ'^(r−1) · L, L = Ω · Π F_j^e_j (точно, как многочлены)
                let lFull =
                    fl |> Array.fold (fun acc (f, e) -> mul acc (pow f e)) (mulConst (omega, 1I) one)
                let lhs = cs |> Array.fold mul one
                let rhs = mulConst (BigInteger.Pow (delta2, r - 1), 1I) lFull
                if lhs = rhs then Some (cs, us2, delta2) else None

// Простые чуть меньше 2^31 (операции mod p — в int64, UniFactor работает с int)
let private bigPrimes : Lazy<int[]> =
    lazy (
        let isPrime (n: int64) =
            let mutable ok = true
            let mutable d = 3L
            while ok && d * d <= n do
                if n % d = 0L then ok <- false
                d <- d + 2L
            ok
        let res = ResizeArray<int>()
        let mutable c = 2147483647L
        while res.Count < 24 do
            if isPrime c then res.Add (int c)
            c <- c - 2L
        res.ToArray())

// Всё, что не зависит от разбиения множителей на группы: сдвинутый a (с поправкой δ'^(r−1)) mod M,
// сдвинутые lc, одномерные множители, поднятые до M (унитарные), значения lc при y = 0
type private LiftPrep =
    { X: int
      Ys: int[]
      Alphas: int[]
      Md: MM.Mod
      AM: MM.MPolyM
      CsM: MM.MPolyM[]
      Us: UniFactor.ZPoly[]
      Lc0: BigInteger[] }

let private prepareLift (a: MPoly) (x: int) (ys: int[]) (alphas: int[]) (cs: MPoly[])
                        (us: UniFactor.ZPoly[]) (delta2: BigInteger) : LiftPrep option =
    let r = us.Length
    let aCorr = if delta2.IsOne then a else mulConst (BigInteger.Pow (delta2, r - 1), 1I) a
    let aS = shiftBy ys alphas 1 aCorr
    let csS = cs |> Array.map (shiftBy ys alphas 1)
    let a0 = ys |> Array.fold (fun q y -> coeffIn y 0 q) aS
    match intCoeffs a0 with
    | None -> None
    | Some a0z ->
        let lc0 = a0z.[a0z.Length - 1]
        // простое: p ∤ lc, a0 mod p бесквадратен
        let pick =
            bigPrimes.Force() |> Array.tryFind (fun p ->
                let bp = BigInteger p
                if (BigInteger.Remainder (lc0, bp)).IsZero then false
                else
                    let ap = a0z |> Array.map (fun c -> int (((BigInteger.Remainder (c, bp)) + bp) % bp)) |> UniFactor.trimP
                    ap.Length = a0z.Length && (UniFactor.gcdP p ap (UniFactor.derivP p ap)).Length = 1)
        match pick with
        | None -> None
        | Some p ->
            let bp = BigInteger p
            // граница: B = 2^(deg_x a + Σ deg_y a) · ‖a‖₂, M = p^l > 2B
            let sumSq = ref 0I
            iterConsts (fun (n, _) -> sumSq.Value <- sumSq.Value + n * n) aS
            let degSum = degMain aS + (ys |> Array.sumBy (fun y -> degIn y aS))
            let bound = BigInteger.Pow (2I, degSum) * (isqrtBigint sumSq.Value + 1I)
            let mutable bigM = bp
            while bigM <= 2I * bound do bigM <- bigM * bp
            let md : MM.Mod = { M = bigM; P = bp }
            let invLc = MM.invMod lc0 bigM
            let fM = a0z |> Array.map (fun c -> (((c * invLc) % bigM) + bigM) % bigM)
            let facs =
                us |> Array.map (fun u ->
                    UniFactor.monicP p (u |> Array.map (fun c -> int (((BigInteger.Remainder (c, bp)) + bp) % bp)) |> UniFactor.trimP))
                |> List.ofArray
            let lifted = UniFactor.liftAll fM facs p bigM |> Array.ofList
            Some { X = x; Ys = ys; Alphas = alphas; Md = md
                   AM = MM.ofMPoly md aS
                   CsM = csS |> Array.map (MM.ofMPoly md)
                   Us = lifted
                   Lc0 = us |> Array.map (fun u -> (((u.[u.Length - 1] % bigM) + bigM) % bigM)) }

// Подъём для разбиения множителей на группы (каждая группа — список индексов u_i): результат — истинные
// множители a (нормированные), по одному на группу; None — подъём не удался
let private liftGroups (pp: LiftPrep) (groups: int list[]) : MPoly list option =
    let md = pp.Md
    let uniM (z: BigInteger[]) : MM.MPolyM = MM.mk pp.X (z |> Array.map MM.MC)
    let groupU (g: int list) = g |> List.fold (fun acc i -> MM.mul md acc (uniM pp.Us.[i])) MM.one
    let groupLcs (g: int list) = g |> List.fold (fun acc i -> MM.mul md acc pp.CsM.[i]) MM.one
    let groupLc0 (g: int list) = g |> List.fold (fun acc i -> (acc * pp.Lc0.[i]) % md.M) 1I
    let fs0 = groups |> Array.map (fun g -> MM.mulConst md (groupLc0 g) (groupU g))
    let lcs = groups |> Array.map groupLcs
    match MM.henselMulti md pp.X pp.Ys pp.AM lcs fs0 with
    | None -> None
    | Some fs ->
        Some (fs |> Array.map (fun f -> unitNormal (shiftBy pp.Ys pp.Alphas -1 (MM.toMPoly md f))) |> List.ofArray)

// Счётчики путей многомерной факторизации (для тестов и отладки): [0] — полный подъём удался,
// [1] — рекомбинация подмножеств, [2] — откат на запасной путь/«как есть»
// (по потокам: тесты идут параллельно; счётчики и флаг принадлежат вызывающему потоку; реестр AlgoStats, группа «factor.wang»)
let private statsGroup = AlgoStats.register "factor.wang" [| "full-lift"; "subset-recombination"; "fallback" |]
let stats () : int[] = statsGroup.Values

// Тестовый крючок: пропустить полный подъём, чтобы проверить рекомбинацию подмножеств на обычных входах
let skipFullLift = new System.Threading.ThreadLocal<bool>(fun () -> false)

// Разложение бесквадратного примитивного (по главной переменной) нормированного a (>= 2 переменных)
// на неприводимые; None — не получилось (нет подходящей точки). «Как есть» (Some [a]) — подъём и
// рекомбинация не нашли разложения (неприводим или лимит попыток)
let rec private tryMultiFactor (a: MPoly) : MPoly list option =
    let x = mainVar a
    let ys = Array.ofList (varsOf a |> Set.remove x |> Set.toList)
    let da = degMain a
    if da <= 1 then Some [a]
    else
        // L = Ω · Π F_j^e_j: factorPoly определён ниже (взаимная рекурсия), поэтому раскладываем через factorUnit
        let ((omega, _), lPrim) = primitiveInt (lcMain a)
        let lfs = if isConst lPrim then [] else factorUnit lPrim
        // 1. подходящие точки (условия Ванга): нули, затем детерминированные случайные ±3, ±10, ±50
        let rnd = System.Random 20271013
        let seen = System.Collections.Generic.HashSet<string>()
        let cands = ResizeArray<Cand>()
        let mutable attempts = 0
        let mutable stop = false
        // до 10 подходящих точек; если уже 4 и все дают не больше 3 множителей — достаточно (выбор лучшей r
        // нужен при большом r; для малого r повторные точки только подтверждают то же число множителей)
        let enough () = cands.Count >= 10 || (cands.Count >= 4 && (cands |> Seq.map (fun c -> c.Us.Length) |> Seq.min) <= 3)
        while attempts < 150 && not (enough ()) && not stop do
            Cancel.check ()     // подшаг 22.4: прерывание по проверке на попытку подстановки
            let alphas : int[] =
                if attempts = 0 then Array.zeroCreate ys.Length
                else
                    let range = if attempts < 25 then 3 elif attempts < 60 then 10 else 50
                    ys |> Array.map (fun _ -> rnd.Next(-range, range + 1))
            attempts <- attempts + 1
            if seen.Add (System.String.Join (",", alphas)) then
                match evalCandidate a x ys da omega lfs alphas with
                | Some c ->
                    cands.Add c
                    if c.Us.Length = 1 then stop <- true
                | None -> ()
        if cands.Count = 0 then None
        else
            // с наименьшим числом одномерных множителей (сортировка устойчива)
            let sorted = cands |> Seq.sortBy (fun c -> c.Us.Length) |> List.ofSeq
            if sorted.Head.Us.Length = 1 then Some [a]
            else
                // предсказание lc + подготовка подъёма в точке (лениво, один раз на точку)
                let prepare (c: Cand) : LiftPrep option =
                    match (try distributeLc ys lfs omega c.Alphas (Array.ofList c.Us) c.Delta with _ -> None) with
                    | None -> None
                    | Some (cs, us2, delta2) -> (try prepareLift a x ys c.Alphas cs us2 delta2 with _ -> None)
                let verified (parts: MPoly list) = (parts |> List.fold mul one) = a
                let attempt (pp: LiftPrep) (groups: int list[]) : MPoly list option =
                    match (try liftGroups pp groups with _ -> None) with
                    | Some parts when verified parts && parts |> List.forall (fun f -> not (isConst f)) -> Some parts
                    | _ -> None
                let preps = sorted |> List.truncate 5 |> List.map (fun c -> (c, lazy (prepare c)))
                // 2. полный подъём всех r множителей; провал (или проверки) — следующая точка, до 5
                let full =
                    if skipFullLift.Value then None
                    else
                        preps |> List.tryPick (fun (c, pp) ->
                            match pp.Force () with
                            | Some p -> attempt p (Array.init c.Us.Length (fun i -> [i]))
                            | None -> None)
                match full with
                | Some parts ->
                    stats().[0] <- stats().[0] + 1
                    Some parts
                | None ->
                    // 3. лишние одномерные множители (истинный множитель — произведение нескольких u_i):
                    // рекомбинация подмножеств в лучшей из точек; пара (u_S, остаток) поднимается тем же
                    // henselMulti с C_S = Π C_i; размеры по возрастанию, лимит попыток — maxSplitAttempts
                    let usable = preps |> List.tryPick (fun (c, pp) -> pp.Force () |> Option.map (fun p -> (c, p)))
                    let asIs () =
                        stats().[2] <- stats().[2] + 1
                        Some [a]
                    match usable with
                    | Some (c, pp) when c.Us.Length > 2 ->
                        let r = c.Us.Length
                        let budget = ref maxSplitAttempts
                        let found =
                            seq { 1 .. r / 2 }
                            |> Seq.tryPick (fun s ->
                                combos r s 0 |> Seq.tryPick (fun idx ->
                                    // при 2s = r подмножество и дополнение дают одну пару — берём то, где есть 0
                                    if 2 * s = r && not (List.contains 0 idx) then None
                                    elif budget.Value <= 0 then None
                                    else
                                        budget.Value <- budget.Value - 1
                                        let rest = [ for i in 0 .. r - 1 do if not (List.contains i idx) then yield i ]
                                        match attempt pp [| idx; rest |] with
                                        | Some [fs; fr] -> Some (fs, fr)
                                        | _ -> None))
                        match found with
                        | Some (fs, fr) ->
                            stats().[1] <- stats().[1] + 1
                            // fs неприводим (меньшие подмножества уже проверены); остаток — заново (общего вида)
                            let restParts = factorSqfree fr |> List.map fst
                            Some (fs :: restParts)
                        | None -> asIs ()
                    | _ -> asIs ()

// Разложение бесквадратного примитивного по главной переменной нормированного a
and private factorSqfree (a: MPoly) : (MPoly * int) list =
    let v = mainVar a
    let vars = varsOf a
    if vars.Count = 1 then
        // одномерный: убрать степень x, остальное — Цассенхауз
        match a with
        | Poly (_, cs) ->
            let k = cs |> Array.findIndex (fun c -> not (isZero c))
            let rest = mk v (Array.sub cs k (cs.Length - k))
            let xFactor = if k > 0 then [(var v, 1)] else []
            match toZPoly rest with
            | Some zs when zs.Length > 1 ->
                let fs = UniFactor.factorSquarefreeFull (UniFactor.primitiveZ zs)
                xFactor @ (fs |> List.map (fun g -> (mk v (g |> Array.map ofInt), 1)))
            | _ -> xFactor @ (if isConst rest then [] else [(rest, 1)])
        | _ -> [(a, 1)]
    else
        // содержание по каждой другой переменной
        let others = vars |> Set.remove v |> Set.toList
        let withContent =
            others |> List.tryPick (fun w ->
                let cw = contentWrt w a
                if isConst cw then None else Some (cw, divExactExn a cw))
        match withContent with
        | Some (cw, pw) -> merge (factorUnit cw @ factorUnit (unitNormal pw))
        | None ->
            if vars.Count = 2 && isHomogeneous a then
                let w = others.Head
                let g = subst w one a
                match toZPoly g with
                | Some zs when mainVar g = v ->
                    let fs = UniFactor.factorSquarefreeFull (UniFactor.primitiveZ zs)
                    let homog (z: BigInteger[]) : MPoly =
                        let k = z.Length - 1
                        let mutable r = zero
                        for i in 0 .. k do
                            if not z.[i].IsZero then
                                r <- add r (mulConst (z.[i], 1I) (mul (pow (var v) i) (pow (var w) (k - i))))
                        r
                    let parts = fs |> List.map homog
                    // проверка: произведение гомогенизаций должно дать a
                    if parts |> List.fold mul one = a then parts |> List.map (fun f -> (f, 1))
                    else [(a, 1)]
                | _ -> [(a, 1)]
            else
                match (try tryMultiFactor a with _ -> None) with
                | Some fs -> fs |> List.map (fun f -> (f, 1))
                | None -> [(a, 1)]

// Неконстантный нормированный p: все неприводимые множители с кратностями
and private factorUnit (p: MPoly) : (MPoly * int) list =
    if isConst p then []
    else
        let (cont, prim) = contentAndPrimitive p
        let contFactors = if isConst cont then [] else factorUnit (unitNormal cont)
        let primN = unitNormal prim
        let primFactors =
            if isConst primN then []
            else
                sqfreeMain primN
                |> List.collect (fun (a, k) -> factorSqfree a |> List.map (fun (f, m) -> (f, m * k)))
        merge (contFactors @ primFactors)

// Разложение многочлена: рациональная константа и неприводимые множители с кратностями
let factorPoly (p: MPoly) : Q * (MPoly * int) list =
    if isZero p then ((0I, 1I), [])
    else
        let (c, pp) = primitiveInt p
        if isConst pp then (c, [])
        else (c, factorUnit pp)

// Бесквадратное разложение: константа и [(a_i, i)], p = c · Π a_i^i (a_i не обязательно неприводимы)
let sqfreePoly (p: MPoly) : Q * (MPoly * int) list =
    if isZero p then ((0I, 1I), [])
    else
        let (c, pp) = primitiveInt p
        if isConst pp then (c, [])
        else
            let rec sq (q: MPoly) : (MPoly * int) list =
                if isConst q then []
                else
                    let (ct, pr) = contentAndPrimitive q
                    let own = if isConst (unitNormal pr) then [] else sqfreeMain (unitNormal pr)
                    merge ((if isConst ct then [] else sq (unitNormal ct)) @ own)
            (c, sq pp)

// Рациональная функция: (числитель, знаменатель) → константа, множители числителя, множители знаменателя
let factorRatFun ((n, d): MPoly * MPoly) : Q * (MPoly * int) list * (MPoly * int) list =
    let (n, d) = normalizeFrac (n, d)
    let (cn, fn) = factorPoly n
    let (cd, fd) = factorPoly d
    (ratDiv cn cd, fn, fd)
