// Базисы Грёбнера: алгоритм Бухбергера (шаг 21i) — перенос на F# эталонной Lisp-версии lib\groebner.lisp
// (правило «сначала Lisp»: Lisp-версия — эталон для тестов, здесь — тот же алгоритм шаг в шаг, но на массивах).
// Причина переноса — замеры: в Lisp-версии ≈ 95 % времени — интерпретация циклов над мономами-списками
// (сравнение, делимость, НОК, умножение; car/cdr/null? — миллионы вызовов), рациональная арифметика — доли процента.
//
// Алгоритм (как в Lisp): GROEBNERNEWS2 Беккера–Вейспфеннинга (с. 232; структура книги):
// начальная интерредукция (BW с. 203), вставка образующих по возрастанию старших мономов, update с критериями
// Гебауэра–Мёллера (M, F — новые пары, B_k — старые, критерий произведения — после отсева), выбор пары — нормальная
// стратегия (минимум НОК в порядке) или sugar, полная редукция S-многочлена по базису (делители по возрастанию
// старших мономов), единичный идеал — ранний выход, приведённый базис. Порядок пар/элементов, тай-брейки и
// счётчики совпадают с Lisp-версией (тест сравнивает базисы и счётчики).
//
// Представление: моном — int[] (0: полная степень, 1..n: показатели), терм — коэффициент ℚ (кортеж) и моном,
// многочлен — массив термов по УБЫВАНИЮ в текущем порядке, нуль — пустой массив.
module Groebner

open System
open System.Numerics
open Rational

type Q = BigInteger * BigInteger

[<Struct>]
type Term = { C: Q; M: int[] }

type Poly = Term[]

// Порядок мономов: lex, grlex, grevlex; Block k — grevlex по первым k переменным, при равенстве — по остальным
type Order =
    | Lex
    | GrLex
    | GrevLex
    | Block of int

let orderOfName (s: string) : Order =
    match s with
    | "lex" -> Lex
    | "grlex" -> GrLex
    | "grevlex" -> GrevLex
    | _ -> invalidArg "order" (sprintf "groebner: порядок — lex, grlex или grevlex, получено %s" s)

// обратный лексикографический хвост на [from, upto): последний отличающийся показатель; меньший → моном больше
let inline private revlex (a: int[]) (b: int[]) (from: int) (upto: int) : int =
    let mutable r = 0
    let mutable i = upto - 1
    while r = 0 && i >= from do
        if a.[i] < b.[i] then r <- 1
        elif a.[i] > b.[i] then r <- -1
        i <- i - 1
    r

let private cmpLex (a: int[]) (b: int[]) (from: int) : int =
    let mutable r = 0
    let mutable i = from
    while r = 0 && i < a.Length do
        if a.[i] < b.[i] then r <- -1
        elif a.[i] > b.[i] then r <- 1
        i <- i + 1
    r

let private partialDeg (a: int[]) (k: int) =
    let mutable s = 0
    for i in 1 .. k do s <- s + a.[i]
    s

// сравнение мономов → -1 / 0 / 1
let compare (ord: Order) (a: int[]) (b: int[]) : int =
    match ord with
    | Lex -> cmpLex a b 1
    | GrLex -> cmpLex a b 0
    | GrevLex ->
        if a.[0] < b.[0] then -1
        elif a.[0] > b.[0] then 1
        else revlex a b 1 a.Length
    | Block k ->
        let da = partialDeg a k
        let db = partialDeg b k
        if da < db then -1
        elif da > db then 1
        else
            let r = revlex a b 1 (k + 1)
            if r <> 0 then r
            else
                let ra = a.[0] - da
                let rb = b.[0] - db
                if ra < rb then -1 elif ra > rb then 1 else revlex a b (k + 1) a.Length

let private mmul (a: int[]) (b: int[]) : int[] = Array.init a.Length (fun i -> a.[i] + b.[i])
let private mdiv (a: int[]) (b: int[]) : int[] = Array.init a.Length (fun i -> a.[i] - b.[i])

// a делит b (покомпонентно ≤, полная степень — первой)
let private mdivides (a: int[]) (b: int[]) : bool =
    let mutable ok = true
    let mutable i = 0
    while ok && i < a.Length do
        if a.[i] > b.[i] then ok <- false
        i <- i + 1
    ok

let private mlcm (a: int[]) (b: int[]) : int[] =
    let r = Array.zeroCreate a.Length
    let mutable d = 0
    for i in 1 .. a.Length - 1 do
        let m = max a.[i] b.[i]
        r.[i] <- m
        d <- d + m
    r.[0] <- d
    r

let private coprime (a: int[]) (b: int[]) : bool =
    let mutable ok = true
    let mutable i = 1
    while ok && i < a.Length do
        if a.[i] > 0 && b.[i] > 0 then ok <- false
        i <- i + 1
    ok

let private meq (a: int[]) (b: int[]) : bool =
    let mutable ok = true
    let mutable i = 0
    while ok && i < a.Length do
        if a.[i] <> b.[i] then ok <- false
        i <- i + 1
    ok

let private qOne : Q = (1I, 1I)
let private qIsOne ((n, d): Q) = n.IsOne && d.IsOne

// ---------- счётчики ----------

// topsteps/tailsteps — шаги редукции, сделанные до первого терма, ушедшего в остаток (верх), и после него (хвост);
// ratops/coefbits/maxbits — арифметика коэффициентов, только при groebner-diag = stats | trace (в Lisp — те же места):
// ratops — число ratAdd (совпавшие мономы) + ratMul (mulTerm) + ratDiv (monic); coefbits — сумма длин (числитель + знаменатель,
// в битах) результатов сложений; maxbits — максимум длины результата любой из этих операций
let private counters = [| "calls"; "pairs"; "product"; "chain"; "bk"; "reductions"; "zero"; "added"; "basis"
                          "topsteps"; "tailsteps"; "ratops"; "coefbits"; "maxbits" |]
let stats = AlgoStats.register "groebner" counters
let private sPairs, sProduct, sChain, sBk, sReductions, sZero, sAdded = 1, 2, 3, 4, 5, 6, 7
let private sTop, sTail, sRatOps, sCoefBits, sMaxBits = 9, 10, 11, 12, 13

let private bump (i: int) (n: int) = if n > 0 then let v = stats.Values in v.[i] <- v.[i] + n

let inline private diagStats () = Algorithms.groebnerDiag.Index >= 1
let inline private diagTrace () = Algorithms.groebnerDiag.Index >= 2

// слить локальные накопления арифметики коэффициентов в счётчики (насыщение по int)
let private noteArith (ops: int) (bitsSum: int64) (mx: int64) =
    if ops > 0 then
        let v = stats.Values
        v.[sRatOps] <- v.[sRatOps] + ops
        v.[sCoefBits] <- int (min (int64 v.[sCoefBits] + bitsSum) (int64 Int32.MaxValue))
        if mx > int64 v.[sMaxBits] then v.[sMaxBits] <- int (min mx (int64 Int32.MaxValue))

// ---------- многочлены ----------

// p + q (слияние по убыванию)
let add (ord: Order) (p: Poly) (q: Poly) : Poly =
    let dg = diagStats ()
    let mutable ops = 0
    let mutable bitsSum = 0L
    let mutable mx = 0L
    let r = ResizeArray<Term>(p.Length + q.Length)
    let mutable i = 0
    let mutable j = 0
    while i < p.Length && j < q.Length do
        let c = compare ord p.[i].M q.[j].M
        if c > 0 then
            r.Add p.[i]; i <- i + 1
        elif c < 0 then
            r.Add q.[j]; j <- j + 1
        else
            let s = ratAdd p.[i].C q.[j].C
            if dg then
                let b = ratBits s
                ops <- ops + 1
                bitsSum <- bitsSum + b
                if b > mx then mx <- b
            if not (ratIsZero s) then r.Add { C = s; M = p.[i].M }
            i <- i + 1
            j <- j + 1
    while i < p.Length do
        r.Add p.[i]; i <- i + 1
    while j < q.Length do
        r.Add q.[j]; j <- j + 1
    noteArith ops bitsSum mx
    r.ToArray()

// c·m·q[from..] (порядок термов сохраняется: порядок мономиальный)
let private mulTerm (c: Q) (m: int[]) (q: Poly) (from: int) : Poly =
    let n = q.Length - from
    let res : Poly = Array.zeroCreate n
    if diagStats () then
        let mutable mx = 0L
        for k in 0 .. n - 1 do
            let t = q.[from + k]
            let x = ratMul c t.C
            let b = ratBits x
            if b > mx then mx <- b
            res.[k] <- { C = x; M = mmul m t.M }
        noteArith n 0L mx
    else
        for k in 0 .. n - 1 do
            let t = q.[from + k]
            res.[k] <- { C = ratMul c t.C; M = mmul m t.M }
    res

let monic (p: Poly) : Poly =
    if p.Length = 0 || qIsOne p.[0].C then p
    else
        let c = p.[0].C
        if diagStats () then
            let mutable mx = 0L
            let res =
                p |> Array.map (fun t ->
                    let x = ratDiv t.C c
                    { C = x; M = t.M })
            for t in res do
                let b = ratBits t.C
                if b > mx then mx <- b
            noteArith p.Length 0L mx
            res
        else
            p |> Array.map (fun t -> { C = ratDiv t.C c; M = t.M })

// Элемент базиса: номер, sugar, многочлен (монический)
type Elem = { Id: int; Sugar: int; P: Poly }

let inline private lm (e: Elem) = e.P.[0].M

// Полная редукция p по элементам gs (по порядку списка): (остаток, sugar); при вычитании t·g
// sugar = max(sugar, sugar(g) + deg t)
let reduce (ord: Order) (p0: Poly) (sug0: int) (gs: Elem list) : Poly * int =
    let rem = ResizeArray<Term>()
    let mutable p = p0
    let mutable sug = sug0
    let mutable top = 0
    let mutable tail = 0
    while p.Length > 0 do
        Cancel.check ()     // подшаг 22.4: прерывание (таймаут) — по проверке на шаг редукции
        let m = p.[0].M
        match gs |> List.tryFind (fun g -> mdivides (lm g) m) with
        | Some g ->
            if rem.Count = 0 then top <- top + 1 else tail <- tail + 1
            let t = mdiv m (lm g)
            p <- add ord (Array.sub p 1 (p.Length - 1)) (mulTerm (let (n, d) = p.[0].C in (-n, d)) t g.P 1)
            sug <- max sug (g.Sugar + t.[0])
        | None ->
            rem.Add p.[0]
            p <- Array.sub p 1 (p.Length - 1)
    bump sTop top
    bump sTail tail
    (rem.ToArray(), sug)

let nf (ord: Order) (p: Poly) (polys: Poly list) : Poly =
    fst (reduce ord p 0 (polys |> List.map (fun q -> { Id = 0; Sugar = 0; P = q })))

// S-многочлен монических f, g (старшие термы сокращаются)
let spoly (ord: Order) (f: Poly) (g: Poly) : Poly =
    let L = mlcm f.[0].M g.[0].M
    add ord (mulTerm qOne (mdiv L f.[0].M) f 1) (mulTerm (-1I, 1I) (mdiv L g.[0].M) g 1)

// ---------- Бухбергер ----------

// Пара: НОК старших мономов, sugar, элементы (A — новый h, B — g)
type Pair = { L: int[]; Sugar: int; A: Elem; B: Elem }

type private State(ord: Order, sugarStrategy: bool, maxReductions: int) =
    let mutable nextId = 0
    member _.Ord = ord
    member _.MaxReductions = maxReductions
    member _.Elem(p: Poly, sug: int) : Elem =
        nextId <- nextId + 1
        { Id = nextId; Sugar = sug; P = p }
    member _.Pair(a: Elem, b: Elem) : Pair =
        let L = mlcm (lm a) (lm b)
        { L = L; Sugar = max (a.Sugar + L.[0] - (lm a).[0]) (b.Sugar + L.[0] - (lm b).[0]); A = a; B = b }
    // p «лучше» q
    member _.Better(p: Pair, q: Pair) : bool =
        if sugarStrategy then p.Sugar < q.Sugar || (p.Sugar = q.Sugar && compare ord p.L q.L < 0)
        else compare ord p.L q.L < 0

// вставка по возрастанию старших мономов
let rec private insert (ord: Order) (e: Elem) (gs: Elem list) : Elem list =
    match gs with
    | [] -> [ e ]
    | g :: rest -> if compare ord (lm e) (lm g) < 0 then e :: gs else g :: insert ord e rest

// update(G, B, h) — BW с. 230; порядок обхода и результат — как в Lisp-версии
let private update (st: State) (gs: Elem list) (bs: Pair list) (h: Elem) : Elem list * Pair list =
    let ord = st.Ord
    let mh = lm h
    // новые пары: C — (lcm, g) по порядку G; принятые D — в обратном порядке принятия (как cons в Lisp)
    let rec newPairs (C: (int[] * Elem) list) (D: Pair list) =
        match C with
        | [] -> D
        | (L, g) :: rest ->
            if coprime mh (lm g)
               || (not (rest |> List.exists (fun (l, _) -> mdivides l L))
                   && not (D |> List.exists (fun pr -> mdivides pr.L L))) then
                newPairs rest (st.Pair(h, g) :: D)
            else newPairs rest D
    let D = newPairs (gs |> List.map (fun g -> (mlcm mh (lm g), g))) []
    let E = D |> List.filter (fun pr -> not (coprime mh (lm pr.B)))
    let B2 =
        bs |> List.filter (fun pr ->
            not (mdivides mh pr.L) || meq (mlcm (lm pr.A) mh) pr.L || meq (mlcm (lm pr.B) mh) pr.L)
    let G2 = insert ord h (gs |> List.filter (fun g -> not (mdivides mh (lm g))))
    bump sProduct (D.Length - E.Length)
    bump sChain (gs.Length - D.Length)
    bump sBk (bs.Length - B2.Length)
    bump sPairs E.Length
    (G2, B2 @ E)

// выбор пары: лучшая (первая из равных — как foldl в Lisp) и остальные
let private select (st: State) (ps: Pair list) : Pair * Pair list =
    let best = ps.Tail |> List.fold (fun b p -> if st.Better(p, b) then p else b) ps.Head
    let rec remove l =
        match l with
        | [] -> []
        | p :: rest -> if p.A.Id = best.A.Id && p.B.Id = best.B.Id then rest else p :: remove rest
    (best, remove ps)

let private isConstant (p: Poly) = p.[0].M.[0] = 0

let private tdeg (p: Poly) = p |> Array.fold (fun m t -> max m t.M.[0]) 0

let private interreduce (ord: Order) (fs: Poly list) : Poly list =
    let pass (fs: Poly list) =
        let rec go (fs: Poly list) (dn: Poly list) (acc: Poly list) =
            match fs with
            | [] -> List.rev acc
            | f :: rest ->
                let r = monic (nf ord f dn)
                go rest (f :: dn) (if r.Length = 0 then acc else r :: acc)
        go fs [] []
    let polyEq (a: Poly) (b: Poly) =
        a.Length = b.Length && Array.forall2 (fun (x: Term) (y: Term) -> x.C = y.C && meq x.M y.M) a b
    let rec fix fs =
        let f1 = pass fs
        if List.length f1 = List.length fs && List.forall2 polyEq f1 fs then fs else fix f1
    fix fs

let private buchberger (st: State) (fs: Poly list) : Elem list =
    let ord = st.Ord
    let f0 = interreduce ord (fs |> List.map monic)
    match f0 |> List.tryFind isConstant with
    | Some c -> [ st.Elem([| { C = qOne; M = c.[0].M } |], 0) ]
    | None ->
        let sorted = f0 |> List.sortWith (fun a b -> compare ord a.[0].M b.[0].M)   // устойчивая, как sort в Lisp
        let (g0, b0) = sorted |> List.fold (fun (g, b) p -> update st g b (st.Elem(p, tdeg p))) ([], [])
        let trace = diagTrace ()
        let clock = Diagnostics.Stopwatch.StartNew()
        let rec loop (G: Elem list) (B: Pair list) (n: int) =
            match B with
            | [] -> G
            | _ when n > st.MaxReductions ->
                failwithf "groebner: превышен предел числа редукций S-многочленов %d" st.MaxReductions
            | _ ->
                Cancel.check ()
                let (pr, B1) = select st B
                let sp = spoly ord pr.A.P pr.B.P
                let (r, sug) = reduce ord sp pr.Sugar G
                // трасса: номер, |G|, |B| (до выбора пары), членов S-многочлена, членов остатка, maxbits, время (мкс)
                if trace then
                    eprintfn "groebner #%d |G|=%d |B|=%d S=%d rem=%d maxbits=%d t=%d мкс" (n + 1) G.Length B.Length sp.Length
                        r.Length stats.Values.[sMaxBits] (clock.ElapsedTicks * 1000000L / Diagnostics.Stopwatch.Frequency)
                let h = monic r
                bump sReductions 1
                if h.Length = 0 then
                    bump sZero 1
                    loop G B1 (n + 1)
                elif isConstant h then
                    bump sAdded 1
                    [ st.Elem(h, 0) ]
                else
                    bump sAdded 1
                    let (G2, B2) = update st G B1 (st.Elem(h, sug))
                    loop G2 B2 (n + 1)
        loop g0 b0 0

// приведённый базис: каждый элемент — по остальным, монический; по убыванию старших мономов
let private reducedBasis (ord: Order) (G: Elem list) : Poly list =
    G |> List.map (fun g -> monic (fst (reduce ord g.P 0 (G |> List.filter (fun x -> x.Id <> g.Id)))))
      |> List.filter (fun p -> p.Length > 0)
      |> List.sortWith (fun a b -> compare ord b.[0].M a.[0].M)

// Приведённый базис Грёбнера (нули во входе отбрасываются; пустой вход → пустой базис)
let basis (ord: Order) (sugarStrategy: bool) (maxReductions: int) (fs: Poly list) : Poly list =
    let nz = fs |> List.filter (fun p -> p.Length > 0)
    if nz.IsEmpty then []
    else reducedBasis ord (buchberger (State(ord, sugarStrategy, maxReductions)) nz)

// Критерий Бухбергера: все S-многочлены образующих редуцируются к нулю (для тестов)
let isGroebner (ord: Order) (ps: Poly list) : bool =
    let ms = ps |> List.map monic |> Array.ofList
    seq { for i in 0 .. ms.Length - 1 do
            for j in i + 1 .. ms.Length - 1 -> (i, j) }
    |> Seq.forall (fun (i, j) -> (nf ord (spoly ord ms.[i] ms.[j]) (List.ofArray ms)).Length = 0)
