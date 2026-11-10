// Разреженный модулярный НОД Зиппеля: LINZIP (шаг 21g); вынесено из MPoly.fs в шаге 21h'.
// Здесь же точки входа для тестов и замеров (tryZippelGcd, zippelPrimeGcd, zippelImage, ...) и правило выбора
// Браун / Зиппель (zippelWanted); драйвер НОД — PolyGcd.modularPrimitiveGcd.
module Zippel

open System.Numerics
open MPoly
open ModArith

// --- разреженный модулярный НОД Зиппеля: LINZIP (de Kleine–Monagan–Wittkopf, ISSAC 2005; шаг 21g) ---
//
// Нумерация шагов в комментариях — как в статье: Algorithm 1 (LINZIP M, по простым, над Z) и Algorithm 2
// (LINZIP P, по точкам последней переменной x_n, над Z_p). Переменные: x1 = x (главная), x2..xn = ys в порядке
// убывания номера; лексикографический порядок — по (x1, x2, ..., xn). Многочлены на этом пути — ПЛОСКИЕ
// (массивы термов), а не рекурсивные ZP: вычисление в точке — один проход по термам.
//
// Отличия от статьи (осознанные):
//  * точки одного набора образов — геометрическая прогрессия α_j = β^j (а не независимые случайные), как у
//    Javadi–Monagan / Kaltofen–Lakshman: каждый блок (коэффициент при x1^e) — транспонированная система
//    Вандермонда, решаемая за O(n^2) (Zippel 1990); в статье — общая линейная система (O(n^3) на блок).
//    Для multiple scaling масштабы m_j находятся из линейных рекуррентностей блоков (характеристический
//    многочлен — мастер-многочлен блока), та же система, что в Example 3 / Figure 1, но без неизвестных-коэффициентов;
//  * при «плохом» образе (степень НОД упала, не хватает степени a) набор образов начинается заново с новой β;
//    «число неудач > min(k, ni)» считается по максимальному числу накопленных образов (k = 2 в M, 1 в P).
// Результат LINZIP M ВСЕГДА проверяется точным делением (шаг 7), поэтому вероятностные допущения не влияют на корректность.

// Плоский многочлен над Z_p: NV переменных (индекс 0 — x1), термы по убыванию лексикографического порядка,
// Ex — по NV экспонент на терм
type private Flat = { NV: int; Ex: int[]; Cf: int64[] }

// Счётчики Зиппеля (по потокам, для тестов и замеров; реестр AlgoStats, группа «gcd.zippel»)
let private zGroup =
    AlgoStats.register "gcd.zippel"
        [| "calls"; "ok"; "fallback-brown"; "content-xn"; "degree-drop"; "bad-form"; "bad-point"; "underdetermined"
           "prob-division-failed"; "division-failed"; "single-scaling"; "multi-scaling"; "univariate-gcds"; "p-fail"; "micros" |]
// [0] вызовов LINZIP M; [1] успехов (кандидат принят точным делением); [2] откатов на Брауна;
// [3] P, шаг 0: НОД имеет содержание по x_n (Fail); [4] падение степени (deg g1 < dx1, goto 2);
// [5] неверная форма (несовместность / нет масштабного терма / терм вне формы / нулевой старший);
// [6] невезучая точка или простое (deg g1 > dx1); [7] недоопределённая система (повтор степеней свободы);
// [8] P, шаг 7: вероятностный тест деления не прошёл; [9] M, шаг 7: точное деление кандидата не прошло;
// [10] построено форм single scaling; [11] построено форм multiple scaling;
// [12] унивариатных НОД (образов); [13] P: прочие Fail (рекурсия, исчерпание попыток);
// [14] суммарное время LINZIP M, мкс
let zippelStats () : int[] = zGroup.Values

[<Literal>]
let private ZCalls = 0
[<Literal>]
let private ZOk = 1
[<Literal>]
let private ZFallback = 2
[<Literal>]
let private ZContent = 3
[<Literal>]
let private ZDeg = 4
[<Literal>]
let private ZForm = 5
[<Literal>]
let private ZBad = 6
[<Literal>]
let private ZUnder = 7
[<Literal>]
let private ZDivP = 8
[<Literal>]
let private ZDivM = 9
[<Literal>]
let private ZSingle = 10
[<Literal>]
let private ZMulti = 11
[<Literal>]
let private ZImg = 12
[<Literal>]
let private ZPFail = 13
[<Literal>]
let private ZMicros = 14

// Проверочные образы сверх nx в разреженной интерполяции (см. sparseImage)
let private verifyImages = 1

// Режим выбора алгоритма (по потокам; для тестов и замеров): 0 — по эвристике, 1 — Зиппель всегда, 2 — только Браун.
// Шаг 21h': режим хранит общий переключатель Algorithms.gcd (auto | zippel | brown): (set-algorithm 'gcd 'zippel) в Lisp,
// Algorithms.gcd.Set в F#; начальное значение — переменная окружения LISP_GCD (A/B-замеры без пересборки). setZippelMode —
// прежний числовой вход для тестов
let setZippelMode (m: int) : unit =
    Algorithms.gcd.Set (match m with 1 -> "zippel" | 2 -> "brown" | _ -> "auto")

let inline private mm (p: int64) (a: int64) (b: int64) : int64 = a * b % p
let inline private addm (p: int64) (a: int64) (b: int64) : int64 = let s = a + b in if s >= p then s - p else s
let inline private subm (p: int64) (a: int64) (b: int64) : int64 = let s = a - b in if s < 0L then s + p else s

// Многочлен Горнера: значение a(x) (a — коэффициенты от младшего)
let private evalUni (p: int64) (a: int64[]) (x: int64) : int64 =
    let mutable acc = 0L
    for i in a.Length - 1 .. -1 .. 0 do acc <- addm p (mm p acc x) a.[i]
    acc

// Точное деление a / b над Z_p (b ненулевой, последний коэффициент b не ноль); частное — массив длины deg a - deg b + 1
let private polyDivExact (p: int64) (a: int64[]) (b: int64[]) : int64[] =
    let db = b.Length - 1
    let inv = invModL b.[db] p
    let r = Array.copy a
    let q = Array.zeroCreate<int64> (max 1 (a.Length - db))
    for k in a.Length - 1 .. -1 .. db do
        let c = r.[k]
        if c <> 0L then
            let f = mm p c inv
            q.[k - db] <- f
            for j in 0 .. db do r.[k - db + j] <- subm p r.[k - db + j] (mm p f b.[j])
    q

// Делит ли g многочлен a (оба над Z_p, g ненулевой)
let private uniDivides (p: int64) (g0: int64[]) (a0: int64[]) : bool =
    let trim (a: int64[]) =
        let mutable n = a.Length
        while n > 0 && a.[n - 1] = 0L do n <- n - 1
        if n = a.Length then a else Array.sub a 0 n
    let g, a = trim g0, trim a0
    if g.Length = 0 then false
    elif a.Length = 0 then true
    elif a.Length < g.Length then false
    else
        let db = g.Length - 1
        let inv = invModL g.[db] p
        let r = Array.copy a
        for k in a.Length - 1 .. -1 .. db do
            let c = r.[k]
            if c <> 0L then
                let f = mm p c inv
                for j in 0 .. db do r.[k - db + j] <- subm p r.[k - db + j] (mm p f g.[j])
        let mutable ok = true
        for i in 0 .. db - 1 do
            if r.[i] <> 0L then ok <- false
        ok

// Мастер-многочлен Π_{t<n} (z - v[lo+t]): коэффициенты от младшего, длина n+1
let private masterPoly (p: int64) (v: int64[]) (lo: int) (n: int) : int64[] =
    let m = Array.zeroCreate<int64> (n + 1)
    m.[0] <- 1L
    for t in 0 .. n - 1 do
        let r = v.[lo + t]
        for k in t + 1 .. -1 .. 1 do
            m.[k] <- subm p m.[k - 1] (mm p r m.[k])
        m.[0] <- mm p (subm p 0L r) m.[0]
    m

// Обращение набора ненулевых элементов одним возведением в степень (трюк Монтгомери)
let private batchInv (p: int64) (a: int64[]) : int64[] =
    let n = a.Length
    let pre = Array.zeroCreate<int64> n
    let mutable acc = 1L
    for i in 0 .. n - 1 do
        pre.[i] <- acc
        acc <- mm p acc a.[i]
    let mutable inv = invModL acc p
    let res = Array.zeroCreate<int64> n
    for i in n - 1 .. -1 .. 0 do
        res.[i] <- mm p inv pre.[i]
        inv <- mm p inv a.[i]
    res

// Транспонированная система Вандермонда: Σ_t c_t v_t^j = w_j, j = 1..n (v[lo..lo+n) — попарно различные ненулевые).
// Zippel 1990 / Kaltofen–Lakshman 1988 (§5, Lemma 2 и Invert: x_i = Q_n(v_i)/B'(v_i)); здесь — прямой вариант за O(n²):
// q_t = M/(z - v_t), c_t = (Σ_j w_j q_{t,j-1}) / (v_t q_t(v_t)). None — значения не различны (знаменатель 0).
let private vandSolve (p: int64) (v: int64[]) (lo: int) (n: int) (w: int64[]) : int64[] option =
    if n = 1 then Some [| mm p w.[0] (invModL v.[lo] p) |]
    else
        let mst = masterPoly p v lo n
        let num = Array.zeroCreate<int64> n
        let den = Array.zeroCreate<int64> n
        let q = Array.zeroCreate<int64> n
        let mutable bad = false
        for t in 0 .. n - 1 do
            let r = v.[lo + t]
            q.[n - 1] <- mst.[n]
            for k in n - 1 .. -1 .. 1 do q.[k - 1] <- addm p mst.[k] (mm p r q.[k])
            let mutable qr = 0L
            for k in n - 1 .. -1 .. 0 do qr <- addm p (mm p qr r) q.[k]
            let mutable s = 0L
            for k in 0 .. n - 1 do s <- (s + w.[k] * q.[k]) % p
            num.[t] <- s
            den.[t] <- mm p r qr
            if den.[t] = 0L then bad <- true
        if bad then None
        else
            let inv = batchInv p den
            Some (Array.init n (fun t -> mm p num.[t] inv.[t]))

type private GRes =
    | GInconsistent
    | GUnder of int
    | GSolved of int64[]

// Решение линейной системы над Z_p методом Гаусса–Жордана. Строка: ncols коэффициентов и правая часть (индекс ncols).
let private gaussSolve (p: int64) (rows: int64[][]) (ncols: int) : GRes =
    let nr = rows.Length
    let pivCol = ResizeArray<int>()
    let mutable r = 0
    for c in 0 .. ncols - 1 do
        if r < nr then
            let mutable piv = -1
            let mutable i = r
            while piv < 0 && i < nr do
                if rows.[i].[c] <> 0L then piv <- i
                i <- i + 1
            if piv >= 0 then
                let tmp = rows.[r]
                rows.[r] <- rows.[piv]
                rows.[piv] <- tmp
                let inv = invModL rows.[r].[c] p
                for j in c .. ncols do rows.[r].[j] <- mm p rows.[r].[j] inv
                for i2 in 0 .. nr - 1 do
                    if i2 <> r && rows.[i2].[c] <> 0L then
                        let f = rows.[i2].[c]
                        for j in c .. ncols do rows.[i2].[j] <- subm p rows.[i2].[j] (mm p f rows.[r].[j])
                pivCol.Add c
                r <- r + 1
    let mutable inconsistent = false
    for i in r .. nr - 1 do
        if rows.[i].[ncols] <> 0L then inconsistent <- true
    if inconsistent then GInconsistent
    elif r < ncols then GUnder (ncols - r)
    else
        let x = Array.zeroCreate<int64> ncols
        for i in 0 .. r - 1 do x.[pivCol.[i]] <- rows.[i].[ncols]
        GSolved x

// Имеют ли термы i и j одинаковые первые m экспонент
let private prefixEq (f: Flat) (m: int) (i: int) (j: int) : bool =
    let nv = f.NV
    let mutable ok = true
    let mutable c = 0
    while ok && c < m do
        if f.Ex.[i * nv + c] <> f.Ex.[j * nv + c] then ok <- false
        c <- c + 1
    ok

let private oneFlat (nv: int) : Flat = { NV = nv; Ex = Array.zeroCreate nv; Cf = [| 1L |] }

let private flatDeg1 (f: Flat) : int = if f.Cf.Length = 0 then 0 else f.Ex.[0]

// Одномерный (по x1) многочлен: массив коэффициентов / обратно
let private flatToUni (f: Flat) : int64[] =
    if f.Cf.Length = 0 then [||]
    else
        let a = Array.zeroCreate<int64> (f.Ex.[0] + 1)
        for t in 0 .. f.Cf.Length - 1 do a.[f.Ex.[t]] <- f.Cf.[t]
        a

let private uniToFlat (g: int64[]) : Flat =
    let ex = ResizeArray<int>()
    let cf = ResizeArray<int64>()
    for e in g.Length - 1 .. -1 .. 0 do
        if g.[e] <> 0L then
            ex.Add e
            cf.Add g.[e]
    { NV = 1; Ex = ex.ToArray(); Cf = cf.ToArray() }

// Подстановка x_n := v (последняя переменная): результат — многочлен от x1..x_{n-1}
let private evalLast (p: int64) (f: Flat) (v: int64) : Flat =
    let nv = f.NV
    let m = nv - 1
    let n = f.Cf.Length
    let mutable maxe = 0
    for t in 0 .. n - 1 do
        if f.Ex.[t * nv + m] > maxe then maxe <- f.Ex.[t * nv + m]
    let pw = Array.zeroCreate<int64> (maxe + 1)
    pw.[0] <- 1L
    for e in 1 .. maxe do pw.[e] <- mm p pw.[e - 1] v
    let ex = ResizeArray<int>(n * m)
    let cf = ResizeArray<int64>(n)
    let mutable i = 0
    while i < n do
        let mutable j = i + 1
        while j < n && prefixEq f m i j do j <- j + 1
        let mutable acc = 0L
        for t in i .. j - 1 do
            acc <- (acc + f.Cf.[t] * pw.[f.Ex.[t * nv + m]]) % p
        if acc <> 0L then
            for c in 0 .. m - 1 do ex.Add f.Ex.[i * nv + c]
            cf.Add acc
        i <- j
    { NV = m; Ex = ex.ToArray(); Cf = cf.ToArray() }

// Подстановка всех переменных, кроме keep (alphas.[i] — значение переменной i): многочлен от keep, массив длины deg+1
let private evalToVar (p: int64) (f: Flat) (keep: int) (alphas: int64[]) : int64[] =
    let nv = f.NV
    let n = f.Cf.Length
    let maxe = Array.zeroCreate<int> nv
    for t in 0 .. n - 1 do
        for i in 0 .. nv - 1 do
            let e = f.Ex.[t * nv + i]
            if e > maxe.[i] then maxe.[i] <- e
    let tabs =
        Array.init nv (fun i ->
            if i = keep then null
            else
                let tb = Array.zeroCreate<int64> (maxe.[i] + 1)
                tb.[0] <- 1L
                for e in 1 .. maxe.[i] do tb.[e] <- mm p tb.[e - 1] alphas.[i]
                tb)
    let out = Array.zeroCreate<int64> (maxe.[keep] + 1)
    for t in 0 .. n - 1 do
        let mutable r = f.Cf.[t]
        for i in 0 .. nv - 1 do
            if i <> keep then r <- mm p r tabs.[i].[f.Ex.[t * nv + i]]
        let e = f.Ex.[t * nv + keep]
        out.[e] <- addm p out.[e] r
    out

// Последовательные образы в точках геометрической прогрессии α_j = β^j (β — для переменных x2..xn):
// для каждого терма хранится текущее значение c·m(β)^j, переход к следующему образу — одно умножение на m(β)
type private GeomEval(p: int64, f: Flat, beta: int64[]) =
    let n = f.Cf.Length
    let nv = f.NV
    let deg = if n = 0 then 0 else f.Ex.[0]
    let ratio = Array.zeroCreate<int64> n
    let run = Array.copy f.Cf
    do
        let maxe = Array.zeroCreate<int> nv
        for t in 0 .. n - 1 do
            for i in 1 .. nv - 1 do
                let e = f.Ex.[t * nv + i]
                if e > maxe.[i] then maxe.[i] <- e
        let tabs =
            Array.init nv (fun i ->
                if i = 0 then null
                else
                    let tb = Array.zeroCreate<int64> (maxe.[i] + 1)
                    tb.[0] <- 1L
                    for e in 1 .. maxe.[i] do tb.[e] <- tb.[e - 1] * beta.[i - 1] % p
                    tb)
        for t in 0 .. n - 1 do
            let mutable r = 1L
            for i in 1 .. nv - 1 do r <- r * tabs.[i].[f.Ex.[t * nv + i]] % p
            ratio.[t] <- r
    // образ в очередной точке: многочлен от x1 (длина deg+1)
    member _.Next () : int64[] =
        let out = Array.zeroCreate<int64> (deg + 1)
        for t in 0 .. n - 1 do
            let v = run.[t] * ratio.[t] % p
            run.[t] <- v
            let e = f.Ex.[t * nv]
            let s = out.[e] + v
            out.[e] <- if s >= p then s - p else s
        out

// Многочлены от x_n для каждого префикса (x1..x_{n-1}): (индекс первого терма, коэффициенты)
let private runsLast (f: Flat) : ResizeArray<int * int64[]> =
    let nv = f.NV
    let m = nv - 1
    let n = f.Cf.Length
    let res = ResizeArray<int * int64[]>()
    let mutable i = 0
    while i < n do
        let mutable j = i + 1
        while j < n && prefixEq f m i j do j <- j + 1
        let arr = Array.zeroCreate<int64> (f.Ex.[i * nv + m] + 1)
        for t in i .. j - 1 do arr.[f.Ex.[t * nv + m]] <- f.Cf.[t]
        res.Add ((i, arr))
        i <- j
    res

// Содержание по x_n: НОД (унитарный) многочленов от x_n при мономах x1..x_{n-1}
let private contentOfRuns (p: int64) (runs: ResizeArray<int * int64[]>) : int64[] =
    let mutable g : int64[] = [||]
    for (_, arr) in runs do
        if g.Length <> 1 then
            g <- if g.Length = 0 then arr else gcdArr p g arr
    if g.Length <= 1 then [| 1L |]
    else
        let inv = invModL g.[g.Length - 1] p
        g |> Array.map (fun c -> mm p c inv)

// Верхняя граница deg_{x_n} НОДа (Remark 1 статьи): подстановка случайных значений во все остальные переменные
let private lastDegBound (p: int64) (a: Flat) (b: Flat) (rng: Rng) : int =
    let nv = a.NV
    let keep = nv - 1
    let degOf (f: Flat) =
        let mutable d = 0
        for t in 0 .. f.Cf.Length - 1 do
            if f.Ex.[t * nv + keep] > d then d <- f.Ex.[t * nv + keep]
        d
    let da, db = degOf a, degOf b
    let mutable best = min da db
    let mutable good = 0
    let mutable tries = 0
    while good < 2 && best > 0 && tries < 8 do
        tries <- tries + 1
        let alphas = Array.init nv (fun _ -> rng.Range (1L, p - 1L))
        let ua = evalToVar p a keep alphas
        let ub = evalToVar p b keep alphas
        if ua.[da] <> 0L && ub.[db] <> 0L then
            good <- good + 1
            let g = gcdArr p ua ub
            if g.Length - 1 < best then best <- g.Length - 1
    best

// ---- форма (носитель) НОДа, масштабирование ----

// Термы формы (лекс. порядок) сгруппированы в блоки по степени x1; Scale — индекс блока из одного терма
// (single scaling) или -1 (multiple scaling); Nx — число образов (шаг 3.1 / 3.2; -1 — форма непригодна)
type private Form =
    { FNV: int
      FEx: int[]
      FNT: int
      BlkE: int[]
      BlkS: int[]
      Scale: int
      Nx: int }

let private formOfFlat (f: Flat) : Form =
    let nv = f.NV
    let nt = f.Cf.Length
    let bs = ResizeArray<int>()
    let be = ResizeArray<int>()
    for t in 0 .. nt - 1 do
        if t = 0 || f.Ex.[t * nv] <> f.Ex.[(t - 1) * nv] then
            bs.Add t
            be.Add f.Ex.[t * nv]
    bs.Add nt
    let nb = be.Count
    let sizes = Array.init nb (fun i -> bs.[i + 1] - bs.[i])
    let nmax = if nb = 0 then 0 else Array.max sizes
    let scale = match sizes |> Array.tryFindIndex (fun s -> s = 1) with Some i -> i | None -> -1
    let nx =
        if nb = 0 then -1
        elif scale >= 0 then nmax
        elif nb < 2 then -1                      // единственный блок из ≥ 2 термов: у НОДа есть содержание по x1
        else max nmax ((nt - 1 + nb - 2) / (nb - 1))   // Remark 2: max(nmax, ⌈(Σn_i − 1)/(s − 1)⌉)
    { FNV = nv; FEx = f.Ex; FNT = nt; BlkE = be.ToArray(); BlkS = bs.ToArray(); Scale = scale; Nx = nx }

type private SolveRes =
    | SolOk of int64[]
    | SolBad
    | SolUnder of int

// Шаги 5.4–5.6: решение системы по ni накопленным образам rows (rows.[j-1] — унитарный НОД j-й точки β^j как массив
// по степеням x1). vals — значения мономов формы в β. single scaling: коэффициент масштабного терма := 1, масштабы
// m_j = v_s^j / c_{j,s}; multiple scaling: m_1 = 1, остальные — из рекуррентностей блоков. Затем каждый блок —
// транспонированная система Вандермонда по первым n_e образам; остальные образы проверяют согласованность.
let private solveForm (p: int64) (form: Form) (vals: int64[]) (rows: ResizeArray<int64[]>) : SolveRes =
    let ni = rows.Count
    let nb = form.BlkE.Length
    let nt = form.FNT
    let m = Array.zeroCreate<int64> ni
    let mutable res : SolveRes option = None
    if form.Scale >= 0 then
        let b = form.Scale
        let e = form.BlkE.[b]
        let v = vals.[form.BlkS.[b]]
        let invs = batchInv p (Array.init ni (fun j -> rows.[j].[e]))
        let mutable vp = 1L
        for j in 0 .. ni - 1 do
            vp <- mm p vp v
            m.[j] <- mm p vp invs.[j]
    else
        let eqs = ResizeArray<int64[]>()
        for b in 0 .. nb - 1 do
            let nbk = form.BlkS.[b + 1] - form.BlkS.[b]
            if nbk < ni then
                let mu = masterPoly p vals form.BlkS.[b] nbk
                let e = form.BlkE.[b]
                for sh in 0 .. ni - nbk - 1 do
                    // Σ_k μ_k · c_{sh+k} · m_{sh+k} = 0 (рекуррентность последовательности u_j = m_j c_{j,e})
                    let row = Array.zeroCreate<int64> ni
                    for kk in 0 .. nbk do
                        let c = mm p mu.[kk] rows.[sh + kk].[e]
                        let img = sh + kk
                        if img = 0 then row.[ni - 1] <- subm p 0L c       // m_1 = 1 — в правую часть
                        else row.[img - 1] <- c
                    eqs.Add row
        match gaussSolve p (eqs.ToArray()) (ni - 1) with
        | GInconsistent -> res <- Some SolBad
        | GUnder d -> res <- Some (SolUnder d)
        | GSolved x ->
            m.[0] <- 1L
            for i in 0 .. ni - 2 do m.[i + 1] <- x.[i]
            if m |> Array.exists (fun c -> c = 0L) then res <- Some SolBad
    match res with
    | Some r -> r
    | None ->
        let coef = Array.zeroCreate<int64> nt
        let w = Array.zeroCreate<int64> ni
        let mutable ok = true
        let mutable b = 0
        while ok && b < nb do
            let lo = form.BlkS.[b]
            let nbk = form.BlkS.[b + 1] - lo
            let e = form.BlkE.[b]
            for j in 0 .. ni - 1 do w.[j] <- mm p m.[j] rows.[j].[e]
            match vandSolve p vals lo nbk w with
            | None -> ok <- false
            | Some c ->
                let pw = Array.init nbk (fun t -> powModL vals.[lo + t] (int64 nbk) p)
                for j in nbk .. ni - 1 do
                    let mutable s = 0L
                    for t in 0 .. nbk - 1 do
                        pw.[t] <- mm p pw.[t] vals.[lo + t]
                        s <- (s + c.[t] * pw.[t]) % p
                    if s <> w.[j] then ok <- false
                Array.blit c 0 coef lo nbk
            b <- b + 1
        if ok then SolOk coef else SolBad

type private SOut =
    | SOk of int64[]       // коэффициенты по термам формы (с нулями)
    | SDegDrop of int      // deg g1 < dx1: новая степень (goto 2)
    | SForm                // форма неверна (goto 2)
    | SBad                 // невезучая точка / простое (goto 5.1)

// Шаги 5.2–5.6 LINZIP P / M: разреженный образ для заданной формы. a, b — многочлены от x1 и k = NV-1 остальных
// переменных (уже подставлены x_n = v в P либо сам Z_p-образ в M). failLimit — k из «число неудач > min(k, ni)».
// extra — число проверочных образов сверх nx (у нас 1: без него в блоке максимального размера нет ни одного лишнего
// уравнения, и пропавший терм формы не обнаруживается на шаге 5.5; в статье nx образов ровно).
let private sparseImageCore (p: int64) (a: Flat) (b: Flat) (form: Form) (dx1: int) (failLimit: int) (extra: int)
                            (rng: Rng) (st: int[]) : SOut =
    let nv = form.FNV
    let k = nv - 1
    let nt = form.FNT
    let nb = form.BlkE.Length
    if form.BlkE.[0] > dx1 then SForm
    else
    let blockOfDeg = Array.create (dx1 + 1) -1
    for i in 0 .. nb - 1 do blockOfDeg.[form.BlkE.[i]] <- i
    let single = form.Scale >= 0
    let scaleDeg = if single then form.BlkE.[form.Scale] else -1
    let da, db = flatDeg1 a, flatDeg1 b
    let outsideForm (g1: int64[]) =
        let mutable bad = false
        for e in 0 .. dx1 do
            if blockOfDeg.[e] < 0 && g1.[e] <> 0L then bad <- true
        bad
    if k = 0 then
        // одна переменная x1: единственный образ — сам НОД
        let g = gcdArr p (flatToUni a) (flatToUni b)
        st.[ZImg] <- st.[ZImg] + 1
        let d = g.Length - 1
        if d < dx1 then SDegDrop d
        elif d > dx1 then
            st.[ZBad] <- st.[ZBad] + 1
            SBad
        elif outsideForm g then SForm
        else SOk (Array.init nt (fun t -> g.[form.BlkE.[t]]))
    else
    let mutable outcome : SOut option = None
    let mutable failures = 0
    let mutable nimax = 0
    let mutable attempts = 0
    let seenDof = System.Collections.Generic.Dictionary<int, int>()
    while outcome.IsNone do
        attempts <- attempts + 1
        if attempts > 25 then outcome <- Some SBad
        else
            let beta = Array.init k (fun _ -> rng.Range (1L, p - 1L))
            // значения мономов формы в β
            let maxe = Array.zeroCreate<int> nv
            for t in 0 .. nt - 1 do
                for i in 1 .. k do
                    let e = form.FEx.[t * nv + i]
                    if e > maxe.[i] then maxe.[i] <- e
            let tabs =
                Array.init nv (fun i ->
                    if i = 0 then null
                    else
                        let tb = Array.zeroCreate<int64> (maxe.[i] + 1)
                        tb.[0] <- 1L
                        for e in 1 .. maxe.[i] do tb.[e] <- mm p tb.[e - 1] beta.[i - 1]
                        tb)
            let vals =
                Array.init nt (fun t ->
                    let mutable r = 1L
                    for i in 1 .. k do r <- mm p r tabs.[i].[form.FEx.[t * nv + i]]
                    r)
            // значения мономов внутри блока должны быть различны (иначе Вандермонд вырожден) — новая β
            let mutable distinct = true
            for bi in 0 .. nb - 1 do
                let lo, hi = form.BlkS.[bi], form.BlkS.[bi + 1]
                if hi - lo > 1 then
                    let s = Array.sub vals lo (hi - lo)
                    Array.sortInPlace s
                    for i in 1 .. s.Length - 1 do
                        if s.[i] = s.[i - 1] then distinct <- false
            if distinct then
                let ea = GeomEval (p, a, beta)
                let eb = GeomEval (p, b, beta)
                let rows = ResizeArray<int64[]>()
                let mutable target = form.Nx + extra
                let mutable restart = false
                while outcome.IsNone && not restart do
                    let ga = ea.Next ()
                    let gb = eb.Next ()
                    if ga.[da] = 0L || gb.[db] = 0L then restart <- true      // 5.3.1: степень a или b упала
                    else
                        let g1 = gcdArr p ga gb
                        st.[ZImg] <- st.[ZImg] + 1
                        let d1 = g1.Length - 1
                        if d1 < dx1 then outcome <- Some (SDegDrop d1)          // 5.3.3
                        elif d1 > dx1 then                                       // 5.3.4
                            failures <- failures + 1
                            if rows.Count > nimax then nimax <- rows.Count
                            if failures > min failLimit nimax then
                                st.[ZBad] <- st.[ZBad] + 1
                                outcome <- Some SBad
                            else restart <- true
                        elif outsideForm g1 || (single && g1.[scaleDeg] = 0L) then outcome <- Some SForm   // 5.3.5
                        else
                            rows.Add g1                                          // 5.3.6
                            if rows.Count >= target then
                                match solveForm p form vals rows with
                                | SolOk c -> outcome <- Some (SOk c)
                                | SolBad -> outcome <- Some SForm                // 5.5: несовместна
                                | SolUnder dof ->                                // 5.6: недоопределена
                                    let seen = match seenDof.TryGetValue dof with | true, c -> c | _ -> 0
                                    if seen >= 2 then
                                        st.[ZUnder] <- st.[ZUnder] + 1
                                        outcome <- Some SBad
                                    else
                                        seenDof.[dof] <- seen + 1
                                        target <- target + 1
    outcome.Value

// То же со счётчиками исходов «падение степени» и «неверная форма» ([4], [5])
let private sparseImage (p: int64) (a: Flat) (b: Flat) (form: Form) (dx1: int) (failLimit: int) (extra: int)
                        (rng: Rng) (st: int[]) : SOut =
    let r = sparseImageCore p a b form dx1 failLimit extra rng st
    match r with
    | SDegDrop _ -> st.[ZDeg] <- st.[ZDeg] + 1
    | SForm -> st.[ZForm] <- st.[ZForm] + 1
    | _ -> ()
    r

// Интерполяция Лагранжа по x_n (шаг 6): imgs.[i] — образ в точке vs.[i] (коэффициенты по термам формы).
// Результат — плоский многочлен от x1..x_n, термы в лекс. порядке.
let private interpolateLast (p: int64) (form: Form) (imgs: ResizeArray<int64[]>) (vs: int64[]) : Flat =
    let n = imgs.Count
    let mst = masterPoly p vs 0 n
    let basis =
        Array.init n (fun i ->
            let r = vs.[i]
            let q = Array.zeroCreate<int64> n
            q.[n - 1] <- mst.[n]
            for k in n - 1 .. -1 .. 1 do q.[k - 1] <- addm p mst.[k] (mm p r q.[k])
            let mutable qr = 0L
            for k in n - 1 .. -1 .. 0 do qr <- addm p (mm p qr r) q.[k]
            let inv = invModL qr p
            Array.map (fun c -> mm p c inv) q)
    let nv = form.FNV
    let ex = ResizeArray<int>()
    let cf = ResizeArray<int64>()
    for t in 0 .. form.FNT - 1 do
        for k in n - 1 .. -1 .. 0 do
            let mutable s = 0L
            for i in 0 .. n - 1 do s <- (s + imgs.[i].[t] * basis.[i].[k]) % p
            if s <> 0L then
                for c in 0 .. nv - 1 do ex.Add form.FEx.[t * nv + c]
                ex.Add k
                cf.Add s
    { NV = nv + 1; Ex = ex.ToArray(); Cf = cf.ToArray() }

// Шаг 6 (конец): снять содержание по x_n
let private removeContentLast (p: int64) (f: Flat) : Flat =
    let runs = runsLast f
    let c = contentOfRuns p runs
    if c.Length <= 1 then f
    else
        let nv = f.NV
        let ex = ResizeArray<int>()
        let cf = ResizeArray<int64>()
        for (i, arr) in runs do
            let q = polyDivExact p arr c
            for k in q.Length - 1 .. -1 .. 0 do
                if q.[k] <> 0L then
                    for cc in 0 .. nv - 2 do ex.Add f.Ex.[i * nv + cc]
                    ex.Add k
                    cf.Add q.[k]
        { NV = nv; Ex = ex.ToArray(); Cf = cf.ToArray() }

// Шаг 7 LINZIP P: вероятностный тест деления в случайной точке (x2..xn) ∈ (Z_p \ {0})^{n-1}
let private divisionTest (p: int64) (gc: Flat) (a: Flat) (b: Flat) (rng: Rng) : bool =
    let nv = gc.NV
    let dg = flatDeg1 gc
    let mutable verdict : bool option = None
    let mutable tries = 0
    while verdict.IsNone && tries < 6 do
        tries <- tries + 1
        let alphas = Array.init nv (fun _ -> rng.Range (1L, p - 1L))
        let g1 = evalToVar p gc 0 alphas
        if g1.[dg] <> 0L then
            let a1 = evalToVar p a 0 alphas
            let b1 = evalToVar p b 0 alphas
            verdict <- Some (uniDivides p g1 a1 && uniDivides p g1 b1)
    defaultArg verdict false

// Algorithm 2 (LINZIP P): НОД a, b ∈ Z_p[x1..xn] (NV = n ≥ 2). Результат — НОД с точностью до ненулевой константы,
// без содержания по x_n; None — Fail. dx1In — граница deg_x1 НОДа.
let rec private zipP (p: int64) (a: Flat) (b: Flat) (dx1In: int) (rng: Rng) (st: int[]) : Flat option =
    let nv = a.NV
    // шаг 0: у НОДа есть содержание по x_n ⇔ НОД содержаний (многочленов от x_n) нетривиален
    let runsA = runsLast a
    let runsB = runsLast b
    let ca = contentOfRuns p runsA
    let cb = contentOfRuns p runsB
    if (gcdArr p ca cb).Length > 1 then
        st.[ZContent] <- st.[ZContent] + 1
        None
    else
    // шаг 1: γ(x_n) = НОД старших (по x1..x_{n-1}) коэффициентов — многочленов от x_n
    let gamma = gcdArr p (snd runsA.[0]) (snd runsB.[0])
    let degG = gamma.Length - 1
    let nimg = lastDegBound p a b rng + degG + 1
    let used = System.Collections.Generic.HashSet<int64>()
    // случайная точка v ≠ 0 с γ(v) ≠ 0, ещё не использованная в этой попытке; -1 — точек не нашлось (малое p)
    let pickV () : int64 =
        let mutable v = -1L
        let mutable n = 0
        while v < 0L && n < 2000 do
            n <- n + 1
            let c = rng.Range (1L, p - 1L)
            if not (used.Contains c) && evalUni p gamma c <> 0L then v <- c
        if v >= 0L then used.Add v |> ignore
        v
    let mutable dx1 = dx1In
    let mutable result : Flat option = None
    let mutable failed = false
    let mutable tries = 0
    let mutable badCount = 0
    while result.IsNone && not failed do
        tries <- tries + 1
        if tries > 8 then
            st.[ZPFail] <- st.[ZPFail] + 1
            failed <- true
        else
            // шаг 2
            used.Clear ()
            let v0 = pickV ()
            let av = if v0 < 0L then a else evalLast p a v0
            let bv = if v0 < 0L then b else evalLast p b v0
            let gv0 : Flat option =
                if v0 < 0L then None
                elif nv = 2 then
                    let g = gcdArr p (flatToUni av) (flatToUni bv)
                    st.[ZImg] <- st.[ZImg] + 1
                    if g.Length - 1 > dx1 then
                        st.[ZBad] <- st.[ZBad] + 1
                        None
                    else Some (uniToFlat g)
                else zipP p av bv dx1 rng st
            match gv0 with
            | None -> failed <- true
            | Some gv ->
                dx1 <- flatDeg1 gv
                if dx1 = 0 then result <- Some (oneFlat nv)        // НОД = 1
                else
                    // шаг 3: форма и число образов
                    let form = formOfFlat gv
                    if form.Nx < 0 then
                        st.[ZForm] <- st.[ZForm] + 1
                        failed <- true
                    else
                        if form.Scale >= 0 then st.[ZSingle] <- st.[ZSingle] + 1 else st.[ZMulti] <- st.[ZMulti] + 1
                        // шаг 4
                        let imgs = ResizeArray<int64[]>()
                        let vseq = ResizeArray<int64>()
                        let sc0 = mm p (evalUni p gamma v0) (invModL gv.Cf.[0] p)
                        imgs.Add (Array.map (fun c -> mm p c sc0) gv.Cf)
                        vseq.Add v0
                        // шаг 5
                        let mutable restart = false
                        while not restart && not failed && imgs.Count < nimg do
                            let v = pickV ()
                            if v < 0L then
                                st.[ZPFail] <- st.[ZPFail] + 1
                                failed <- true
                            else
                            let av = evalLast p a v
                            let bv = evalLast p b v
                            match sparseImage p av bv form dx1 1 verifyImages rng st with
                            | SOk c ->
                                if c.[0] = 0L then
                                    st.[ZForm] <- st.[ZForm] + 1
                                    restart <- true
                                else
                                    let sc = mm p (evalUni p gamma v) (invModL c.[0] p)
                                    imgs.Add (Array.map (fun x -> mm p x sc) c)
                                    vseq.Add v
                            | SDegDrop d ->
                                dx1 <- d
                                restart <- true
                            | SForm -> restart <- true
                            | SBad ->
                                badCount <- badCount + 1
                                if badCount > 6 then
                                    st.[ZPFail] <- st.[ZPFail] + 1
                                    failed <- true
                        if not restart && not failed then
                            // шаги 6–7
                            let gstar = interpolateLast p form imgs (vseq.ToArray ())
                            let gc = removeContentLast p gstar
                            if divisionTest p gc a b rng then result <- Some gc
                            else st.[ZDivP] <- st.[ZDivP] + 1
    result

// Полиномиальная запись термов (лекс. порядок, переменные vs) как MPoly
let private polyOfTerms (vs: int[]) (ex: int[]) (cf: BigInteger[]) : MPoly =
    let nv = vs.Length
    let idx = [| for t in 0 .. cf.Length - 1 do if not cf.[t].IsZero then yield t |]
    let rec build (lvl: int) (lo: int) (hi: int) : MPoly =
        if lvl = nv then ofInt cf.[idx.[lo]]
        else
            let maxd = ex.[idx.[lo] * nv + lvl]
            let cs = Array.create (maxd + 1) zero
            let mutable i = lo
            while i < hi do
                let d = ex.[idx.[i] * nv + lvl]
                let mutable j = i + 1
                while j < hi && ex.[idx.[j] * nv + lvl] = d do j <- j + 1
                cs.[d] <- build (lvl + 1) i j
                i <- j
            mk vs.[lvl] cs
    if idx.Length = 0 then zero else build 0 0 idx.Length

// Термы многочлена с целыми коэффициентами (лекс. порядок по переменным vs)
let private flatZ (vs: int[]) (m: MPoly) : int[] * BigInteger[] =
    let nv = vs.Length
    let ex = ResizeArray<int>()
    let cf = ResizeArray<BigInteger>()
    let cur = Array.zeroCreate<int> nv
    let rec go (m: MPoly) =
        match m with
        | Const (n, _) ->
            if not n.IsZero then
                ex.AddRange cur
                cf.Add n
        | Poly (v, cs) ->
            let idx = System.Array.IndexOf (vs, v)
            for d in cs.Length - 1 .. -1 .. 0 do
                if not (isZero cs.[d]) then
                    cur.[idx] <- d
                    go cs.[d]
            cur.[idx] <- 0
    go m
    (ex.ToArray (), cf.ToArray ())

let private reduceFlat (p: int64) (nv: int) (ex: int[]) (cf: BigInteger[]) : Flat =
    let bp = BigInteger p
    let ox = ResizeArray<int>(ex.Length)
    let oc = ResizeArray<int64>(cf.Length)
    for t in 0 .. cf.Length - 1 do
        let r0 = BigInteger.Remainder (cf.[t], bp)
        let r = if r0.Sign < 0 then r0 + bp else r0
        if not r.IsZero then
            for c in 0 .. nv - 1 do ox.Add ex.[t * nv + c]
            oc.Add (int64 r)
    { NV = nv; Ex = ox.ToArray (); Cf = oc.ToArray () }

// Шаг 5.7 LINZIP M: КТО по массиву коэффициентов (симметричные вычеты); true — ни один коэффициент не изменился
let private crtStep (p: int64) (m: BigInteger) (gm: BigInteger[]) (img: int64[]) : bool =
    let bp = BigInteger p
    let minv = invModL (int64 (m % bp)) p
    let mp = m * bp
    let half = mp / 2I
    let mutable same = true
    for t in 0 .. gm.Length - 1 do
        let n = gm.[t]
        let gmod = int64 (((n % bp) + bp) % bp)
        let tt = (((img.[t] - gmod) % p + p) % p) * minv % p
        let v = n + m * BigInteger tt
        let v2 = if v > half then v - mp else v
        if v2 <> n then same <- false
        gm.[t] <- v2
    same

// Algorithm 1 (LINZIP M): pa, pb — целые, примитивные по x (содержания по x1 нет); bound — граница deg_x НОДа.
// None — отказ (исчерпаны простые / слишком много неудач): вызывающий откатывается на Брауна.
let linzipM (pa: MPoly) (pb: MPoly) (x: int) (ys: int list) (bound: int) (rng: Rng) : MPoly option =
    let st = zippelStats ()
    st.[ZCalls] <- st.[ZCalls] + 1
    let t0 = System.Diagnostics.Stopwatch.GetTimestamp ()
    let vs = Array.ofList (x :: ys)
    let nv = vs.Length
    let (exA, cfA) = flatZ vs pa
    let (exB, cfB) = flatZ vs pb
    let la, lb = cfA.[0], cfB.[0]
    // шаг 1: γ — НОД старших (лекс.) коэффициентов
    let gamma = BigInteger.GreatestCommonDivisor (la, lb)
    let mutable dx1 = min bound (min exA.[0] exB.[0])
    let primes = modPrimes.Force ()
    let mutable idx = 0
    let mutable form : Form option = None
    let mutable gm : BigInteger[] = [||]
    let mutable modulus = 1I
    let mutable result : MPoly option = None
    let mutable finished = false
    let mutable failures = 0
    while not finished && idx < primes.Length && failures < 40 do
        let p = primes.[idx]
        idx <- idx + 1
        let bp = BigInteger p
        if not (la % bp).IsZero && not (lb % bp).IsZero then
            let ap = reduceFlat p nv exA cfA
            let bq = reduceFlat p nv exB cfB
            let gp = int64 (gamma % bp)
            match form with
            | None ->
                // шаги 2–4
                match zipP p ap bq dx1 rng st with
                | None -> failures <- failures + 1
                | Some g ->
                    let d = flatDeg1 g
                    if d = 0 then
                        result <- Some one
                        finished <- true
                    else
                        let f = formOfFlat g
                        if f.Nx < 0 then
                            st.[ZForm] <- st.[ZForm] + 1
                            failures <- failures + 1
                        else
                            if f.Scale >= 0 then st.[ZSingle] <- st.[ZSingle] + 1 else st.[ZMulti] <- st.[ZMulti] + 1
                            dx1 <- d
                            form <- Some f
                            let sc = mm p gp (invModL g.Cf.[0] p)
                            gm <- g.Cf |> Array.map (fun c ->
                                let v = mm p c sc
                                BigInteger (if v > p / 2L then v - p else v))
                            modulus <- bp
            | Some f ->
                // шаги 5.1–5.7
                match sparseImage p ap bq f dx1 2 verifyImages rng st with
                | SOk c ->
                    if c.[0] = 0L then
                        st.[ZForm] <- st.[ZForm] + 1
                        form <- None
                    else
                        let sc = mm p gp (invModL c.[0] p)
                        let img = Array.map (fun v -> mm p v sc) c
                        let same = crtStep p modulus gm img
                        modulus <- modulus * bp
                        if same then
                            // шаг 7: целое содержание снимается, кандидат проверяется точным делением
                            let cand = unitNormal (polyOfTerms vs f.FEx gm)
                            if divExact pa cand |> Option.isSome && divExact pb cand |> Option.isSome then
                                result <- Some cand
                                finished <- true
                            else st.[ZDivM] <- st.[ZDivM] + 1
                | SDegDrop d ->
                    dx1 <- d
                    form <- None
                | SForm -> form <- None
                | SBad -> ()
    match result with
    | Some _ -> st.[ZOk] <- st.[ZOk] + 1
    | None -> st.[ZFallback] <- st.[ZFallback] + 1
    st.[ZMicros] <- st.[ZMicros] + int ((System.Diagnostics.Stopwatch.GetTimestamp () - t0) / (System.Diagnostics.Stopwatch.Frequency / 1000000L))
    result

// Выбор Браун / Зиппель. Стартовое правило (n >= 4 или n = 3 и terms(a)+terms(b) < 0.1·Π(d_i+1))
// заменено по замерам шага 21g (Release, in-process, плотные и разреженные семейства): при n >= 3 переменных
// (с x) Зиппель не хуже Брауна ни в одной точке семейства — плотные G до степени 9 (1.2–2.0 раза быстрее на 3 переменных,
// 2–8 раз на 4–6), разреженные G — в 2–11 раз; при n = 2 Зиппель проигрывает на мелких задачах (0.7 раза при степени НОД
// 1–2: накладные расходы плоских представлений) и выигрывает в 1.2–1.5 раза при степени >= 3.
// bound — верхняя граница степени НОД по x из пробы одной точкой. LISP_GCD = zippel | brown — принудительный режим.
let zippelWanted (ys: int list) (bound: int) : bool =
    match Algorithms.gcd.Index with
    | 1 -> not ys.IsEmpty
    | 2 -> false
    | _ ->
        let n = ys.Length + 1
        n >= 3 || (n = 2 && bound >= 3)

// --- точки входа Зиппеля для тестов и замеров ---

// Переменные в лекс. порядке LINZIP: x (главная) и остальные по убыванию номера
let private zipVars (x: int) (ms: MPoly list) : int[] =
    let s = ms |> List.fold (fun acc m -> varsOf m acc) Set.empty
    Array.ofList (x :: (s |> Set.remove x |> Set.toList |> List.rev))

// LINZIP M без пробы и без отката: pa, pb примитивны по общей главной переменной; None — отказ
let tryZippelGcd (pa0: MPoly) (pb0: MPoly) (seed: uint64) : MPoly option =
    let pa, pb = unitNormal pa0, unitNormal pb0
    let x = mainVar pa
    let ys = varsOf pb (varsOf pa Set.empty) |> Set.remove x |> Set.toList |> List.rev
    if ys.IsEmpty then None else linzipM pa pb x ys System.Int32.MaxValue (Rng seed)

// Algorithm 2 (LINZIP P) по простому p: НОД a, b по модулю p (коэффициенты — вычеты 0..p-1, с точностью до константы)
let zippelPrimeGcd (p: int64) (a: MPoly) (b: MPoly) (dx1: int) (seed: uint64) : MPoly option =
    let x = mainVar a
    let vs = zipVars x [ a; b ]
    let nv = vs.Length
    let (exA, cfA) = flatZ vs a
    let (exB, cfB) = flatZ vs b
    let fa, fb = reduceFlat p nv exA cfA, reduceFlat p nv exB cfB
    match zipP p fa fb dx1 (Rng seed) (zippelStats ()) with
    | Some g -> Some (polyOfTerms vs g.Ex (g.Cf |> Array.map BigInteger))
    | None -> None

// Шаги 5.2–5.6 (разреженный образ по форме = носитель formPoly по модулю p): (исход, образ mod p).
// Исход: "ok" | "degdrop:d" | "form" | "bad". Масштаб образа: single scaling — коэффициент масштабного терма 1;
// multiple scaling — первый масштабный множитель 1. nxOverride >= 0 — принудительное начальное число образов.
let zippelImage (p: int64) (a: MPoly) (b: MPoly) (formPoly: MPoly) (dx1: int) (nxOverride: int) (extra: int)
                (seed: uint64) : string * MPoly =
    let x = mainVar a
    let vs = zipVars x [ a; b; formPoly ]
    let nv = vs.Length
    let (exA, cfA) = flatZ vs a
    let (exB, cfB) = flatZ vs b
    let (exF, cfF) = flatZ vs formPoly
    let fa, fb = reduceFlat p nv exA cfA, reduceFlat p nv exB cfB
    let ff = reduceFlat p nv exF cfF
    let form0 = formOfFlat ff
    let form = if nxOverride >= 0 then { form0 with Nx = nxOverride } else form0
    match sparseImage p fa fb form dx1 2 extra (Rng seed) (zippelStats ()) with
    | SOk c -> ("ok", polyOfTerms vs form.FEx (c |> Array.map BigInteger))
    | SDegDrop d -> (sprintf "degdrop:%d" d, zero)
    | SForm -> ("form", zero)
    | SBad -> ("bad", zero)

// (число образов Nx, single scaling?) для формы — по шагам 3.1 / 3.2 (Nx = -1 — форма непригодна)
let zippelFormInfo (formPoly: MPoly) : int * bool =
    let x = mainVar formPoly
    let vs = zipVars x [ formPoly ]
    let (ex, cf) = flatZ vs formPoly
    let f = formOfFlat { NV = vs.Length; Ex = ex; Cf = cf |> Array.map (fun _ -> 1L) }
    (f.Nx, f.Scale >= 0)

// Транспонированная система Вандермонда Σ_t c_t v_t^j = w_j (j = 1..n) по модулю p — для тестов
let vandermondeSolve (p: int64) (v: int64[]) (w: int64[]) : int64[] option =
    vandSolve p v 0 v.Length w

