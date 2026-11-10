// Многочлены от нескольких переменных по модулю m (Шаг 21f) — основа p-адического подъёма Хензеля
//
// Представление — то же РЕКУРСИВНОЕ ПЛОТНОЕ, что и в MPoly: многочлен = константа | (номер главной
// переменной v, массив коэффициентов от младшей степени к старшей); коэффициенты — многочлены от
// переменных с МЕНЬШИМИ номерами. Инварианты (поддерживает `mk`): массив не заканчивается нулём и
// содержит минимум 2 элемента. Массивы после создания не изменяются.
// Коэффициенты — BigInteger в [0, M); модуль M = p^l обычно больше 2^63, P — простое.
// Целые MPoly переводятся в/из этого представления: `toMPoly` возвращает СИММЕТРИЧНЫЕ вычеты (-M/2, M/2].
//
// Что здесь есть (по частям шага 21f):
//   1. арифметика (add/sub/mul/mulConst), доступ к коэффициентам, подстановка нуля, замена старшего
//      коэффициента, усечение по степени, деление с остатком по x;
//   2. диофантовы уравнения mod p^l (одномерное — Безу mod p и p-адическая итерация; многомерное —
//      рекурсия по переменным; r > 2 множителей — multiterm);
//   3. многомерный подъём Хензеля всех r множителей одновременно (Geddes–Czapor–Labahn, алг. 6.1–6.4).
module ModPoly

open System.Numerics

type MPolyM =
    | MC of BigInteger
    | MP of int * MPolyM[]

type Mod = { M: BigInteger; P: BigInteger }

let zero = MC 0I
let one = MC 1I

let isZero (p: MPolyM) = match p with MC c -> c.IsZero | _ -> false
// Номер главной переменной; -1 для константы
let mainVar (p: MPolyM) : int = match p with MC _ -> -1 | MP (v, _) -> v

// Конструктор с нормализацией (отбрасывает старшие нули)
let mk (v: int) (cs: MPolyM[]) : MPolyM =
    let mutable n = cs.Length
    while n > 0 && isZero cs.[n - 1] do n <- n - 1
    if n = 0 then zero
    elif n = 1 then cs.[0]
    elif n = cs.Length then MP (v, cs)
    else MP (v, Array.sub cs 0 n)

// Вычет x в [0, M)
let private red (m: Mod) (x: BigInteger) : BigInteger =
    let r = BigInteger.Remainder (x, m.M)
    if r.Sign < 0 then r + m.M else r

// Обратный элемент a по модулю m (расширенный Евклид); исключение, если a и m не взаимно просты
let invMod (a: BigInteger) (m: BigInteger) : BigInteger =
    let mutable r0 = m
    let mutable r1 = ((BigInteger.Remainder (a, m)) + m) % m
    let mutable t0 = 0I
    let mutable t1 = 1I
    while not r1.IsZero do
        let q = BigInteger.Divide (r0, r1)
        let r2 = r0 - q * r1
        r0 <- r1
        r1 <- r2
        let t2 = t0 - q * t1
        t0 <- t1
        t1 <- t2
    if not r0.IsOne then failwith "ModPoly.invMod: элемент необратим"
    ((t0 % m) + m) % m

// --- перевод из MPoly и обратно ---

// Только целые MPoly (знаменатели констант равны 1); вычеты в [0, M)
let rec ofMPoly (m: Mod) (p: MPoly.MPoly) : MPolyM =
    match p with
    | MPoly.Const (n, d) ->
        if not d.IsOne then failwith "ModPoly.ofMPoly: нецелый коэффициент"
        MC (red m n)
    | MPoly.Poly (v, cs) -> mk v (Array.map (ofMPoly m) cs)

// Симметричные вычеты (-M/2, M/2]
let rec toMPoly (m: Mod) (p: MPolyM) : MPoly.MPoly =
    let half = m.M / 2I
    match p with
    | MC c -> MPoly.Const ((if c > half then c - m.M else c), 1I)
    | MP (v, cs) -> MPoly.mk v (Array.map (toMPoly m) cs)

// --- арифметика ---

let rec add (m: Mod) (a: MPolyM) (b: MPolyM) : MPolyM =
    match a, b with
    | MC x, MC y -> let s = x + y in MC (if s >= m.M then s - m.M else s)
    | MP (v, ca), MP (w, cb) when v = w ->
        let n = max ca.Length cb.Length
        mk v (Array.init n (fun i ->
            if i >= ca.Length then cb.[i]
            elif i >= cb.Length then ca.[i]
            else add m ca.[i] cb.[i]))
    | MP (v, ca), _ when v > mainVar b ->
        let cs = Array.copy ca
        cs.[0] <- add m cs.[0] b
        mk v cs
    | _, MP (w, cb) when w > mainVar a ->
        let cs = Array.copy cb
        cs.[0] <- add m a cs.[0]
        mk w cs
    | _ -> failwith "ModPoly.add: нарушен инвариант порядка переменных"

let rec neg (m: Mod) (p: MPolyM) : MPolyM =
    match p with
    | MC c -> MC (if c.IsZero then c else m.M - c)
    | MP (v, cs) -> MP (v, Array.map (neg m) cs)

let sub (m: Mod) (a: MPolyM) (b: MPolyM) : MPolyM = add m a (neg m b)

// Умножение на константу (любое целое, приводится по модулю)
let mulConst (m: Mod) (c: BigInteger) (p: MPolyM) : MPolyM =
    let c = red m c
    let rec go (p: MPolyM) : MPolyM =
        match p with
        | MC x -> MC (red m (x * c))
        | MP (v, cs) -> mk v (Array.map go cs)
    if c.IsZero then zero else go p

let private allConst (cs: MPolyM[]) = cs |> Array.forall (fun c -> match c with MC _ -> true | _ -> false)
let private cval (p: MPolyM) = match p with MC c -> c | _ -> 0I

let rec mul (m: Mod) (a: MPolyM) (b: MPolyM) : MPolyM =
    match a, b with
    | MC x, MC y -> MC (red m (x * y))
    | MP (v, ca), MP (w, cb) when v = w ->
        if allConst ca && allConst cb then
            // лист: свёртка целых с одной редукцией на коэффициент
            let r = Array.create (ca.Length + cb.Length - 1) 0I
            for i in 0 .. ca.Length - 1 do
                let x = cval ca.[i]
                if not x.IsZero then
                    for j in 0 .. cb.Length - 1 do
                        r.[i + j] <- r.[i + j] + x * cval cb.[j]
            mk v (r |> Array.map (fun c -> MC (red m c)))
        else
            let res = Array.create (ca.Length + cb.Length - 1) zero
            for i in 0 .. ca.Length - 1 do
                if not (isZero ca.[i]) then
                    for j in 0 .. cb.Length - 1 do
                        if not (isZero cb.[j]) then
                            res.[i + j] <- add m res.[i + j] (mul m ca.[i] cb.[j])
            mk v res
    | MP (v, ca), _ when v > mainVar b -> mk v (Array.map (fun c -> mul m c b) ca)
    | _, MP (w, cb) when w > mainVar a -> mk w (Array.map (fun c -> mul m a c) cb)
    | _ -> failwith "ModPoly.mul: нарушен инвариант порядка переменных"

// --- доступ к коэффициентам ---

// Степень по главной переменной (0 для ненулевой константы, -1 для нуля)
let degMain (p: MPolyM) : int =
    match p with
    | MC c -> if c.IsZero then -1 else 0
    | MP (_, cs) -> cs.Length - 1

// Старший коэффициент по главной переменной (сам многочлен, если константа)
let lcMain (p: MPolyM) : MPolyM =
    match p with
    | MC _ -> p
    | MP (_, cs) -> cs.[cs.Length - 1]

// Степень по переменной v (не обязательно главной)
let rec degIn (v: int) (p: MPolyM) : int =
    match p with
    | MC c -> if c.IsZero then -1 else 0
    | MP (w, cs) when w = v -> cs.Length - 1
    | MP (w, cs) when w > v -> cs |> Array.map (degIn v) |> Array.max
    | _ -> 0

// Коэффициент при v^k (многочлен от остальных переменных)
let rec coeffIn (v: int) (k: int) (p: MPolyM) : MPolyM =
    match p with
    | MC _ -> if k = 0 then p else zero
    | MP (w, cs) when w = v -> if k < cs.Length then cs.[k] else zero
    | MP (w, cs) when w > v -> mk w (Array.map (coeffIn v k) cs)
    | _ -> if k = 0 then p else zero

// Подстановка y := 0 (после сдвига точка — ноль): коэффициент при y^0
let rec subst0 (y: int) (p: MPolyM) : MPolyM =
    match p with
    | MC _ -> p
    | MP (w, cs) when w = y -> cs.[0]
    | MP (w, cs) when w > y -> mk w (Array.map (subst0 y) cs)
    | _ -> p

// Замена старшего по x коэффициента на lcNew (g — многочлен с главной переменной x; иначе g без изменений)
let replaceLc (x: int) (lcNew: MPolyM) (g: MPolyM) : MPolyM =
    match g with
    | MP (v, cs) when v = x ->
        let c2 = Array.copy cs
        c2.[c2.Length - 1] <- lcNew
        mk v c2
    | _ -> g

// Отбросить члены со степенью по y больше d
let rec truncDeg (y: int) (d: int) (p: MPolyM) : MPolyM =
    match p with
    | MC _ -> p
    | MP (w, cs) when w = y -> if cs.Length <= d + 1 then p else mk w (Array.sub cs 0 (d + 1))
    | MP (w, cs) when w > y -> mk w (Array.map (truncDeg y d) cs)
    | _ -> p

// y^t · p, где p не содержит y и переменных с номерами >= y
let shiftY (y: int) (t: int) (p: MPolyM) : MPolyM =
    if isZero p || t = 0 then p
    else
        let cs = Array.create (t + 1) zero
        cs.[t] <- p
        MP (y, cs)

// Деление с остатком по x: a = q·b + r, deg_x r < deg_x b. b — многочлен от x (или ненулевая константа)
// со старшим коэффициентом-КОНСТАНТОЙ, обратимой по модулю M; a — многочлен от x и переменных ниже x
let divModUni (m: Mod) (x: int) (a: MPolyM) (b: MPolyM) : MPolyM * MPolyM =
    match b with
    | MC c ->
        if c.IsZero then failwith "ModPoly.divModUni: деление на ноль"
        (mulConst m (invMod c m.M) a, zero)
    | MP (v, cb) when v = x ->
        let db = cb.Length - 1
        let lb =
            match cb.[db] with
            | MC c -> c
            | _ -> failwith "ModPoly.divModUni: старший коэффициент делителя не константа"
        let inv = invMod lb m.M
        match a with
        | MP (w, ca) when w = x && ca.Length >= cb.Length ->
            let da = ca.Length - 1
            let r = Array.copy ca
            let q = Array.create (da - db + 1) zero
            for k in da - db .. -1 .. 0 do
                let c = r.[k + db]
                if not (isZero c) then
                    let qk = mulConst m inv c
                    q.[k] <- qk
                    for j in 0 .. db do
                        r.[k + j] <- sub m r.[k + j] (mul m qk cb.[j])
            (mk x q, mk x (Array.sub r 0 db))
        | _ -> (zero, a)
    | _ -> failwith "ModPoly.divModUni: делитель не содержит x"

// y^t · p для p, которое МОЖЕТ содержать y (в отличие от shiftY)
let rec mulYPow (y: int) (t: int) (p: MPolyM) : MPolyM =
    if t = 0 || isZero p then p
    else
        match p with
        | MP (w, cs) when w = y -> MP (w, Array.append (Array.create t zero) cs)
        | MP (w, cs) when w > y -> mk w (Array.map (mulYPow y t) cs)
        | _ -> shiftY y t p

// --- диофантовы уравнения mod p^l (Geddes–Czapor–Labahn, алг. 6.2 и 6.3) ---
//
// Задача: для попарно взаимно простых по модулю p множителей f_1..f_r (по x; старшие коэффициенты
// обратимы mod p) и правой части c найти σ_1..σ_r с  Σ σ_i · b_i = c (mod M),  b_i = Π_{m≠i} f_m,
// deg_x σ_i < deg_x f_i. При deg_x c < Σ deg_x f_i решение единственно. Любое несовпадение
// (множители не взаимно просты mod p, степень c слишком велика, подъём не сошёлся) — исключение LiftFail.

exception LiftFail

let private trimArr (a: BigInteger[]) : BigInteger[] =
    let mutable n = a.Length
    while n > 0 && a.[n - 1].IsZero do n <- n - 1
    if n = a.Length then a else Array.sub a 0 n

// Одномерный (по x) многочлен → массив коэффициентов
let private uniCoeffs (x: int) (p: MPolyM) : BigInteger[] =
    match p with
    | MC c -> if c.IsZero then [||] else [| c |]
    | MP (v, cs) when v = x -> cs |> Array.map (fun c -> match c with MC k -> k | _ -> failwith "ModPoly: ожидался одномерный многочлен")
    | _ -> failwith "ModPoly: ожидался многочлен от x"

let private ofUni (x: int) (a: BigInteger[]) : MPolyM = mk x (a |> Array.map MC)

let private mulArr (m: Mod) (a: BigInteger[]) (b: BigInteger[]) : BigInteger[] =
    if a.Length = 0 || b.Length = 0 then [||]
    else
        let r = Array.create (a.Length + b.Length - 1) 0I
        for i in 0 .. a.Length - 1 do
            if not a.[i].IsZero then
                for j in 0 .. b.Length - 1 do
                    r.[i + j] <- r.[i + j] + a.[i] * b.[j]
        trimArr (r |> Array.map (red m))

// Подготовка для одномерного уравнения: все, что не зависит от правой части (считается один раз на набор множителей)
type UniPrep =
    { Md: Mod
      X: int
      Pi: int               // p как int (p < 2^31)
      L: int                // M = p^L
      Us: int[][]           // f_i mod p
      Ss: int[][]           // s_i: s_i · b_i ≡ 1 (mod p, mod u_i), deg s_i < deg u_i
      Bs: BigInteger[][] }  // b_i mod M

let prepUni (m: Mod) (x: int) (fs: MPolyM[]) : UniPrep =
    let p = int m.P
    let r = fs.Length
    let fz = fs |> Array.map (uniCoeffs x)
    let us = fz |> Array.map (fun a -> UniFactor.trimP (a |> Array.map (fun c -> int (BigInteger.Remainder (c, m.P)))))
    // степень сохраняется при редукции mod p (старший коэффициент обратим)
    if Array.exists2 (fun (a: BigInteger[]) (u: int[]) -> a.Length <> u.Length || u.Length < 2) fz us then raise LiftFail
    let mutable l = 0
    let mutable pp = 1I
    while pp < m.M do
        pp <- pp * m.P
        l <- l + 1
    if pp <> m.M then failwith "ModPoly.prepUni: M не степень P"
    let prodArr (f: int -> 'a) (mulF: 'a -> 'a -> 'a) (unit: 'a) (i: int) : 'a =
        let mutable acc = unit
        for j in 0 .. r - 1 do
            if j <> i then acc <- mulF acc (f j)
        acc
    let bs = Array.init r (fun i -> prodArr (fun j -> fz.[j]) (mulArr m) [| 1I |] i)
    let bps = Array.init r (fun i -> prodArr (fun j -> us.[j]) (UniFactor.mulP p) [| 1 |] i)
    let ss =
        Array.init r (fun i ->
            let bi = snd (UniFactor.divModP p bps.[i] us.[i])
            let (g, s, _) = UniFactor.extGcdP p bi us.[i]
            if g.Length <> 1 then raise LiftFail      // не взаимно просты mod p
            snd (UniFactor.divModP p s us.[i]))
    { Md = m; X = x; Pi = p; L = l; Us = us; Ss = ss; Bs = bs }

// Решение одномерного уравнения: p-адическая итерация (σ += p^k · решение mod p для (c − Σσb)/p^k)
let solveUni (pr: UniPrep) (c: MPolyM) : MPolyM[] =
    let m = pr.Md
    let r = pr.Us.Length
    let mutable res = uniCoeffs pr.X c |> Array.map (red m) |> trimArr
    let sigma = Array.init r (fun i -> Array.create (pr.Us.[i].Length - 1) 0I)
    let mutable pk = 1I
    let mutable k = 0
    while res.Length > 0 && k < pr.L do
        // все коэффициенты res обязаны делиться на p^k
        let pkv = pk
        let resv = res
        let ck =
            resv |> Array.map (fun v ->
                let (q, rem) = BigInteger.DivRem (v, pkv)
                if not rem.IsZero then raise LiftFail
                int (BigInteger.Remainder (q, m.P)))
            |> UniFactor.trimP
        if ck.Length > 0 then
            let mutable contrib : BigInteger[] = [||]
            for i in 0 .. r - 1 do
                let sk = snd (UniFactor.divModP pr.Pi (UniFactor.mulP pr.Pi pr.Ss.[i] ck) pr.Us.[i])
                for j in 0 .. sk.Length - 1 do
                    sigma.[i].[j] <- sigma.[i].[j] + pkv * BigInteger sk.[j]
                let t = mulArr m (sk |> Array.map BigInteger) pr.Bs.[i]
                let cur = contrib
                contrib <-
                    if cur.Length = 0 then t
                    else
                        let n = max cur.Length t.Length
                        trimArr (Array.init n (fun j ->
                            red m ((if j < cur.Length then cur.[j] else 0I) + (if j < t.Length then t.[j] else 0I))))
            let cv = contrib
            let n = max resv.Length cv.Length
            res <- trimArr (Array.init n (fun j ->
                red m ((if j < resv.Length then resv.[j] else 0I) - pkv * (if j < cv.Length then cv.[j] else 0I))))
        pk <- pk * m.P
        k <- k + 1
    if res.Length > 0 then raise LiftFail
    sigma |> Array.map (fun s -> ofUni pr.X (trimArr (s |> Array.map (red m))))

// Одномерное уравнение «с нуля» (подготовка + решение); для многократного использования — prepUni/solveUni
let diophUni (m: Mod) (x: int) (c: MPolyM) (fs: MPolyM[]) : MPolyM[] =
    solveUni (prepUni m x fs) c

// Контекст многомерного уравнения: множители каждого уровня v (переменные x, ys[0..v-1]) и произведения b_i
type DiophCtx =
    { Cm: Mod
      Cx: int
      Ys: int[]
      Bnd: int -> int                  // граница степени σ по переменной y
      Uni: UniPrep
      Fs: ResizeArray<MPolyM[]>
      Bs: ResizeArray<MPolyM[]> }

// b_i = Π_{m≠i} f_m через префиксные и суффиксные произведения
let private productsExcept (m: Mod) (fs: MPolyM[]) : MPolyM[] =
    let r = fs.Length
    let pre = Array.create (r + 1) one
    let suf = Array.create (r + 1) one
    for i in 0 .. r - 1 do pre.[i + 1] <- mul m pre.[i] fs.[i]
    for i in r - 1 .. -1 .. 0 do suf.[i] <- mul m suf.[i + 1] fs.[i]
    Array.init r (fun i -> mul m pre.[i] suf.[i + 1])

let newDiophCtx (m: Mod) (x: int) (ys: int[]) (bnd: int -> int) (fs0: MPolyM[]) : DiophCtx =
    let ctx =
        { Cm = m; Cx = x; Ys = ys; Bnd = bnd; Uni = prepUni m x fs0
          Fs = ResizeArray<MPolyM[]>(); Bs = ResizeArray<MPolyM[]>() }
    ctx.Fs.Add fs0
    ctx.Bs.Add [||]
    ctx

// Добавить следующий уровень (множители с ещё одной переменной)
let addDiophLevel (ctx: DiophCtx) (fs: MPolyM[]) : unit =
    ctx.Fs.Add fs
    ctx.Bs.Add (productsExcept ctx.Cm fs)

// Многомерное уравнение на уровне v: раскладываем c по степеням y_v; свободный член — рекурсивно по меньшему
// уровню, затем поправки при y_v^t, t = 1 .. bnd(y_v), пока остаток не обнулится
let rec diophAt (ctx: DiophCtx) (v: int) (c: MPolyM) : MPolyM[] =
    let r = ctx.Fs.[0].Length
    if isZero c then Array.create r zero
    elif v = 0 then solveUni ctx.Uni c
    else
        let m = ctx.Cm
        let y = ctx.Ys.[v - 1]
        let bs = ctx.Bs.[v]
        let sigma = Array.copy (diophAt ctx (v - 1) (subst0 y c))
        let sumProd (ds: MPolyM[]) =
            let mutable acc = zero
            for i in 0 .. r - 1 do
                if not (isZero ds.[i]) then acc <- add m acc (mul m ds.[i] bs.[i])
            acc
        let mutable err = sub m c (sumProd sigma)
        let bd = ctx.Bnd y
        let mutable t = 1
        while not (isZero err) && t <= bd do
            let ct = coeffIn y t err
            if not (isZero ct) then
                let d = diophAt ctx (v - 1) ct
                for i in 0 .. r - 1 do
                    sigma.[i] <- add m sigma.[i] (mulYPow y t d.[i])
                err <- sub m err (mulYPow y t (sumProd d))
            t <- t + 1
        if not (isZero err) then raise LiftFail
        sigma

// Многомерное диофантово уравнение уровня level: fs — множители от x и ys[0..level-1] (нижние уровни —
// подстановкой нулей), bnd — границы степеней σ по y; None — решения нет (с такими границами)
let diophMulti (m: Mod) (x: int) (ys: int[]) (bnd: int -> int) (level: int) (c: MPolyM) (fs: MPolyM[]) : MPolyM[] option =
    try
        let levels = Array.create (level + 1) fs
        for v in level .. -1 .. 1 do
            levels.[v - 1] <- levels.[v] |> Array.map (subst0 ys.[v - 1])
        let ctx = newDiophCtx m x ys bnd levels.[0]
        for v in 1 .. level do addDiophLevel ctx levels.[v]
        Some (diophAt ctx level c)
    with LiftFail -> None

// --- многомерный подъём Хензеля mod p^l, все r множителей одновременно (Geddes, алг. 6.4) ---
//
// a — многочлен от x и ys (точка подъёма — ноль после сдвига), lcs.[i] — предсказанный старший по x
// коэффициент i-го множителя (многочлен от ys; Π lcs = lc_x a), fs0.[i] — образы при ys = 0 (многочлены
// от x со старшими коэффициентами lcs.[i](0), Π fs0 ≡ a(x, 0) mod M, попарно взаимно просты mod p).
// Для j = 1..k (ys.[j-1]): старшие коэффициенты множителей заменяются на lcs при ys.[j..] = 0, ошибка
// e = a^(j) − Π f_i раскладывается по степеням y_j, поправка при y_j^t решает диофантово уравнение
// Σ σ_i · Π_{m≠i} f_m = e_t (уровень j−1). Ненулевая ошибка после deg_{y_j} a шагов — None.
let henselMulti (m: Mod) (x: int) (ys: int[]) (a: MPolyM) (lcs: MPolyM[]) (fs0: MPolyM[]) : MPolyM[] option =
    try
        let k = ys.Length
        let r = fs0.Length
        let bnd (y: int) = degIn y a
        // a^(j) и lc^(j): переменные ys.[j..k-1] := 0
        let aj = Array.create (k + 1) a
        let lj = Array.create (k + 1) lcs
        for j in k .. -1 .. 1 do
            aj.[j - 1] <- subst0 ys.[j - 1] aj.[j]
            lj.[j - 1] <- lj.[j] |> Array.map (subst0 ys.[j - 1])
        let ctx = newDiophCtx m x ys bnd fs0
        let mutable f = fs0
        for j in 1 .. k do
            let y = ys.[j - 1]
            // множители предыдущего уровня — основа диофантовых уравнений шага j (при j = 1 это fs0)
            if j >= 2 then addDiophLevel ctx f
            let bd = bnd y
            let lcj = lj.[j]
            let fj = f |> Array.mapi (fun i g -> replaceLc x lcj.[i] g)
            let prodTrunc () =
                let mutable acc = one
                for i in 0 .. r - 1 do acc <- truncDeg y bd (mul m acc fj.[i])
                acc
            let mutable e = sub m aj.[j] (prodTrunc ())
            let mutable t = 1
            while not (isZero e) && t <= bd do
                let ct = coeffIn y t e
                if not (isZero ct) then
                    let sigma = diophAt ctx (j - 1) ct
                    for i in 0 .. r - 1 do
                        fj.[i] <- add m fj.[i] (mulYPow y t sigma.[i])
                    e <- sub m aj.[j] (prodTrunc ())
                t <- t + 1
            if not (isZero e) then raise LiftFail
            f <- fj
        Some f
    with LiftFail -> None
