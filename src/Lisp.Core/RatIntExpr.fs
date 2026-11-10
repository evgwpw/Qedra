// Интегрирование рациональных функций: мост «выражение Lisp ↔ RatInt» (шаг 21h'; вынесено из RatInt.fs).
// rat-integrate (сырой результат ЛРТ) и rat-integrate-log (первообразная в явном виде: логарифмы, арктангенсы, root-sum).
// Чистая алгебра (KP, Эрмит, ЛРТ, LogToAtan, точная проверка) — RatInt.fs в Cas.Algebra.
module RatIntExpr

open System.Numerics
open Types
open Numeric
open MPoly
open PolyGcd
open PolyExpr
open RatInt

let kpExpr (ctx: Ctx) (a: KP) : LispValue = ratFunToExpr ctx (a.N, a.D)

// g = gnum/gden как выражение
let ratPartExpr (ctx: Ctx) ((gn, gd): KP * KP) : LispValue =
    if kIsZero gn then LispInteger 0I
    else ratFunToExpr ctx (normalizeFrac (mul gn.N gd.D, mul gn.D gd.N))

// (rat-integrate e x t): сырой результат ЛРТ — (∫полином, рациональная часть, ((Q S i) ...));
// Q и S — выражения от t (символ t свободен от e), S — от t и x
let ratIntegrateRaw (e: LispValue) (x: LispValue) (t: LispValue) : LispValue =
    let simp = Simplify.simplify e
    let xs = Simplify.simplify x
    let ts = Simplify.simplify t
    let ctx = makeCtx [simp] [ts; xs]
    let xi = varIndex ctx xs
    let ti = varIndex ctx ts
    let (n, d) = toRatFun ctx simp
    let r = integrateRational xi ti n d
    let terms =
        r.Log |> List.map (fun tm ->
            LispList [toExpr ctx tm.Q; toExpr ctx tm.S; LispInteger (BigInteger tm.Mult)])
    LispList [kpExpr ctx r.PolyInt; ratPartExpr ctx r.RatPart; LispList terms; kpExpr ctx r.LogScale]

// ---------- выражения ----------

let private mulE (xs: LispValue list) : LispValue = LispList (LispSym "*" :: xs)
let private addE (xs: LispValue list) : LispValue = LispList (LispSym "+" :: xs)
let private powE (b: LispValue) (n: LispValue) : LispValue = LispList [ LispSym "^"; b; n ]
let private halfE : LispValue = LispRational (1I, 2I)

let private intE (n: BigInteger) : LispValue = LispInteger n

// √κ как выражение (κ — бесквадратное натуральное; 1 → 1)
let private sqrtKappa (kappa: BigInteger) : LispValue =
    if kappa.IsOne then LispInteger 1I else powE (intE kappa) halfE

// Σ_k s_k·x^k как выражение (s_k — выражения)
let private polyExpr (xe: LispValue) (cs: LispValue list) : LispValue =
    addE (cs |> List.mapi (fun k c -> if k = 0 then c else mulE [ c; powE xe (LispInteger (BigInteger k)) ]))

type private LogCtx =
    { Ctx: Ctx; X: int; T: int; Real: bool }

// Член для неприводимого множителя f степени 1
let private linearTerm (lc: LogCtx) (f: MPoly) (coeffs: KP[]) : LispValue =
    let c1 = coeffIn lc.T 1 f
    let c0 = coeffIn lc.T 0 f
    let alpha = kmk (neg c0) c1
    let s = kpolyOf lc.X coeffs
    mulE [ kpExpr lc.Ctx alpha; LispList [ LispSym "log"; toExpr lc.Ctx (cleanPoly lc.X s) ] ]

// Член для f = a·t² + b·t + c (неприводимого над ℚ(параметры))
let private quadraticTerm (lc: LogCtx) (f: MPoly) (coeffs: KP[]) : LispValue =
    let ctx, x, t = lc.Ctx, lc.X, lc.T
    let a2, b1, c0 = coeffIn t 2 f, coeffIn t 1 f, coeffIn t 0 f
    let delta = sub (mul b1 b1) (mulConst (4I, 1I) (mul a2 c0))
    let twoA = mulConst (2I, 1I) a2
    let u = kmk (neg b1) twoA
    let pk = coeffs |> Array.map (kcoef t 0)
    let qk = coeffs |> Array.map (kcoef t 1)
    let xe = ctx.Vars.[x]
    let kind = classifySign delta
    match kind with
    | Neg (kappa, gk) when lc.Real ->
        // вещественная форма: u ± i·v, v = w0·ω, ω = √κ, w0 = g/(2a)
        let w0 = kmul gk (kmk one twoA)
        let ak = Array.init coeffs.Length (fun k -> kadd pk.[k] (kmul qk.[k] u))
        let bk = Array.init coeffs.Length (fun k -> kmul qk.[k] w0)
        let apoly = kpolyOf x ak
        let bpoly = kpolyOf x bk
        let kappaK = kmk (ofInt kappa) one
        let sqrtE = sqrtKappa kappa
        let uTerm =
            if kIsZero u then None
            else
                let nsum = kadd (kmul apoly apoly) (kmul kappaK (kmul bpoly bpoly))
                Some (mulE [ kpExpr ctx u; LispList [ LispSym "log"; toExpr ctx (cleanPoly x nsum) ] ])
        if kIsZero bpoly then
            // S(α) = S(ᾱ): вклад 2u·log A (A²+B² = A²)
            match uTerm with
            | Some tm -> addE [ tm ]
            | None -> LispInteger 0I
        else
            let tag = if kappa.IsOne then 0 else 1
            let args = logToAtanT x kappaK { P = apoly; E = 0 } { P = bpoly; E = tag }
            let argExpr (c: TP) =
                if c.E = 0 then kpExpr ctx c.P else mulE [ kpExpr ctx c.P; sqrtE ]
            let v = mulE [ kpExpr ctx w0; sqrtE ]
            let atans = args |> List.map (fun c -> mulE [ LispInteger 2I; v; LispList [ LispSym "atan"; argExpr c ] ])
            let atanTerm = if atans.IsEmpty then LispInteger 0I else addE atans
            addE ((match uTerm with Some tm -> [ tm ] | None -> []) @ [ atanTerm ])
    | _ ->
        // корни в радикалах: α± = (−b ± √Δ)/(2a)
        let omega =
            match kind with
            | Pos (kappa, gk) -> mulE [ kpExpr ctx gk; sqrtKappa kappa ]
            | Neg (kappa, gk) -> mulE [ LispSym "%i"; kpExpr ctx gk; sqrtKappa kappa ]
            | Unknown -> powE (toExpr ctx delta) halfE
        let bE = toExpr ctx b1
        let invTwoA = powE (toExpr ctx twoA) (LispInteger -1I)
        let term (sign: int) =
            let alpha = mulE [ addE [ mulE [ LispInteger -1I; bE ]; (if sign > 0 then omega else mulE [ LispInteger -1I; omega ]) ]; invTwoA ]
            let cs = Array.init coeffs.Length (fun k -> addE [ kpExpr ctx pk.[k]; mulE [ kpExpr ctx qk.[k]; alpha ] ])
            mulE [ alpha; LispList [ LispSym "log"; polyExpr xe (List.ofArray cs) ] ]
        addE [ term 1; term -1 ]

// Аргумент логарифма для S(t, x) = Σ s_k(t)·x^k по коэффициентам s_k (многочлены по t степени < deg f):
// скаляры поля K (по параметрам и числа) отбрасываются — log(c·S) = log c + log S, c не зависит от x и t
// (постоянная интегрирования)
let private argOf (lc: LogCtx) (cs: MPoly[]) : LispValue =
    let i = cs.Length - 1
    let arg =
        if degIn lc.T cs.[i] <= 0 then
            let poly = cs |> Array.mapi (fun k c -> mul c (pow (var lc.X) k)) |> Array.fold add zero
            toExpr lc.Ctx (unitNormal (if mainVar poly = lc.X then divExactExn poly (contentMain poly) else poly))
        else
            // старший коэффициент по x зависит от t: нормировка x^i + Σ (c_k/lc)·x^k с коэффициентами — рациональными функциями
            // от t (обратный к lc по модулю f дал бы огромные коэффициенты). Старший коэффициент 1 — ветвь log непрерывна
            // по x для невещественных корней (Im S(α, x) постоянна при i = 1)
            let g = cs |> Array.fold (fun acc c -> if isZero c then acc else gcd acc c) zero
            let cs0 = cs |> Array.map (fun c -> if isZero c || isOne g then c else divExactExn c g)
            // числовое содержание: общий рациональный множитель коэффициентов
            let (cInt, _) = primitiveInt (cs0 |> Array.mapi (fun k c -> mul c (pow (var lc.X) k)) |> Array.fold add zero)
            let cs1 = cs0 |> Array.map (fun c -> mulConst (ratDiv (1I, 1I) cInt) c)
            let lcn = toExpr lc.Ctx cs1.[i]
            let xe = lc.Ctx.Vars.[lc.X]
            let lower =
                [ for k in 0 .. i - 1 do
                    if not (isZero cs1.[k]) then
                        let ck = mulE [ toExpr lc.Ctx cs1.[k]; powE lcn (LispInteger -1I) ]
                        yield (if k = 0 then ck else mulE [ ck; powE xe (LispInteger (BigInteger k)) ]) ]
            addE ((if i = 1 then xe else powE xe (LispInteger (BigInteger i))) :: lower)
    arg

// Член для f степени ≥ 3: сумма по корням. Параметр нормируется подстановкой t → t/c:
// Q_c(t) = c^d·Q(t/c) и s_k(t) → c^D·s_k(t/c) с общим D, т.е. S_c = c^D·S(t/c, x). Корни Q_c равны c·α,
// поэтому сумма по ним равна c·исходной, и перед членом ставится множитель 1/c (его же учитывает verifyExact).
// Из c = 1..6 берётся самая короткая запись (c = 1 — без нормировки; при равной длине остаётся она)
let private rootSumTerm (lc: LogCtx) (f: MPoly) (coeffs: MPoly[]) (tSym: LispValue) =
    // D — наименьшее общее, при котором c^D·s_k(t/c) целые: в s_k есть t^j, j ≤ deg_t s_k
    let dmax = coeffs |> Array.mapi (fun k c -> k + max 0 (degIn lc.T c)) |> Array.max
    let cand (c: bigint) =
        let fC = unitNormal (scaleParam c lc.T f)
        let csC = coeffs |> Array.map (scaleParamWith c dmax lc.T)
        let logE = LispList [ LispSym "log"; argOf lc csC ]
        let eC =
            if c.IsOne then mulE [ tSym; logE ]
            else mulE [ LispRational (1I, c); tSym; logE ]
        (LispList [ LispSym "root-sum"; tSym; toExpr lc.Ctx fC; eC ], fC, csC |> Array.map ofPoly, (1I, c))
    [ 1I; 2I; 3I; 4I; 5I; 6I ]
    |> List.map cand
    |> List.minBy (fun (ex, _, _, _) -> (Printer.prettyPrint ex).Length)

// Члены логарифмической части для одного Q_i: (выражение, f, коэффициенты S_f по x — элементы K[t]/(f) с точностью до
// скаляра, множитель выражения — см. verifyExact)
let private logTermsOf (lc: LogCtx) (tSym: LispValue) (tm: LrtTerm) : (LispValue * MPoly * KP[] * Q) list =
    let (_, fs) = PolyFactor.factorPoly tm.Q
    fs |> List.choose (fun (f, _) ->
        let m = degIn lc.T f
        if m <= 0 then None
        else
            match m with
            // линейный f: S(α, x) — многочлен над K, скаляр не важен (нормировка не нужна)
            | 1 ->
                let cs = reduceKP lc.X lc.T f tm.S false
                Some (linearTerm lc f cs, f, cs, (1I, 1I))
            | 2 ->
                // нормировка по x (старший коэффициент 1) — только без параметров: над ℚ(параметры) обратный к lc_x(S) по модулю f
                // и сокращения дробей стоят на порядки дороже; для вещественной формы (атаны, лог. многочленов) она не нужна
                let cs = reduceKP lc.X lc.T f tm.S (lc.Ctx.Vars.Length <= 2)
                Some (quadraticTerm lc f cs, f, cs, (1I, 1I))
            | _ ->
                // без нормировки по x (обратный к lc_x(S) по модулю f раздувает коэффициенты; общий скаляр не важен)
                let coeffs = reduceScaled lc.X lc.T f tm.S
                Some (rootSumTerm lc f coeffs tSym))

// (rat-integrate-log e x t real): первообразная рациональной функции e по x — выражение (+ полином рациональная-часть члены…).
// t — свободный от e символ (связанная переменная сумм по корням); real — вещественная форма для пар сопряжённых корней
// (допустимо, когда все параметры вещественны). Структура ответа проверяется ТОЧНО в рациональных точках (verifyExact);
// несовпадение — внутренняя ошибка (исключение)
let ratIntegrateLog (e: LispValue) (x: LispValue) (t: LispValue) (real: bool) : LispValue =
    let simp = Simplify.simplify e
    let xs = Simplify.simplify x
    let ts = Simplify.simplify t
    let ctx = makeCtx [ simp ] [ ts; xs ]
    let xi = varIndex ctx xs
    let ti = varIndex ctx ts
    let (n, d) = toRatFun ctx simp
    let r = integrateRational xi ti n d
    let lc = { Ctx = ctx; X = xi; T = ti; Real = real }
    let items = r.Log |> List.collect (logTermsOf lc ts)
    if not (verifyExact xi ti n d r (items |> List.map (fun (_, f, cs, mul) -> (f, cs, mul)))) then
        failwith "RatInt: внутренняя ошибка — точная проверка первообразной не пройдена"
    let terms = items |> List.map (fun (ex, _, _, _) -> ex)
    let logPart =
        if terms.IsEmpty then []
        elif isOne r.LogScale.N && isOne r.LogScale.D then terms
        else
            let le = kpExpr ctx r.LogScale
            terms |> List.map (fun tm -> mulE [ le; tm ])
    LispList (LispSym "+" :: kpExpr ctx r.PolyInt :: ratPartExpr ctx r.RatPart :: logPart)
