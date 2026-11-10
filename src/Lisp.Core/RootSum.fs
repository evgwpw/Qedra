// Сумма по корням (Шаг 21h): форма (root-sum t Q E) = Σ E(t) по корням t многочлена Q(t) (с учётом кратности),
// в математическом языке — rootsum(E, t, Q). Используется, когда корни Q не выражаются явно (интеграл рациональной
// функции: ∫ A/D = … + Σ_{Q(t)=0} t·log S(t, x)).
//
// Каноническая форма (simplify идемпотентен):
//   * E = 0 или Q без корней → 0;  E не зависит от t → deg Q · E;
//   * линейность: Σ (E1 + E2) = Σ E1 + Σ E2, множители без t выносятся;
//   * Q раскладывается над ℚ(параметры): Σ_Q = Σ k_i·Σ_{f_i}; множитель степени 1 — корень явный, подстановка;
//   * иначе Q — единственный неприводимый (примитивный, с положительным старшим коэффициентом) и связанная переменная
//     переименована в первое из t, s, u, v, w, z, t1, ... , не входящее свободно в Q и E (альфа-эквивалентные формы совпадают).
// Хук Simplify.rootSumHook устанавливает install (вызывается при создании окружения).
module RootSum

open System.Collections.Generic
open System.Numerics
open Types
open Numeric
open MPoly
open PolyGcd
open PolyExpr

// Свободные символы выражения (голова формы — не символ-переменная; связанная переменная root-sum исключается)
let rec freeSymsInto (acc: HashSet<string>) (e: LispValue) : unit =
    match e with
    | LispSym s -> acc.Add s |> ignore
    | LispList [LispSym "root-sum"; LispSym tv; q; body] ->
        let inner = HashSet<string>()
        freeSymsInto inner q
        freeSymsInto inner body
        inner.Remove tv |> ignore
        acc.UnionWith inner
    | LispList (LispSym _ :: args) -> for a in args do freeSymsInto acc a
    | LispList items -> for a in items do freeSymsInto acc a
    | LispVector items -> for a in items do freeSymsInto acc a
    | _ -> ()

let freeSyms (e: LispValue) : HashSet<string> =
    let acc = HashSet<string>()
    freeSymsInto acc e
    acc

let containsFree (name: string) (e: LispValue) : bool = (freeSyms e).Contains name

// Одновременная подстановка символов, без захвата связанной переменной root-sum (при угрозе захвата она переименовывается)
let rec substFree (rules: (string * LispValue) list) (e: LispValue) : LispValue =
    if rules.IsEmpty then e
    else
        match e with
        | LispSym s ->
            (match rules |> List.tryFind (fun (n, _) -> n = s) with
             | Some (_, v) -> v
             | None -> e)
        | LispList [LispSym "root-sum"; LispSym tv; q; body] ->
            let rs = rules |> List.filter (fun (n, _) -> n <> tv)
            if rs.IsEmpty then e
            else
                let valSyms = HashSet<string>()
                for (_, v) in rs do freeSymsInto valSyms v
                if valSyms.Contains tv then
                    let used = HashSet<string>()
                    freeSymsInto used q
                    freeSymsInto used body
                    used.UnionWith valSyms
                    for (n, _) in rs do used.Add n |> ignore
                    let mutable k = 1
                    while used.Contains (tv + string k) do k <- k + 1
                    let nm = tv + string k
                    let ren = [ (tv, LispSym nm) ]
                    LispList [ LispSym "root-sum"; LispSym nm; substFree rs (substFree ren q); substFree rs (substFree ren body) ]
                else LispList [ LispSym "root-sum"; LispSym tv; substFree rs q; substFree rs body ]
        | LispList (LispSym h :: args) -> LispList (LispSym h :: List.map (substFree rules) args)
        | LispList items -> LispList (List.map (substFree rules) items)
        | LispVector items -> LispVector (Array.map (substFree rules) items)
        | _ -> e

let private canonicalNames : string list =
    [ "t"; "s"; "u"; "v"; "w"; "z" ] @ [ for k in 1 .. 200 -> sprintf "t%d" k ]

let private unit1 (l: LispValue list) : LispValue =
    match l with
    | [ single ] -> single
    | _ -> LispList (LispSym "*" :: l)

let private rawForm (args: LispValue list) : LispValue = LispList (LispSym "root-sum" :: args)

// Σ E(α) по корням многочлена fe(t) (степень m ≥ 1, корни — с учётом кратности), если E — многочлен от t:
// Σ_j e_j·p_j, p_j — степенные суммы корней (формулы Ньютона над ℚ(параметры)); иначе None
let private polynomialSum (tv: string) (fe: LispValue) (e: LispValue) : LispValue option =
    let ts = LispSym tv
    let bad =
        kernelsOf e |> List.exists (fun k -> (match k with LispSym _ -> false | _ -> containsFree tv k))
    if bad then None
    else
        let ctx = makeCtx [ fe; e ] [ ts ]
        let ti = varIndex ctx ts
        let (fn, _) = toRatFun ctx fe
        let (en, ed) = toRatFun ctx e
        let m = degIn ti fn
        if m < 1 || degIn ti ed > 0 then None
        else
            let am = coeffIn ti m fn
            // c_i = a_{m−i}/a_m (i = 1..m) — коэффициенты нормированного многочлена
            let c = Array.init (m + 1) (fun i -> if i = 0 then RatInt.kone else RatInt.kmk (coeffIn ti (m - i) fn) am)
            let d = degIn ti en
            let p : RatInt.KP[] = Array.create (max (d + 1) 1) RatInt.kzero
            p.[0] <- RatInt.kmk (ofInt (BigInteger m)) one
            for k in 1 .. d do
                let mutable s = if k <= m then RatInt.kmul (RatInt.kmk (ofInt (BigInteger k)) one) c.[k] else RatInt.kzero
                for i in 1 .. min (k - 1) m do
                    s <- RatInt.kadd s (RatInt.kmul c.[i] p.[k - i])
                p.[k] <- RatInt.kneg s
            let mutable total = RatInt.kzero
            for j in 0 .. d do
                let ej = coeffIn ti j en
                if not (isZero ej) then total <- RatInt.kadd total (RatInt.kmul (RatInt.ofPoly ej) p.[j])
            if RatInt.kIsZero total then Some (LispInteger 0I)
            else Some (Simplify.simplify (ratFunToExpr ctx (normalizeFrac (total.N, mul total.D ed))))

// Разбор Q: (контекст, номер t, числитель в ℚ[…], разложение над ℚ(параметры)). Кэш по (t, запись Q): simplify вызывает хук
// на каждом шаге дифференцирования/подстановки, а разложение многочлена — самая дорогая часть
let private factorCache =
    System.Collections.Concurrent.ConcurrentDictionary<string, Ctx * int * MPoly * (MPoly * int) list>()

let private analyzeQ (tv: string) (q: LispValue) : Ctx * int * MPoly * (MPoly * int) list =
    let key = tv + "|" + Printer.prettyPrint q
    match factorCache.TryGetValue key with
    | true, v -> v
    | _ ->
        let ts = LispSym tv
        let ctx = makeCtx [ q ] [ ts ]
        let ti = varIndex ctx ts
        let (n, _) = toRatFun ctx q
        let fs = if isZero n || degIn ti n <= 0 then [] else snd (PolyFactor.factorPoly n)
        let v = (ctx, ti, n, fs)
        if factorCache.Count > 4000 then factorCache.Clear()
        factorCache.[key] <- v
        v

// Упрощение (root-sum t Q E); аргументы уже упрощены
let rec simplifyRootSum (args: LispValue list) : LispValue =
    match args with
    | [ LispSym tv; q; e ] ->
        (match e with
         | _ when (match e with LispInteger z -> z.IsZero | _ -> false) -> LispInteger 0I
         | LispList (LispSym "+" :: terms) ->
             Simplify.simplify (LispList (LispSym "+" :: (terms |> List.map (fun term -> simplifyRootSum [ LispSym tv; q; term ]))))
         | LispList (LispSym "*" :: factors) when factors |> List.exists (fun f -> not (containsFree tv f)) ->
             let consts, deps = factors |> List.partition (fun f -> not (containsFree tv f))
             let rest = if deps.IsEmpty then LispInteger 1I else Simplify.simplify (unit1 deps)
             Simplify.simplify (LispList [ LispSym "*"; unit1 consts; simplifyRootSum [ LispSym tv; q; rest ] ])
         | _ -> simplifyCore tv q e)
    | _ -> rawForm args

and private simplifyCore (tv: string) (q: LispValue) (e: LispValue) : LispValue =
    let ts = LispSym tv
    let hasTKernel =
        // ядро, не являющееся символом и зависящее от t: Q не многочлен от t
        kernelsOf q |> List.exists (fun k -> (match k with LispSym _ -> false | _ -> containsFree tv k))
    if hasTKernel then rawForm [ ts; q; e ]
    else
        let (ctx, ti, n, fs0) = analyzeQ tv q
        if isZero n then rawForm [ ts; q; e ]
        elif degIn ti n <= 0 then LispInteger 0I                  // нет корней
        else
            let fs = fs0 |> List.filter (fun (f, _) -> degIn ti f > 0)
            if not (containsFree tv e) then
                let total = fs |> List.sumBy (fun (f, k) -> k * degIn ti f)
                Simplify.simplify (LispList [ LispSym "*"; LispInteger (BigInteger total); e ])
            else
                match fs with
                | [ (f, 1) ] ->
                    if degIn ti f = 1 then
                        let c1 = coeffIn ti 1 f
                        let c0 = coeffIn ti 0 f
                        let root = ratFunToExpr ctx (normalizeFrac (neg c0, c1))
                        Simplify.simplify (substFree [ (tv, root) ] e)
                    else
                      match polynomialSum tv (toExpr ctx (unitNormal f)) e with
                      | Some r -> r
                      | None ->
                        let qn = toExpr ctx (unitNormal f)
                        let used = freeSyms qn
                        used.UnionWith (freeSyms e)
                        used.Remove tv |> ignore
                        let name = canonicalNames |> List.find (fun nm -> not (used.Contains nm))
                        if name = tv then rawForm [ ts; qn; e ]
                        else
                            let ren = [ (tv, LispSym name) ]
                            rawForm [ LispSym name; Simplify.simplify (substFree ren qn); Simplify.simplify (substFree ren e) ]
                | _ ->
                    // Q раскладывается: Σ_Q = Σ k_i · Σ_{f_i}
                    let parts =
                        fs |> List.map (fun (f, k) ->
                            let r = simplifyRootSum [ ts; toExpr ctx (unitNormal f); e ]
                            if k = 1 then r else Simplify.simplify (LispList [ LispSym "*"; LispInteger (BigInteger k); r ]))
                    Simplify.simplify (LispList (LispSym "+" :: parts))

let install () : unit =
    Simplify.rootSumHook <- simplifyRootSum
