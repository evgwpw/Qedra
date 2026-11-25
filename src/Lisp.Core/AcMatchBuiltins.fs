// Шаг MATCH.FS: ядро AC-сопоставителя (lib/match.lisp: ac-tick … ac-try) на F#. Тот же алгоритм и тот же порядок перебора,
// что у Lisp-эталона (флаг match::*ac-native* #f включает старый путь для сравнения).
//   (ac-native-ok? ip)                              → #t, если скомпилированный образец ip понятен F#-ядру (нет узлов NV — голова-переменная)
//   (ac-search-native ip ne ctx on-solution id-skip) → результат: первый истинный результат (on-solution b), иначе #f
//        ip — скомпилированный образец (ac-compile), ne — нормализованное выражение, ctx — вектор #(счётчик лимит превышен? ident explicit),
//        читается и пишется (счётчик, флаг превышения); on-solution — Lisp-функция от привязок ((имя значение) ...) (последняя первой),
//        зовётся только на полном решении; #f — искать дальше; id-skip — значение match::ac-id-skip
//   (ac-native-group-used)                          → признак «решение получено групповой привязкой» последнего поиска (ac-group-used)
// Скомпилированный образец разбирается в дерево F# один раз и кэшируется по ссылке на объект ip (ConditionalWeakTable).
module AcMatchBuiltins

open System.Runtime.CompilerServices
open Types
open Builtins
open Numeric

type MNode =
    | NK of LispValue
    | NV of name: string * opt: bool
    | NN of head: LispValue * args: MNode[]
    | NA of op: string * fixedItems: MNode list * seg: string * grp: bool
    | NBad

type Ctx(count: int64, limit: double, exceeded: bool, ident: bool, expl: bool, idSkip: bool, one: bool) =
    member val Count = count with get, set
    member val Exceeded = exceeded with get, set
    member _.Limit = limit
    member _.Ident = ident
    member _.Expl = expl
    member _.IdSkip = idSkip
    member _.One = one

type K = (string * LispValue) list -> LispValue

let private fls = LispBool false
let mutable private groupUsed = false

// --- разбор ip ---
exception private BadIp

let private symName (v: LispValue) : string =
    match v with
    | LispSym s -> s
    | _ -> raise BadIp

let private listOf (v: LispValue) : LispValue list =
    match v with
    | LispList xs -> xs
    | LispNil -> []
    | _ -> raise BadIp

let rec private parse (ip: LispValue) : MNode =
    match ip with
    | LispList (LispSym "K" :: [ x ]) -> NK x
    | LispList [ LispSym "V"; n; o ] -> NV (symName n, (match o with LispBool true -> true | _ -> false))
    | LispList (LispSym "N" :: head :: args) -> NN (head, args |> List.map parse |> Array.ofList)
    | LispList [ LispSym "A"; op; fixedItems; seg; grp ] ->
        let s = match seg with LispBool false -> null | LispSym n -> n | _ -> raise BadIp
        NA (symName op, listOf fixedItems |> List.map parse, s, (match grp with LispBool false -> false | _ -> true))
    | _ -> raise BadIp

let private table = ConditionalWeakTable<LispValue, MNode>()

let private nodeOf (ip: LispValue) : MNode =
    match table.TryGetValue ip with
    | true, n -> n
    | _ ->
        let n = try parse ip with BadIp -> NBad
        table.AddOrUpdate (ip, n)
        n

// --- ядро ---
let inline private tick (c: Ctx) : bool =
    c.Count <- c.Count + 1L
    if float c.Count > c.Limit then c.Exceeded <- true
    not c.Exceeded

let private bind (name: string) (v: LispValue) (binds: (string * LispValue) list) (k: K) : LispValue =
    let mutable l = binds
    let mutable found = false
    let mutable same = false
    while not found && not l.IsEmpty do
        let (n, x) = l.Head
        if System.String.Equals (n, name) then
            found <- true
            same <- structEqual x v
        else l <- l.Tail
    if found then (if same then k binds else fls)
    else k ((name, v) :: binds)

let private build (op: string) (items: LispValue list) : LispValue =
    match items with
    | [] -> if op = "+" then LispInteger 0I else LispInteger 1I
    | [ x ] -> x
    | _ -> LispList (LispSym op :: items)

let inline private skippable (c: Ctx) (node: MNode) (op: string) : bool =
    match node with
    | NV (_, opt) -> if c.Expl then (opt || op <> "^") else c.Ident
    | _ -> false

// MATCH.ONE: точная семантика OneIdentity для вырожденного узла +/* (один аргумент выражения):
// взять его может одна переменная образца, остальные обязаны быть необязательными (?x.) — см. lib/match.lisp
let inline private nodeOptional (node: MNode) : bool =
    match node with
    | NV (_, opt) -> opt
    | _ -> false

let private oneOk (c: Ctx) (op: string) (fixedItems: MNode list) (e: LispValue) : bool =
    if not c.One then true
    else
        match e with
        | LispList (LispSym h :: _) when h = op -> true
        | _ ->
            let n = List.length fixedItems
            n <= 1 || (fixedItems |> List.filter nodeOptional |> List.length) >= n - 1

let rec private mt (c: Ctx) (ip: MNode) (e: LispValue) (binds: (string * LispValue) list) (k: K) : LispValue =
    if not (tick c) then fls
    else
        match ip with
        | NK x -> if structEqual x e then k binds else fls
        | NV (n, _) -> bind n e binds k
        | NN (head, args) ->
            match e with
            | LispList (h :: t) when structEqual h head ->
                let r = if args.Length = t.Length then mtSeq c args 0 t binds k else fls
                if isTruthy r || c.Exceeded then r else mtRecipPow c head args e binds k
            | _ ->
                // единица степени: (^ ?x ?n) против не-степени e — это e^1 (только для необязательного показателя)
                if c.Ident && (match head with LispSym "^" -> true | _ -> false) && args.Length = 2
                   && not (match e with LispList (LispSym "^" :: _) -> true | _ -> false)
                   && skippable c args.[1] "^"
                then mtSeq c args 0 [ e; LispInteger 1I ] binds k
                else fls
        | NA (op, fixedItems, seg, grp) -> mtAc c op fixedItems seg grp e binds k
        | NBad -> fls

// RUBI.TRIG.4: образец (^ (^ B -1) E) и (^ (* ?d. (^ B -1)) E) — Mathematica Csc[u]^n_ в форме ядра (csc u = sin(u)^-1) —
// сопоставляется со степенью (^ T m): B с T, E с -m (?d. — с 1). Запасной путь, после обычного разбора; см. lib/match.lisp ac-recip-pow
and private mtRecipPow (c: Ctx) (head: LispValue) (args: MNode[]) (e: LispValue) binds (k: K) : LispValue =
    match head, args, e with
    | LispSym "^", [| baseN; expN |], LispList [ LispSym "^"; t; m ] ->
        let isM1 (n: MNode) = (match n with NK (LispInteger v) when v = -1I -> true | _ -> false)
        let rb =
            match baseN with
            | NN (LispSym "^", [| b; one |]) when isM1 one -> Some (b, null)
            | NA ("*", [ NV (d, true); NN (LispSym "^", [| b; one |]) ], null, _) when isM1 one -> Some (b, d)
            | NA ("*", [ NN (LispSym "^", [| b; one |]); NV (d, true) ], null, _) when isM1 one -> Some (b, d)
            | _ -> None
        match rb with
        | None -> fls
        | Some (b, d) ->
            let neg =
                if isNumber m then sub (LispInteger 0I) m
                else
                    match m with
                    | LispList [ LispSym "*"; LispInteger v; q ] when v = -1I -> q
                    | _ -> LispList [ LispSym "*"; LispInteger -1I; m ]
            mt c b t binds (fun b1 ->
                let withD (k2: K) = if isNull d then k2 b1 else bind d (LispInteger 1I) b1 k2
                withD (fun b2 -> mt c expN neg b2 k))
    | _ -> fls

and private mtSeq (c: Ctx) (args: MNode[]) (i: int) (es: LispValue list) binds (k: K) : LispValue =
    if i >= args.Length then k binds
    else
        match es with
        | e :: rest -> mt c args.[i] e binds (fun b -> mtSeq c args (i + 1) rest b k)
        | [] -> fls

and private mtAc (c: Ctx) (op: string) (fixedItems: MNode list) (seg: string) (grp: bool) (e: LispValue) binds (k: K) : LispValue =
    let items =
        match e with
        | LispList (LispSym h :: t) when h = op -> t
        | _ -> [ e ]
    let nitems = List.length items
    let nfixed = List.length fixedItems
    let bad =
        (not (oneOk c op fixedItems e))
        || (if c.Ident then
                nitems < (fixedItems |> List.filter (fun f -> not (skippable c f op)) |> List.length)
                || (isNull seg && nitems > nfixed && not grp
                    && not (op = "+" && fixedItems |> List.exists nodeOptional))
            elif not (isNull seg) then nitems < nfixed
            else nitems <> nfixed)
    if bad then fls else fixedF c op fixedItems items seg binds k grp

and private bindIdent (c: Ctx) (op: string) (fixedItems: MNode list) (seg: string) binds (k: K) : LispValue =
    match fixedItems with
    | [] -> if not (isNull seg) then bind seg (build op []) binds k else k binds
    | f :: rest ->
        if skippable c f op then
            match f with
            | NV (n, _) -> bind n (build op []) binds (fun b -> bindIdent c op rest seg b k)
            | _ -> fls
        else fls

and private fixedF (c: Ctx) (op: string) (fixedItems: MNode list) (items: LispValue list) (seg: string) binds (k: K) (grp: bool) : LispValue =
    match fixedItems with
    | [] ->
        if not (isNull seg) then bind seg (build op items) binds k
        elif items.IsEmpty then k binds
        else fls
    | f :: rest ->
        if items.IsEmpty && c.Ident then
            if fixedItems |> List.forall (fun x -> skippable c x op) then bindIdent c op fixedItems seg binds k else fls
        elif (not c.Ident) && List.length items < List.length fixedItems then fls
        else tryF c op f rest [] items seg binds k grp

// before — уже перебранные аргументы (в обратном порядке), after — ещё не перебранные
and private tryF (c: Ctx) (op: string) (p: MNode) (rest: MNode list) (before0: LispValue list) (after0: LispValue list)
                 (seg: string) binds (k: K) (grp: bool) : LispValue =
    let mutable before = before0
    let mutable after = after0
    let mutable result = fls
    let mutable fin = false
    while not fin do
        match after with
        | [] ->
            let r = trySkip c op p rest before seg binds k
            result <- (if isTruthy r then r else tryGroup c op p rest before seg binds k grp)
            fin <- true
        | a :: tl ->
            if List.exists (fun x -> structEqual a x) before then after <- tl
            else
                let bf = before
                let r = mt c p a binds (fun b -> fixedF c op rest (List.append (List.rev bf) tl) seg b k grp)
                if isTruthy r then
                    result <- r
                    fin <- true
                elif c.Exceeded then
                    result <- fls
                    fin <- true
                else
                    before <- a :: before
                    after <- tl
    result

and private trySkip (c: Ctx) (op: string) (p: MNode) (rest: MNode list) (before: LispValue list) (seg: string) binds (k: K) : LispValue =
    match p with
    | NV (n, _) when c.IdSkip && skippable c p op && not c.Exceeded ->
        bind n (build op []) binds (fun b -> fixedF c op rest (List.rev before) seg b k false)
    | _ -> fls

and private tryGroup (c: Ctx) (op: string) (p: MNode) (rest: MNode list) (before: LispValue list) (seg: string) binds (k: K) (grp: bool) : LispValue =
    match p with
    | NV (n, _) when (grp || (op = "+" && nodeOptional p)) && (match before with _ :: _ :: _ -> true | _ -> false) && rest.IsEmpty && isNull seg && not c.Exceeded ->
        bind n (build op (List.rev before)) binds
            (fun b ->
                let r = k b
                if isTruthy r then groupUsed <- true
                r)
    | _ -> fls

let private toLimit (v: LispValue) : double =
    match v with
    | LispInteger _ | LispRational _ | LispFloat _ -> toDouble v
    | _ -> failwith "ac-search-native: лимит — число"

let all : (string * LispValue) list = [
    builtin "ac-native-ok?" (fun args ->
        match args with
        | [ ip ] -> LispBool (match nodeOf ip with NBad -> false | _ -> true)
        | _ -> failwith "ac-native-ok?: (ac-native-ok? ip)")
    builtin "ac-native-group-used" (fun args ->
        match args with
        | [] -> LispBool groupUsed
        | _ -> failwith "ac-native-group-used: без аргументов")
    builtin "ac-search-native" (fun args ->
        match args with
        | [ ip; ne; LispVector ctx; onSol; idSkip ] ->
            let node = nodeOf ip
            if (match node with NBad -> true | _ -> false) then failwith "ac-search-native: образец с головой-переменной не поддерживается (ac-native-ok?)"
            let count = match ctx.[0] with LispInteger n -> int64 n | _ -> failwith "ac-search-native: ctx[0] — целое"
            let c = Ctx (count, toLimit ctx.[1], isTruthy ctx.[2], isTruthy ctx.[3], isTruthy ctx.[4], isTruthy idSkip,
                         (ctx.Length > 5 && isTruthy ctx.[5]))
            groupUsed <- false
            let k : K =
                fun binds ->
                    ctx.[0] <- LispInteger (System.Numerics.BigInteger c.Count)
                    ctx.[2] <- LispBool c.Exceeded
                    ListBuiltins.apply1 onSol (LispList [ for (n, v) in binds -> LispList [ LispSym n; v ] ])
            try
                mt c node ne [] k
            finally
                ctx.[0] <- LispInteger (System.Numerics.BigInteger c.Count)
                ctx.[2] <- LispBool c.Exceeded
        | _ -> failwith "ac-search-native: (ac-search-native ip ne ctx on-solution id-skip)")
]
