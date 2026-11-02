// Мост «выражение Lisp ↔ многочлен» (шаг 21h'; вынесено из MPoly.fs): контекст переменных (ядра выражения),
// выражение → рациональная функция / многочлен, многочлен → каноническое выражение.
// Это единственное место, где многочлены (Cas.Algebra) встречаются с Lisp-выражениями (Lisp.Core).
module PolyExpr

open System.Numerics
open Types
open Numeric
open MPoly
open PolyGcd

type Ctx = { Vars: LispValue[] }

let private maxPowSimple = 100000
let private maxPowCompound = 256

// Может ли (^ b n) (n целое) быть разобрано как степень многочлена; иначе — ядро
let private powOk (b: LispValue) (n: BigInteger) : bool =
    let k = BigInteger.Abs n
    let simple = match b with LispSym _ -> true | _ -> false
    k <= BigInteger (if simple then maxPowSimple else maxPowCompound)
    && not (n.Sign < 0 && (match b with LispInteger z -> z.IsZero | _ -> false))

// Шаг 21c: упрощатель сливает (exp u)^n в exp(n·u); для многочленов обратно: exp(n·u), n целое ≠ 1,
// — это n-я степень ядра exp(u) (иначе e^(2x) - 1 не раскладывалось бы как (e^x - 1)(e^x + 1))
let private expPower (e: LispValue) : (LispValue * BigInteger) option =
    match e with
    | LispList [LispSym "exp"; LispList (LispSym "*" :: LispInteger n :: rest)]
        when not n.IsOne && not rest.IsEmpty && BigInteger.Abs n <= 256I ->
        let u = match rest with [r] -> r | _ -> LispList (LispSym "*" :: rest)
        Some (LispList [LispSym "exp"; u], n)
    | _ -> None

// Сбор ядер упрощённого выражения (структурно различные, в порядке появления)
let rec private collect (acc: ResizeArray<LispValue>) (e: LispValue) : unit =
    match e with
    | LispInteger _ | LispRational _ -> ()
    | LispList [LispSym "exp"; _] when (expPower e).IsSome -> collect acc (fst (expPower e).Value)
    | LispList (LispSym "+" :: args) | LispList (LispSym "*" :: args) -> for a in args do collect acc a
    | LispList [LispSym "^"; b; LispInteger n] when powOk b n -> collect acc b
    | _ -> if not (acc.Exists (fun k -> structEqual k e)) then acc.Add e

// Ядра выражения (после simplify)
let kernelsOf (e: LispValue) : LispValue list =
    let acc = ResizeArray<LispValue>()
    collect acc (Simplify.simplify e)
    List.ofSeq acc

// Контекст: ядра всех выражений, отсортированные по orderCompare (первое — главная); mainLast — переменные,
// которые должны получить наибольшие номера (главные), в указанном порядке
let makeCtx (es: LispValue list) (mainLast: LispValue list) : Ctx =
    let acc = ResizeArray<LispValue>()
    for e in es do collect acc (Simplify.simplify e)
    let mains = mainLast |> List.map Simplify.simplify
    let rest = acc |> Seq.filter (fun k -> not (mains |> List.exists (structEqual k))) |> List.ofSeq
    // по убыванию порядка: алфавитно ПЕРВОЕ ядро получает наибольший номер (главная переменная),
    // поэтому знак множителей при разложении «естественный»: (x - y)(x + y), а не (y - x)(y + x)
    let sorted = rest |> List.sortWith (fun a b -> Order.orderCompare b a)
    { Vars = Array.ofList (sorted @ mains) }

let varIndex (ctx: Ctx) (k: LispValue) : int =
    match ctx.Vars |> Array.tryFindIndex (structEqual k) with
    | Some i -> i
    | None -> failwith "MPoly: ядро отсутствует в контексте"

// Упрощённое выражение → пара (числитель, знаменатель), без сокращения
let rec private ratFunRaw (ctx: Ctx) (e: LispValue) : MPoly * MPoly =
    match e with
    | LispInteger n -> (ofInt n, one)
    | LispRational (p, q) -> (Const (p, q), one)
    | LispList (LispSym "+" :: args) ->
        args |> List.fold (fun acc a -> fracAdd acc (ratFunRaw ctx a)) (zero, one)
    | LispList (LispSym "*" :: args) ->
        args |> List.fold (fun acc a -> fracMul acc (ratFunRaw ctx a)) (one, one)
    | LispList [LispSym "^"; b; LispInteger n] when powOk b n ->
        let (nb, db) = ratFunRaw ctx b
        let k = int (BigInteger.Abs n)
        if n.Sign >= 0 then (pow nb k, pow db k)
        elif isZero nb then failwith "Деление на ноль"
        else (pow db k, pow nb k)
    | LispList [LispSym "exp"; _] when (expPower e).IsSome ->
        let (b, n) = (expPower e).Value
        ratFunRaw ctx (LispList [LispSym "^"; b; LispInteger n])
    | _ -> (var (varIndex ctx e), one)

// Выражение → рациональная функция (числитель, знаменатель), сокращённая, знаменатель нормирован
let toRatFun (ctx: Ctx) (e: LispValue) : MPoly * MPoly =
    normalizeFrac (ratFunRaw ctx (Simplify.simplify e))

// Выражение → многочлен; None, если в знаменателе остаётся переменная
let toPoly (ctx: Ctx) (e: LispValue) : MPoly option =
    let (n, d) = toRatFun ctx e
    if isOne d then Some n else None

// Многочлен → каноническое выражение (неподвижная точка simplify)
let toExpr (ctx: Ctx) (p: MPoly) : LispValue =
    let termExpr ((c, ms): Q * (int * int) list) : LispValue =
        let facs =
            ms |> List.rev |> List.map (fun (v, k) ->
                if k = 1 then ctx.Vars.[v] else LispList [LispSym "^"; ctx.Vars.[v]; LispInteger (BigInteger k)])
        let cf = if ratCompare c (1I, 1I) = 0 && not facs.IsEmpty then [] else [ratToValue c]
        match cf @ facs with
        | [single] -> single
        | items -> LispList (LispSym "*" :: items)
    match monomials p with
    | [] -> LispInteger 0I
    | ts -> Simplify.simplify (LispList (LispSym "+" :: List.map termExpr ts))

// Рациональная функция → каноническое выражение num * den^-1
let ratFunToExpr (ctx: Ctx) ((n, d): MPoly * MPoly) : LispValue =
    if isOne d then toExpr ctx n
    else Simplify.simplify (LispList [LispSym "*"; toExpr ctx n; LispList [LispSym "^"; toExpr ctx d; LispInteger -1I]])
