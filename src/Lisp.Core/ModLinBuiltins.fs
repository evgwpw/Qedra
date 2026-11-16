// Шаг PERF.F1: инкрементальный треугольный базис линейной системы по модулю простого P (P < 2^31, произведения в int64).
// Используется анзацем (lib/integrate/ansatz.lisp: строки системы — точки, неизвестные — коэффициенты). Lisp-эталон —
// an-inc-add! / an-inc-solve в ansatz.lisp (те же результаты).
//   (modbasis-new nu P)     → хендл базиса (nu неизвестных, модуль P)
//   (modbasis-add! h row)   → 'indep (ранг вырос) | 'dep (строка выражается через базис) | 'bad (0 = c ≠ 0, несовместна);
//                             row — список или вектор nu + 1 целых (последний — правая часть), любые целые (приводятся по модулю P)
//   (modbasis-solve h)      → список nu значений по модулю P (свободные неизвестные — 0)
//   (modbasis-rank h)       → ранг
// Хендл — вектор из одного элемента; состояние держится в ConditionalWeakTable (освобождается сборщиком).
module ModLinBuiltins

open System
open System.Numerics
open System.Runtime.CompilerServices
open Types
open Builtins

/// Базис: pivots.[c] — нормированная ведущая строка со столбцом c (первый ненулевой элемент 1) или null
type ModBasis(nu: int, p: int64) =
    let pivots : int64[][] = Array.zeroCreate nu
    let mutable rank = 0
    member _.Nu = nu
    member _.P = p
    member _.Rank = rank

    static member ModInv (a: int64, p: int64) : int64 =
        let mutable r0 = p
        let mutable r1 = ((a % p) + p) % p
        let mutable s0 = 0L
        let mutable s1 = 1L
        while r1 <> 0L do
            let q = r0 / r1
            let r2 = r0 - q * r1
            r0 <- r1
            r1 <- r2
            let s2 = s0 - q * s1
            s0 <- s1
            s1 <- s2
        ((s0 % p) + p) % p

    /// rv — длина nu + 1, значения в [0, P); массив меняется на месте (и может стать ведущей строкой)
    member _.Add (rv: int64[]) : string =
        let mutable c = 0
        let mutable result : string = null
        while isNull result do
            if c = nu then result <- (if rv.[nu] = 0L then "dep" else "bad")
            elif rv.[c] = 0L then c <- c + 1
            else
                let pr = pivots.[c]
                if not (isNull pr) then
                    let f = rv.[c]
                    for j in c .. nu do
                        let v = (rv.[j] - f * pr.[j]) % p
                        rv.[j] <- (if v < 0L then v + p else v)
                    c <- c + 1
                else
                    let inv = ModBasis.ModInv (rv.[c], p)
                    for j in c .. nu do
                        rv.[j] <- (rv.[j] * inv) % p
                    pivots.[c] <- rv
                    rank <- rank + 1
                    result <- "indep"
        result

    member _.Solve () : int64[] =
        let sol : int64[] = Array.zeroCreate nu
        for c in nu - 1 .. -1 .. 0 do
            let pr = pivots.[c]
            if not (isNull pr) then
                let mutable acc = pr.[nu]
                for j in c + 1 .. nu - 1 do
                    if sol.[j] <> 0L then
                        let v = (acc - pr.[j] * sol.[j]) % p
                        acc <- (if v < 0L then v + p else v)
                sol.[c] <- acc
        sol

let private table = ConditionalWeakTable<LispValue[], ModBasis>()

let private basisOf (who: string) (v: LispValue) : ModBasis =
    match v with
    | LispVector arr ->
        (match table.TryGetValue arr with
         | true, b -> b
         | _ -> failwithf "%s: не базис (modbasis-new)" who)
    | _ -> failwithf "%s: не базис (modbasis-new)" who

let private toInt64 (who: string) (p: int64) (v: LispValue) : int64 =
    match v with
    | LispInteger n ->
        let r = BigInteger.Remainder (n, BigInteger p)
        let x = int64 r
        if x < 0L then x + p else x
    | other -> failwithf "%s: ожидается целое, получено %s" who (Printer.prettyPrint other)

let all : (string * LispValue) list = [
    builtin "modbasis-new" (fun args ->
        match args with
        | [LispInteger nu; LispInteger p] when nu.Sign >= 0 && p > 1I && p < BigInteger 2147483648L ->
            let arr = [| LispInteger nu |]
            table.Add (arr, ModBasis (int nu, int64 p))
            LispVector arr
        | _ -> failwith "modbasis-new: (modbasis-new nu P), P — простое < 2^31")
    builtin "modbasis-add!" (fun args ->
        match args with
        | [h; row] ->
            let b = basisOf "modbasis-add!" h
            let items =
                match row with
                | LispList xs -> Array.ofList xs
                | LispNil -> [||]
                | LispVector a -> a
                | _ -> failwith "modbasis-add!: строка — список или вектор"
            if items.Length <> b.Nu + 1 then failwithf "modbasis-add!: длина строки %d, ожидалось %d" items.Length (b.Nu + 1)
            let rv = items |> Array.map (toInt64 "modbasis-add!" b.P)
            LispSym (b.Add rv)
        | _ -> failwith "modbasis-add!: (modbasis-add! базис строка)")
    builtin "modbasis-solve" (fun args ->
        match args with
        | [h] -> LispList [ for x in (basisOf "modbasis-solve" h).Solve () -> LispInteger (BigInteger x) ]
        | _ -> failwith "modbasis-solve: (modbasis-solve базис)")
    builtin "modbasis-rank" (fun args ->
        match args with
        | [h] -> LispInteger (BigInteger (basisOf "modbasis-rank" h).Rank)
        | _ -> failwith "modbasis-rank: (modbasis-rank базис)")
]
