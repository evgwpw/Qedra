// Раскрытие скобок (expand) — вынесено из Simplify.fs (Шаг 15a)
module Expand

open Types
open Simplify

// Флаттим вложенные суммы: (+ (+ a b) c) → (+ a b c)
let private flattenSum (expr: LispValue) : LispValue =
    let rec collect (e: LispValue) : LispValue list =
        match e with
        | LispList (LispSym "+" :: args) -> args |> List.collect collect
        | other -> [other]
    match collect expr with
    | [] -> LispInteger 0I
    | [single] -> single
    | items -> LispList (LispSym "+" :: items)

// Раскрываем умножение суммы рекурсивно (и целую положительную степень суммы),
// затем упрощаем результат. Вход предварительно приводится к канонической форме
let expand (expr: LispValue) : LispValue =
    let rec expandOnce (e: LispValue) : LispValue =
        match e with
        | LispList (LispSym "*" :: args) ->
            let expandedArgs = List.map expandOnce args
            expandProduct expandedArgs
        // (^ (+ a b) n), целое 2 <= n <= 64 → повторное умножение на сумму;
        // после каждого шага expandProduct упрощает (собирает подобные), поэтому
        // размер промежуточной суммы ограничен числом различных мономов, а не 2^n
        | LispList [LispSym "^"; (LispList (LispSym "+" :: _) as s); LispInteger n] when n >= 2I && n <= 64I ->
            let s' = expandOnce s
            let mutable acc = s'
            for _ in 2 .. int n do
                acc <- expandProduct [acc; s']
            acc
        | LispList items -> LispList (List.map expandOnce items)
        | _ -> e
    and expandProduct (args: LispValue list) : LispValue =
        match args with
        | [] -> LispInteger 1I
        | [single] -> single
        | _ ->
            let sumIndex = args |> List.tryFindIndex (fun a ->
                match a with LispList (LispSym "+" :: _) -> true | _ -> false)
            match sumIndex with
            | None -> LispList (LispSym "*" :: args)
            | Some i ->
                let sum = args.[i]
                let others = args |> List.indexed |> List.filter (fun (j, _) -> j <> i) |> List.map snd
                match sum with
                | LispList (LispSym "+" :: terms) ->
                    let distributed =
                        terms |> List.map (fun t ->
                            expandProduct (others @ [t]) |> flattenSum)
                    // Объединяем все члены в одну плоскую сумму
                    let allTerms = distributed |> List.collect (fun d ->
                        match d with
                        | LispList (LispSym "+" :: items) -> items
                        | other -> [other])
                    LispList (LispSym "+" :: allTerms) |> simplify
                | _ -> LispList (LispSym "*" :: args)
    expandOnce (simplify expr) |> simplify
