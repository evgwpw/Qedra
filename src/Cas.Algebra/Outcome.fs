// Единый контракт алгоритмов (шаг 21h'): исход алгоритма — ответ / «не знаю» (с причиной) / «доказано, что ответа нет» (с причиной).
// Раньше «отказ» алгоритма был None или исключением, а «не умею» и «доказано, что нет» не различались (например, невычисленная
// форма интеграла: интегратор не справился — или интеграл доказуемо неэлементарен). Здесь только каркас; осмысленные причины
// и использование — шаг S (пошаговые решения) и алгоритмы Риша / Грёбнера.
module Outcome

type Outcome<'a> =
    /// найден ответ
    | Answer of 'a
    /// алгоритм не смог получить ответ (исчерпаны ресурсы, метод не применим): с причиной; другой путь может справиться
    | Unknown of reason: string
    /// доказано, что ответа нет (например, интеграл не выражается в элементарных функциях): с причиной (доказательством)
    | NoSolution of reason: string

let isAnswer (o: Outcome<'a>) : bool = match o with Answer _ -> true | _ -> false

// Ответ, если он есть (для старого кода с option: причина теряется)
let toOption (o: Outcome<'a>) : 'a option = match o with Answer a -> Some a | _ -> None

// option → исход: None — «не знаю» с заданной причиной
let ofOption (reason: string) (o: 'a option) : Outcome<'a> =
    match o with
    | Some a -> Answer a
    | None -> Unknown reason

let map (f: 'a -> 'b) (o: Outcome<'a>) : Outcome<'b> =
    match o with
    | Answer a -> Answer (f a)
    | Unknown r -> Unknown r
    | NoSolution r -> NoSolution r

// Цепочка: следующий шаг выполняется, только если есть ответ; «не знаю» и «доказано, что нет» проходят дальше без изменений
let bind (f: 'a -> Outcome<'b>) (o: Outcome<'a>) : Outcome<'b> =
    match o with
    | Answer a -> f a
    | Unknown r -> Unknown r
    | NoSolution r -> NoSolution r

// Первый исход с ответом (ленивые альтернативы); если ответа нет, «доказано, что нет» важнее «не знаю»,
// иначе — «не знаю» с причинами всех попыток
let firstAnswer (alternatives: (unit -> Outcome<'a>) list) : Outcome<'a> =
    let rec go (alts: (unit -> Outcome<'a>) list) (reasons: string list) =
        match alts with
        | [] -> Unknown (String.concat "; " (List.rev reasons))
        | alt :: rest ->
            match alt () with
            | Answer a -> Answer a
            | NoSolution r -> NoSolution r
            | Unknown r -> go rest (r :: reasons)
    go alternatives []

// Читаемое описание исхода (для сообщений и журнала)
let describe (describeAnswer: 'a -> string) (o: Outcome<'a>) : string =
    match o with
    | Answer a -> "ответ: " + describeAnswer a
    | Unknown r -> "не знаю: " + r
    | NoSolution r -> "доказано, что решения нет: " + r

// Ответ или исключение с описанием причины (для мест, где «не знаю» — ошибка)
let getOrFail (what: string) (o: Outcome<'a>) : 'a =
    match o with
    | Answer a -> a
    | Unknown r -> failwithf "%s: не знаю (%s)" what r
    | NoSolution r -> failwithf "%s: доказано, что решения нет (%s)" what r
