// Шаг 21i' (e): списочные функции высшего порядка на F# — map, map2, filter, foldl, reverse, any?, every?.
// Раньше жили в lib\prelude.lisp (хвостовая рекурсия через накопитель: ≈ 110–140 нс на элемент за проход, map ≈ 300 нс на
// элемент). Здесь цикл на F#, а лямбда применяется без построения списка аргументов: apply1/apply2 заполняют слоты
// нового фрейма напрямую (как CallNode.CallFast) и кладут кадр стека pushArr. Остальное (макросы, &rest, неверная арность,
// ещё не скомпилированная функция, trace/profile — Debug.hooked) идёт прежним общим путём Compiler.applyT.
// Для builtin-аргумента (например, `(map car l)`) берётся быстрый вход из реестра FastBuiltins (один раз на вызов map).
// Глубина системного стека не растёт с длиной списка (цикл, не рекурсия); кадры map-acc из стека ошибок исчезли —
// кадр самого builtin (map) и кадр лямбды с её позицией остаются.
module ListBuiltins

open Types
open Builtins
open Compiler

let inline private isNull' (v: LispValue) : bool = obj.ReferenceEquals(v, null)

// Тело скомпилированной функции с кадром стека; frame уже заполнен аргументами (n штук)
let inline private runFrame (code: LambdaCode) (slots: Scope) (n: int) : LispValue =
    let entry = Debug.depth
    Debug.pushArr slots n 0
    Debug.checkStack ()
    let r = runBody code slots
    Debug.depth <- entry
    r

// Функция одного аргумента: замыкание, выбранное один раз по виду f
let makeApply1 (f: LispValue) : LispValue -> LispValue =
    match f with
    | LispFunc u ->
        let code = u.Code
        fun x ->
            if code.Fast && code.NParams = 1 && not Debug.hooked then
                let slots = newFrame code f
                setSlot slots 0 x
                runFrame code slots 1
            else applyT f [ x ]
    | LispBuiltin (Builtin b) ->
        match FastBuiltins.table.TryGetValue (box b) with
        | true, e when not (isNull e.F1) ->
            let f1 = e.F1
            fun x ->
                if Debug.hooked then applyT f [ x ]
                else
                    let r = f1.Invoke x
                    if isNull' r then applyT f [ x ] else r
        | _ -> fun x -> applyT f [ x ]
    | _ -> fun x -> applyT f [ x ]

// Функция двух аргументов
let makeApply2 (f: LispValue) : LispValue -> LispValue -> LispValue =
    match f with
    | LispFunc u ->
        let code = u.Code
        fun x y ->
            if code.Fast && code.NParams = 2 && not Debug.hooked then
                let slots = newFrame code f
                setSlot slots 0 x
                setSlot slots 1 y
                runFrame code slots 2
            else applyT f [ x; y ]
    | LispBuiltin (Builtin b) ->
        match FastBuiltins.table.TryGetValue (box b) with
        | true, e when not (isNull e.F2) ->
            let f2 = e.F2
            fun x y ->
                if Debug.hooked then applyT f [ x; y ]
                else
                    let r = f2.Invoke(x, y)
                    if isNull' r then applyT f [ x; y ] else r
        | _ -> fun x y -> applyT f [ x; y ]
    | _ -> fun x y -> applyT f [ x; y ]

let apply1 (f: LispValue) (x: LispValue) : LispValue = makeApply1 f x
let apply2 (f: LispValue) (x: LispValue) (y: LispValue) : LispValue = makeApply2 f x y

// Элементы списка (nil — пусто)
let private items (who: string) (v: LispValue) : LispValue list =
    match v with
    | LispList xs -> xs
    | LispNil -> []
    | other -> failwithf "%s: ожидается список, получено %s" who (Printer.prettyPrint other)

// Список из элементов в обратном порядке накопления; пустой — LispList [] (как литерал '())
let private ofRevAcc (acc: LispValue list) : LispValue = LispList (List.rev acc)

let private bReverse (args: LispValue list) : LispValue =
    match args with
    | [ l ] -> LispList (List.rev (items "reverse" l))
    | _ -> failwith "reverse: требуется один аргумент — список"

let private bMap (args: LispValue list) : LispValue =
    match args with
    | [ f; l ] ->
        let call = makeApply1 f
        let mutable rest = items "map" l
        let mutable acc = []
        while not rest.IsEmpty do
            acc <- call rest.Head :: acc
            rest <- rest.Tail
        ofRevAcc acc
    | _ -> failwith "map: требуются функция и список"

let private bMap2 (args: LispValue list) : LispValue =
    match args with
    | [ f; a; b ] ->
        let call = makeApply2 f
        let mutable ra = items "map2" a
        let mutable rb = if ra.IsEmpty then [] else items "map2" b
        let mutable acc = []
        while not ra.IsEmpty && not rb.IsEmpty do
            acc <- call ra.Head rb.Head :: acc
            ra <- ra.Tail
            rb <- rb.Tail
        ofRevAcc acc
    | _ -> failwith "map2: требуются функция и два списка"

let private bFilter (args: LispValue list) : LispValue =
    match args with
    | [ p; l ] ->
        let call = makeApply1 p
        let mutable rest = items "filter" l
        let mutable acc = []
        while not rest.IsEmpty do
            let x = rest.Head
            if isTruthy (call x) then acc <- x :: acc
            rest <- rest.Tail
        ofRevAcc acc
    | _ -> failwith "filter: требуются предикат и список"

let private bFoldl (args: LispValue list) : LispValue =
    match args with
    | [ f; init; l ] ->
        let call = makeApply2 f
        let mutable rest = items "foldl" l
        let mutable acc = init
        while not rest.IsEmpty do
            acc <- call acc rest.Head
            rest <- rest.Tail
        acc
    | _ -> failwith "foldl: требуются функция, начальное значение и список"

let private bAny (args: LispValue list) : LispValue =
    match args with
    | [ p; l ] ->
        let call = makeApply1 p
        let mutable rest = items "any?" l
        let mutable found = false
        while not found && not rest.IsEmpty do
            if isTruthy (call rest.Head) then found <- true
            rest <- rest.Tail
        LispBool found
    | _ -> failwith "any?: требуются предикат и список"

let private bEvery (args: LispValue list) : LispValue =
    match args with
    | [ p; l ] ->
        let call = makeApply1 p
        let mutable rest = items "every?" l
        let mutable ok = true
        while ok && not rest.IsEmpty do
            if not (isTruthy (call rest.Head)) then ok <- false
            rest <- rest.Tail
        LispBool ok
    | _ -> failwith "every?: требуются предикат и список"

let all : (string * LispValue) list =
    [ builtin "reverse" bReverse
      builtin "map" bMap
      builtin "map2" bMap2
      builtin "filter" bFilter
      builtin "foldl" bFoldl
      builtin "any?" bAny
      builtin "every?" bEvery ]
