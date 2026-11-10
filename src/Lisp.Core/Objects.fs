// Шаг 14: ядро пользовательских типов — property list, иерархия типов, таблица методов
//
// Общий механизм (не заточен под тензоры): типы CAS (тензоры, множества) пишутся на Lisp
// поверх него. Модуль не зависит от Evaluator: вызов Lisp-функций идёт через applyHook,
// который Evaluator присваивает при создании окружения.
module Objects

open System.Collections.Generic
open Types

// --- Property list: символ → (ключ → значение) ---

let private plists = Dictionary<string, Dictionary<string, LispValue>>()

// (put 'sym 'key value)
let putProp (sym: string) (key: string) (value: LispValue) : unit =
    lock plists (fun () ->
        match plists.TryGetValue sym with
        | true, d -> d.[key] <- value
        | _ ->
            let d = Dictionary<string, LispValue>()
            d.[key] <- value
            plists.[sym] <- d)

// (get 'sym 'key) → Some значение | None
let getProp (sym: string) (key: string) : LispValue option =
    lock plists (fun () ->
        match plists.TryGetValue sym with
        | true, d ->
            match d.TryGetValue key with
            | true, v -> Some v
            | _ -> None
        | _ -> None)

// --- Иерархия типов: родитель хранится как свойство "parent" на имени типа ---

// Встроенная иерархия: integer→rational→real→number→scalar→any и т.д.
let private builtinHierarchy =
    [ "integer", "rational"; "rational", "real"; "real", "number"; "number", "scalar"; "scalar", "any"
      "algebraic", "real"; "float", "real"; "complex", "number"
      "symbol", "scalar"; "expr", "scalar"
      "list", "any"; "vector", "any"; "pair", "any"; "string", "any"; "bool", "any"
      "nil", "any"; "function", "any"; "macro", "any"
      // Шаг 15b: объект ошибки (try)
      "error", "any" ]

// Регистрируем при инициализации модуля (первое обращение к любому значению файла)
let private registered =
    for (t, p) in builtinHierarchy do putProp t "parent" (LispSym p)
    true

let private ensureInit () = if not registered then failwith "unreachable"

// Объявить тип с родителем: (deftype 'name 'parent)
let defType (name: string) (parent: string) : unit =
    ensureInit ()
    putProp name "parent" (LispSym parent)

// Цепочка предков: [t; родитель; ...; "any"] (защита от циклов)
let ancestors (t: string) : string list =
    ensureInit ()
    let seen = HashSet<string>()
    let rec go (cur: string) (acc: string list) =
        if not (seen.Add cur) then List.rev acc
        else
            let acc2 = cur :: acc
            if cur = "any" then List.rev acc2
            else
                match getProp cur "parent" with
                | Some (LispSym p) -> go p acc2
                | _ -> go "any" acc2   // пользовательский тип без родителя → any
    go t []

let isSubtype (t1: string) (t2: string) : bool = List.contains t2 (ancestors t1)

// Имя типа значения
let typeOf (v: LispValue) : string =
    match v with
    | LispInteger _ -> "integer"
    | LispRational _ -> "rational"
    | LispFloat _ -> "float"
    | LispComplex _ -> "complex"
    | LispAlgebraic _ -> "algebraic"
    | LispSym _ -> "symbol"
    | LispStr _ -> "string"
    | LispBool _ -> "bool"
    | LispNil | LispList [] -> "nil"
    | LispFunc _ | LispBuiltin _ -> "function"
    | LispMacro _ -> "macro"
    | LispVector _ -> "vector"
    | LispPair _ -> "pair"
    | LispObject o -> o.Type
    | LispList (LispSym _ :: _) -> "expr"
    | LispList _ -> "list"

// Нужна ли значению диспетчеризация по методам: объекты, векторы и алгебраические числа
// (Шаг 15a: арифметика алгебраических чисел — методы + * = < >, а не особый случай в Evaluator).
// Только для таких значений упрощатель и числовые builtins запускают диспетчеризацию
let needsDispatch (v: LispValue) : bool =
    match v with
    | LispObject _ | LispVector _ | LispAlgebraic _ -> true
    | _ -> false

// Коммутативен ли тип по умножению (свойство "commutative", ищется по предкам)
let isCommutativeType (t: string) : bool =
    ancestors t
    |> List.tryPick (fun a -> getProp a "commutative")
    |> function Some (LispBool true) -> true | _ -> false

// --- Таблица методов: ключ "op|t1|t2" → функция ---

let private methods = Dictionary<string, LispValue>()

let private methodKey (op: string) (types: string list) : string =
    op + "|" + String.concat "|" types

let addMethod (op: string) (types: string list) (fn: LispValue) : unit =
    lock methods (fun () -> methods.[methodKey op types] <- fn)

// Обход декартова произведения предков в порядке поиска (лексикографически: специфичность первого
// аргумента важнее, внутри — от точного типа к общему). probe вызывается для каждого полного ключа-сигнатуры;
// первый Some завершает поиск. Общий код для findMethod и dispatchTrace (explain-dispatch)
let private searchOrder (types: string list) (probe: string list -> LispValue option) : LispValue option =
    let anc = types |> List.map ancestors
    let rec go (chosen: string list) (rest: string list list) : LispValue option =
        match rest with
        | [] -> probe (List.rev chosen)
        | cands :: tail -> cands |> List.tryPick (fun c -> go (c :: chosen) tail)
    go [] anc

let private lookupMethod (op: string) (sigTypes: string list) : LispValue option =
    lock methods (fun () ->
        match methods.TryGetValue (methodKey op sigTypes) with
        | true, f -> Some f
        | _ -> None)

let findMethod (op: string) (types: string list) : LispValue option =
    searchOrder types (lookupMethod op)

// Шаг 15b: трасса поиска для explain-dispatch — перебранные сигнатуры по порядку (с признаком «найден»)
// и выбранный метод. Логика обхода — та же searchOrder, что у findMethod
let dispatchTrace (op: string) (types: string list) : (string list * bool) list * LispValue option =
    let tried = ResizeArray<string list * bool>()
    let found =
        searchOrder types (fun key ->
            let r = lookupMethod op key
            tried.Add((key, r.IsSome))
            r)
    (List.ofSeq tried, found)

// Шаг 15b: все зарегистрированные сигнатуры операции (отсортированы)
let private allMethodKeys () : (string * string list) list =
    lock methods (fun () ->
        methods.Keys
        |> Seq.map (fun k ->
            let parts = k.Split('|') |> List.ofArray
            (List.head parts, (match List.tail parts with [""] -> [] | t -> t)))
        |> Seq.sort
        |> List.ofSeq)

let methodSignatures (op: string) : string list list =
    allMethodKeys () |> List.filter (fun (o, _) -> o = op) |> List.map snd

// операции и сигнатуры, где встречается тип t
let methodsOfType (t: string) : (string * string list) list =
    allMethodKeys () |> List.filter (fun (_, sg) -> List.contains t sg)

// все свойства символа (для describe), отсортированы по ключу
let propsOf (sym: string) : (string * LispValue) list =
    lock plists (fun () ->
        match plists.TryGetValue sym with
        | true, d -> d |> Seq.map (fun kv -> (kv.Key, kv.Value)) |> Seq.sortBy fst |> List.ofSeq
        | _ -> [])

// Вызов Lisp-функций из модулей, компилируемых до Evaluator (присваивает Evaluator)
let mutable applyHook : LispValue -> LispValue list -> LispValue =
    fun _ _ -> failwith "applyHook не инициализирован"

// Диспетчеризация по типам dispatchArgs, вызов метода со ВСЕМИ аргументами allArgs
let tryDispatch (op: string) (dispatchArgs: LispValue list) (allArgs: LispValue list) : LispValue option =
    match findMethod op (dispatchArgs |> List.map typeOf) with
    | Some fn -> Some (applyHook fn allArgs)
    | None -> None
