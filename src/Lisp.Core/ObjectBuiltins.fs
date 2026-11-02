// Шаг 14: встроенные функции для объектов, векторов, property list и таблицы методов.
// Компилируется до Evaluator (не требует eval): спецформа defmethod живёт в Evaluator.
module ObjectBuiltins

open System.Numerics
open Types
open Builtins

let private symName (who: string) (v: LispValue) : string =
    match v with
    | LispSym s -> s
    | other -> failwithf "%s: ожидается символ, получено %s" who (Printer.prettyPrint other)

let private index (who: string) (len: int) (v: LispValue) : int =
    match v with
    | LispInteger n when n.Sign >= 0 && BigInteger.Compare(n, BigInteger len) < 0 -> int n
    | LispInteger n -> failwithf "%s: индекс %A вне границ [0, %d)" who n len
    | other -> failwithf "%s: индекс должен быть целым, получено %s" who (Printer.prettyPrint other)

let private listOf (who: string) (v: LispValue) : LispValue list =
    match v with
    | LispList xs -> xs
    | LispNil -> []
    | other -> failwithf "%s: ожидается список, получено %s" who (Printer.prettyPrint other)

let objectBuiltins : (string * LispValue) list = [
    // --- Объекты ---
    builtin "make-object" (fun args ->
        match args with
        | t :: fields -> LispObject { Type = symName "make-object" t; Fields = Array.ofList fields }
        | [] -> failwith "make-object: требуется тип")
    builtin "object?" (fun args ->
        match args with
        | [LispObject _] -> LispBool true
        | [_] -> LispBool false
        | _ -> failwith "object?: один аргумент")
    // Шаг 19: (try-method 'op (аргументы-диспетчеризации...) (все-аргументы...)) — вызвать метод op, выбранный по
    // значениям первого списка (с иерархией типов), со всеми аргументами второго; результат — список (значение)
    // или #f, если метода нет. Так Lisp-функции (integrate) диспетчеризуют по объектам, как F#-diff
    // (имя dispatch-method занято set.lisp — другая функция, возвращает метод по списку типов)
    builtin "try-method" (fun args ->
        match args with
        | [op; LispList dispatchArgs; LispList allArgs] ->
            match Objects.tryDispatch (symName "try-method" op) dispatchArgs allArgs with
            | Some r -> LispList [r]
            | None -> LispBool false
        | _ -> failwith "try-method: ожидаются операция, список аргументов диспетчеризации и список всех аргументов")
    builtin "object-type" (fun args ->
        match args with
        | [LispObject o] -> LispSym o.Type
        | [v] -> Printer.expectError "object-type" 1 "ожидался объект" v
        | _ -> failwith "object-type: один аргумент")
    builtin "object-ref" (fun args ->
        match args with
        | [LispObject o; i] -> o.Fields.[index "object-ref" o.Fields.Length i]
        | _ -> failwith "object-ref: ожидаются объект и индекс")
    builtin "object-fields" (fun args ->
        match args with
        | [LispObject o] -> LispVector (Array.copy o.Fields)
        | [v] -> Printer.expectError "object-fields" 1 "ожидался объект" v
        | _ -> failwith "object-fields: один аргумент")
    builtin "object-count" (fun args ->
        match args with
        | [LispObject o] -> LispInteger (bigint o.Fields.Length)
        | [v] -> Printer.expectError "object-count" 1 "ожидался объект" v
        | _ -> failwith "object-count: один аргумент")

    // --- Векторы ---
    builtin "vector" (fun args -> LispVector (Array.ofList args))
    builtin "make-vector" (fun args ->
        match args with
        | [LispInteger n; init] when n.Sign >= 0 -> LispVector (Array.create (int n) init)
        | [LispInteger n] when n.Sign >= 0 -> LispVector (Array.create (int n) LispNil)
        | _ -> failwith "make-vector: ожидаются неотрицательная длина и начальное значение")
    builtin "vector?" (fun args ->
        match args with
        | [LispVector _] -> LispBool true
        | [_] -> LispBool false
        | _ -> failwith "vector?: один аргумент")
    builtin "vref" (fun args ->
        match args with
        | [LispVector v; i] -> v.[index "vref" v.Length i]
        | _ -> failwith "vref: ожидаются вектор и индекс")
    builtin "vset!" (fun args ->
        match args with
        | [LispVector v; i; x] ->
            v.[index "vset!" v.Length i] <- x
            x
        | _ -> failwith "vset!: ожидаются вектор, индекс и значение")
    builtin "vlength" (fun args ->
        match args with
        | [LispVector v] -> LispInteger (bigint v.Length)
        | [v] -> Printer.expectError "vlength" 1 "ожидался вектор" v
        | _ -> failwith "vlength: один аргумент")
    builtin "vector->list" (fun args ->
        match args with
        | [LispVector v] -> (if v.Length = 0 then LispNil else LispList (List.ofArray v))
        | [v] -> Printer.expectError "vector->list" 1 "ожидался вектор" v
        | _ -> failwith "vector->list: один аргумент")
    builtin "list->vector" (fun args ->
        match args with
        | [l] -> LispVector (Array.ofList (listOf "list->vector" l))
        | [v] -> Printer.expectError "list->vector" 1 "ожидался список" v
        | _ -> failwith "list->vector: один аргумент")

    // --- Property list ---
    builtin "put" (fun args ->
        match args with
        | [s; k; v] -> Objects.putProp (symName "put" s) (symName "put" k) v; v
        | _ -> failwith "put: ожидаются символ, ключ и значение")
    builtin "get" (fun args ->
        match args with
        | [s; k] -> Objects.getProp (symName "get" s) (symName "get" k) |> Option.defaultValue LispNil
        | _ -> failwith "get: ожидаются символ и ключ")

    // Подшаг 22.4: таблица деклараций доменов ТЕКУЩЕЙ сессии (ActiveSession.Env; lib\domain.lisp) — алист ((x D ...) ...).
    // Plist символов общий для процесса, поэтому декларации в нём протекали между сессиями AgentApi/MCP
    builtin "decl-table" (fun args ->
        match args with
        | [] -> (match ActiveSession.Env with null -> LispList [] | e -> e.Decls)
        | _ -> failwith "decl-table: аргументов нет")
    builtin "decl-table-set!" (fun args ->
        match args with
        | [ (LispList _ | LispNil) as t ] ->
            (match ActiveSession.Env with null -> () | e -> e.Decls <- t)
            t
        | _ -> failwith "decl-table-set!: ожидается список")

    // (to-string x) — строка как есть, остальное — текст prettyPrint (для методов print)
    builtin "to-string" (fun args ->
        match args with
        | [LispStr s] -> LispStr s
        | [x] -> LispStr (Printer.prettyPrint x)
        | _ -> failwith "to-string: один аргумент")

    // --- Типы ---
    builtin "type-of" (fun args ->
        match args with
        | [x] -> LispSym (Objects.typeOf x)
        | _ -> failwith "type-of: один аргумент")
    builtin "deftype" (fun args ->
        match args with
        | [n; p] -> Objects.defType (symName "deftype" n) (symName "deftype" p); n
        | [n] -> Objects.defType (symName "deftype" n) "any"; n
        | _ -> failwith "deftype: ожидаются имя типа и родитель")
    builtin "subtype?" (fun args ->
        match args with
        | [a; b] -> LispBool (Objects.isSubtype (symName "subtype?" a) (symName "subtype?" b))
        | _ -> failwith "subtype?: два аргумента")
    builtin "ancestors" (fun args ->
        match args with
        | [t] -> LispList (Objects.ancestors (symName "ancestors" t) |> List.map LispSym)
        | _ -> failwith "ancestors: один аргумент")

    // --- Методы ---
    builtin "add-method" (fun args ->
        match args with
        | [op; types; fn] ->
            let ts = listOf "add-method" types |> List.map (symName "add-method")
            // Шаг 15b: безымянная лямбда получает имя метода "op(t1 t2)" (для стека и trace)
            let named =
                match fn with
                | LispFunc u when u.Name = "lambda" ->
                    LispFunc { u with Name = symName "add-method" op + "(" + String.concat " " ts + ")" }
                | other -> other
            Objects.addMethod (symName "add-method" op) ts named
            op
        | _ -> failwith "add-method: ожидаются операция, список типов и функция")
    builtin "find-method" (fun args ->
        match args with
        | [op; types] ->
            let ts = listOf "find-method" types |> List.map (symName "find-method")
            Objects.findMethod (symName "find-method" op) ts |> Option.defaultValue LispNil
        | _ -> failwith "find-method: ожидаются операция и список типов")
]
