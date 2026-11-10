// Шаг 15b: builtins отладки — ошибки как значения, trace, интроспекция диспетчеризации и describe.
// Компилируется до Evaluator; describe получает поиск в окружении параметром (см. Evaluator.newEnv).
module DebugBuiltins

open Types
open Builtins

let private symName (who: string) (v: LispValue) : string =
    match v with
    | LispSym s -> s
    | other -> failwithf "%s: ожидается символ, получено %s" who (Printer.prettyPrint other)

// Имя для trace: символ или строка (имя метода "op(t1 t2)" символом не записать)
let private traceName (who: string) (v: LispValue) : string =
    match v with
    | LispStr s -> s
    | other -> symName who other

let private say (s: string) = Debug.out().WriteLine s

let private sigText (op: string) (types: string list) = op + "(" + String.concat " " types + ")"

// Строки поля стека объекта ошибки
let private errorStackLines (e: LispValue) : string list =
    match e with
    | LispObject { Type = "error"; Fields = [| _; LispList lines; _ |] } ->
        lines |> List.map (function LispStr s -> s | other -> Printer.prettyPrint other)
    | _ -> []

// (explain-dispatch 'op a b ...) — подробный отчёт о выборе метода; возвращает метод или nil
let private explainDispatch (args: LispValue list) : LispValue =
    match args with
    | op :: vals ->
        let opName = symName "explain-dispatch" op
        let types = vals |> List.map Objects.typeOf
        say ("диспетчеризация " + opName + ": типы аргументов (" + String.concat " " types + ")")
        for t in types do
            say ("  предки " + t + ": " + String.concat " -> " (Objects.ancestors t))
        let tried, found = Objects.dispatchTrace opName types
        say "  порядок поиска:"
        for (key, ok) in tried do
            say ("    " + sigText opName key + (if ok then " — найден" else " — нет"))
        match found with
        | Some fn ->
            say ("  выбран: " + Printer.prettyPrint fn)
            fn
        | None ->
            say "  метод не найден"
            LispNil
    | [] -> failwith "explain-dispatch: требуется операция"

// (describe x) — значение, тип, предки; для объекта — поля, для символа — значение, plist, методы типа
let describe (lookup: string -> LispValue option) (x: LispValue) : LispValue =
    let t = Objects.typeOf x
    say ("значение: " + Printer.prettyPrint x)
    say ("тип: " + t)
    say ("предки: " + String.concat " -> " (Objects.ancestors t))
    // Шаг 21d: где определена функция/макрос (если форма определения читалась из файла/REPL/JSON)
    let sayWhere (v: LispValue) =
        match v with
        | LispFunc u | LispMacro u when not (isNull u.Code) && not (isNull u.Code.Pos) ->
            say ("определена: " + u.Code.Pos.ToString())
        | _ -> ()
    sayWhere x
    match x with
    | LispObject o ->
        o.Fields |> Array.iteri (fun i f -> say (sprintf "  поле %d: %s" i (Printer.prettyPrint f)))
    | LispSym name ->
        match lookup name with
        | Some v ->
            say ("в окружении: " + Printer.prettyPrint v)
            sayWhere v
        | None -> say "в окружении: не связан"
        for (k, v) in Objects.propsOf name do
            say (sprintf "  свойство %s: %s" k (Printer.prettyPrint v))
        // символ — имя типа: его методы
        let ms = Objects.methodsOfType name
        if not ms.IsEmpty then
            say "методы типа:"
            for (op, sg) in ms do say ("  " + sigText op sg)
    | _ -> ()
    x

let private tracedValue () : LispValue =
    match Debug.tracedList () with
    | [] -> LispNil
    | l -> LispList (l |> List.map LispSym)

let debugBuiltins : (string * LispValue) list = [
    // --- Ошибки как значения ---
    // (raise значение) — ошибка с данными: error-data вернёт значение; сообщение — значение как текст.
    // (error ...) данных не несёт (error-data = nil)
    builtin "raise" (fun args ->
        match args with
        | [v] ->
            let msg = match v with LispStr s -> s | other -> Printer.prettyPrint other
            raise (LispError (msg, Debug.snapshot (), v))
        | _ -> failwith "raise: один аргумент")
    builtin "error?" (fun args ->
        match args with
        | [LispObject { Type = "error" }] -> LispBool true
        | [_] -> LispBool false
        | _ -> failwith "error?: один аргумент")
    builtin "error-message" (fun args ->
        match args with
        | [LispObject { Type = "error"; Fields = f }] -> f.[0]
        | [v] -> Printer.expectError "error-message" 1 "ожидался объект ошибки" v
        | _ -> failwith "error-message: один аргумент")
    builtin "error-stack" (fun args ->
        match args with
        | [LispObject { Type = "error"; Fields = f }] -> f.[1]
        | [v] -> Printer.expectError "error-stack" 1 "ожидался объект ошибки" v
        | _ -> failwith "error-stack: один аргумент")
    builtin "error-data" (fun args ->
        match args with
        | [LispObject { Type = "error"; Fields = f }] -> f.[2]
        | [v] -> Printer.expectError "error-data" 1 "ожидался объект ошибки" v
        | _ -> failwith "error-data: один аргумент")
    // (backtrace) — печатает стек последней ошибки REPL/AgentApi
    builtin "backtrace" (fun _ ->
        (match Debug.lastError with
         | LispObject { Type = "error"; Fields = f } as e ->
             say (match f.[0] with LispStr m -> m | other -> Printer.prettyPrint other)
             for l in errorStackLines e do say l
         | _ -> say "ошибок не было")
        LispNil)

    // --- Защита глубины ---
    builtin "set-max-depth" (fun args ->
        match args with
        | [LispInteger n] when n > 0I && n < 100000000I -> Debug.maxDepth <- int n; LispInteger n
        | [v] -> Printer.expectError "set-max-depth" 1 "ожидалось положительное целое" v
        | _ -> failwith "set-max-depth: один аргумент")

    // --- Шаг D3c: отладочный режим проглоченных ошибок ---
    // (set-debug! #t|#f) — включить/выключить печать ошибок, перехваченных try с обработчиком
    builtin "set-debug!" (fun args ->
        match args with
        | [LispBool on] -> Debug.setSwallowedDebug on; LispBool (Debug.swallowedDebug ())
        | [v] -> Printer.expectError "set-debug!" 1 "ожидалось #t или #f" v
        | _ -> failwith "set-debug!: один аргумент")
    // (swallowed-errors) — список сообщений проглоченных ошибок с начала запроса (для тестов/диагностики)
    builtin "swallowed-errors" (fun _ ->
        LispList (Debug.swallowed () |> List.map LispStr))
    // (debug-mode?) — включён ли отладочный режим (LISP_DEBUG=1 или set-debug!)
    builtin "debug-mode?" (fun _ -> LispBool (Debug.swallowedDebug ()))

    // --- trace ---
    builtin "trace" (fun args ->
        for a in args do Debug.traceAdd (traceName "trace" a)
        tracedValue ())
    builtin "trace-methods" (fun args ->
        for a in args do Debug.traceMethods (symName "trace-methods" a)
        tracedValue ())
    builtin "untrace" (fun args ->
        if args.IsEmpty then Debug.untraceAll ()
        else for a in args do Debug.untrace (traceName "untrace" a)
        tracedValue ())

    // --- Шаг 16: условные правила (defrule — спецформа в Evaluator) ---
    // (rules 'op) — имена правил оператора в порядке определения; (rule-names) — все правила
    builtin "rules" (fun args ->
        match args with
        | [op] -> LispList (Rules.rulesOf (symName "rules" op) |> List.map LispSym)
        | _ -> failwith "rules: один аргумент — оператор")
    builtin "rule-names" (fun args ->
        match args with
        | [] -> LispList (Rules.names () |> List.map LispSym)
        | _ -> failwith "rule-names: без аргументов")
    builtin "remove-rule" (fun args ->
        match args with
        | [name] -> LispBool (Rules.remove (symName "remove-rule" name))
        | _ -> failwith "remove-rule: один аргумент — имя правила")
    builtin "trace-rules" (fun _ -> Rules.tracing <- true; LispBool true)
    builtin "untrace-rules" (fun _ -> Rules.tracing <- false; LispBool false)

    // --- Интроспекция ---
    builtin "explain-dispatch" explainDispatch
    builtin "methods" (fun args ->
        match args with
        | [op] ->
            let sigs = Objects.methodSignatures (symName "methods" op)
            if sigs.IsEmpty then LispNil
            else LispList (sigs |> List.map (fun sg -> LispList (sg |> List.map LispSym)))
        | _ -> failwith "methods: один аргумент — операция")
    builtin "methods-of" (fun args ->
        match args with
        | [t] ->
            let ms = Objects.methodsOfType (symName "methods-of" t)
            if ms.IsEmpty then LispNil
            else LispList (ms |> List.map (fun (op, sg) -> LispList [ LispSym op; LispList (sg |> List.map LispSym) ]))
        | _ -> failwith "methods-of: один аргумент — тип")
]
