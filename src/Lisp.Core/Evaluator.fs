// Публичный API вычислителя: eval / apply / load / newEnv / globalEnv.
// Шаг 17b: прямой интерпретатор (evalCore) заменён предкомпиляцией в дерево узлов — см. Compiler.fs;
// здесь остались охрана верхнего уровня (снимок стека ошибки), load, регистрация builtins и builtins, которым нужно окружение
module Evaluator

open System.Collections.Generic
open System.Runtime.CompilerServices
open Types
open Numeric
open Builtins

// --- Публичные точки входа ---
// Самый внешний вызов охраняется: любое исключение превращается в LispError со снимком стека
// (кадры на этот момент целы — вложенные вызовы ничего не разматывают), глубина сбрасывается в 0.
// Вложенные вызовы (applyHook из упрощателя и т.п.) идут прямо в ядро без try

let private guarded (f: unit -> LispValue) : LispValue =
    Debug.active <- true
    try
        try f ()
        with ex -> raise (Debug.wrap ex)
    finally
        Debug.active <- false
        Debug.depth <- 0

// Вычисление формы в области имён модуля modl (загрузка файла модуля); null — глобальная область
// Подшаг 22.4: самый внешний вызов делает env текущей сессией (ActiveSession: декларации доменов)
let private evalIn (modl: ModuleInfo) (expr: LispValue) (env: Env) : LispValue =
    if Debug.active then Compiler.evalTopIn modl expr env
    else
        ActiveSession.Env <- env
        guarded (fun () -> Compiler.evalTopIn modl expr env)

let eval (expr: LispValue) (env: Env) : LispValue = evalIn null expr env

let apply (fn: LispValue) (args: LispValue list) : LispValue =
    if Debug.active then Compiler.applyT fn args
    else guarded (fun () -> Compiler.applyT fn args)

// Вычисление списка выражений, возврат последнего значения
let evalAll (exprs: LispValue list) (env: Env) : LispValue =
    match exprs with
    | [] -> LispNil
    | _ -> List.fold (fun _ e -> eval e env) LispNil exprs

// Шаг 21h': кэш разбора файлов. Каждое новое окружение (newEnv: тесты, сессии AgentApi) заново читало все lib\*.lisp —
// разбор текста составлял ~45 % стоимости newEnv. Формы — неизменяемые данные (списки F#, строки, числа), поэтому разобранные
// формы файла можно делить между окружениями: ключ — путь, значение — (текст, формы); совпадение текста проверяется
// сравнением строк, так что изменённый файл (временные файлы тестов) читается заново. Не кэшируются файлы с литералами
// векторов #(...): vset! меняет вектор на месте — общий литерал протекал бы между окружениями
let private parseCache = System.Collections.Concurrent.ConcurrentDictionary<string, struct (string * LispValue list)>()

let rec private hasVectorLiteral (v: LispValue) : bool =
    match v with
    | LispVector _ -> true
    | LispList items -> List.exists hasVectorLiteral items
    | LispPair (a, b) -> hasVectorLiteral a || hasVectorLiteral b
    | _ -> false

let private readFileForms (path: string) (content: string) : LispValue list =
    match parseCache.TryGetValue path with
    | true, struct (cached, forms) when System.String.Equals(cached, content) -> forms
    | _ ->
        let forms = Reader.readAllFrom path content
        if not (List.exists hasVectorLiteral forms) then parseCache.[path] <- struct (content, forms)
        forms

// --- Шаг 21h': модули библиотеки ---
// Файл начинается с (module имя (export f g ...)). Определения файла (define, defmacro) принадлежат модулю: экспортированные
// имена — глобальные, прочие — приватные (ячейка «имя::имя», ссылки разрешает компилятор, см. Compiler.refName).
// defmethod / defrule — записи в глобальных таблицах (методы и правила действуют на все модули), но тела и условия
// компилируются в области имён модуля, а повторное определение того же метода/правила из ДРУГОГО модуля — ошибка.
// Типы (deftype) — глобальны. Код вне модулей (REPL, математический язык, пользовательские файлы без module)
// видит только глобальные имена и переопределяет что угодно.

// Имена, определяемые верхнеуровневыми формами (define, defmacro; внутри begin — тоже)
let rec private definedNames (forms: LispValue list) : string list =
    forms |> List.collect (fun f ->
        match f with
        | LispList (LispSym "define" :: LispSym n :: _) -> [ n ]
        | LispList (LispSym "define" :: LispList (LispSym n :: _) :: _) -> [ n ]
        | LispList (LispSym "defmacro" :: LispList (LispSym n :: _) :: _) -> [ n ]
        | LispList (LispSym "begin" :: inner) -> definedNames inner
        | _ -> [])

// Заголовок (module имя [(export имя ...)]) → (имя, экспорт)
let private parseModuleHeader (path: string) (header: LispValue list) : string * string list =
    let file = System.IO.Path.GetFileName path
    match header with
    | LispSym name :: opts ->
        let exports =
            opts |> List.collect (fun o ->
                match o with
                | LispList (LispSym "export" :: names) ->
                    names |> List.map (fun n ->
                        match n with
                        | LispSym s -> s
                        | other -> failwithf "%s: module %s: имя экспорта — символ, получено %s" file name (Printer.prettyPrint other))
                | other -> failwithf "%s: module %s: ожидалось (export имя ...), получено %s" file name (Printer.prettyPrint other))
        (name, exports)
    | _ -> failwithf "%s: module: ожидалось (module имя (export имя ...))" file

// Объявить модуль (или добавить файл к существующему): проверка конфликтов экспорта, разметка приватных имён
let private declareModule (env: Env) (path: string) (name: string) (exports: string list) (body: LispValue list) : ModuleInfo =
    let file = System.IO.Path.GetFileName path
    let reg = env.Modules
    let m =
        match reg.TryGetValue name with
        | true, m -> m
        | _ ->
            let m = ModuleInfo name
            reg.[name] <- m
            m
    if not (m.Files.Contains path) then m.Files.Add path
    for e in exports do
        // два модуля не экспортируют одно имя
        for other in reg.Values do
            if not (obj.ReferenceEquals(other, m)) && other.Exports.Contains e then
                failwithf "%s: модуль %s экспортирует имя %s, которое уже экспортирует модуль %s" file name e other.Name
        // и не переопределяют встроенную функцию (builtin) молча
        match env.TryBound e with
        | null -> ()
        | c ->
            match c.Value with
            | LispBuiltin _ -> failwithf "%s: модуль %s экспортирует имя %s, совпадающее со встроенной функцией (builtin)" file name e
            | _ -> ()
        m.Exports.Add e |> ignore
        m.Private.Remove e |> ignore
    // приватные имена: определены в файле и не экспортированы
    for d in definedNames body do
        if not (m.Exports.Contains d) then
            // определение, затеняющее экспорт ДРУГОГО модуля, — вероятная ошибка (хотели переопределить его функцию)
            for other in reg.Values do
                if not (obj.ReferenceEquals(other, m)) && other.Exports.Contains d then
                    failwithf "%s: модуль %s определяет имя %s, которое экспортирует модуль %s (переименуйте приватное имя; переопределять чужой экспорт нельзя)" file name d other.Name
            // и не совпадают с builtin: затенение встроенной функции в модуле меняло бы поведение только внутри модуля
            (match env.TryBound d with
             | null -> ()
             | c ->
                match c.Value with
                | LispBuiltin _ -> failwithf "%s: модуль %s определяет имя %s, совпадающее со встроенной функцией (builtin): экспортируйте его или переименуйте" file name d
                | _ -> ())
            m.Private.Add d |> ignore
    m

// Функция загрузки .lisp-файла: читает, парсит и выполняет все выражения
// Определяется ПОСЛЕ eval, т.к. использует его. Первая форма (module ...) — модуль библиотеки (см. выше)
let loadIntoEnv (path: string) (env: Env) : LispValue =
    if System.IO.File.Exists path then
        let content = System.IO.File.ReadAllText path
        // Шаг 20: ошибка чтения (скобки, строки) — с именем файла
        let exprs =
            try readFileForms path content
            with ex -> failwithf "load: %s: %s" (System.IO.Path.GetFileName path) ex.Message
        let modl, ownExports, body =
            match exprs with
            | LispList (LispSym "module" :: header) :: rest ->
                let name, exports = parseModuleHeader path header
                declareModule env path name exports rest, exports, rest
            | _ -> null, [], exprs
        let results = body |> List.map (fun e -> evalIn modl e env)
        // экспортированные этим файлом имена должны быть определены
        for e in ownExports do
            if isNull (env.TryBound e) then
                failwithf "%s: модуль %s экспортирует имя %s, но не определяет его" (System.IO.Path.GetFileName path) modl.Name e
        match List.rev results with
        | last :: _ -> last
        | [] -> LispNil
    else
        failwithf "load: файл не найден: %s" path

// Имена, определённые (экспортом или приватно) более чем в одном модуле: при глобальных определениях (до шага 21h') такие
// имена перезаписывали друг друга молча. Возвращает строки «имя: модуль1, модуль2»
let duplicateDefinitions (env: Env) : string list =
    env.Modules.Values
    |> Seq.collect (fun m -> Seq.append m.Exports m.Private |> Seq.map (fun n -> n, m.Name))
    |> Seq.groupBy fst
    |> Seq.filter (fun (_, ms) -> (ms |> Seq.map snd |> Seq.distinct |> Seq.length) > 1)
    |> Seq.map (fun (n, ms) -> n + ": " + String.concat ", " (ms |> Seq.map snd |> Seq.distinct))
    |> Seq.sort
    |> List.ofSeq

// Диагностика модулей: ссылки скомпилированного кода модуля на глобальные имена, которых нет ни в одном модуле и нигде
// не определено (обычно — обращение к неэкспортированному имени другого модуля или опечатка). Предварительно компилирует
// тела всех функций библиотеки (в норме они компилируются лениво при первом вызове). Возвращает строки «модуль: имя ...»
let checkModules (env: Env) : string list =
    let failed = ResizeArray<string>()
    // все шаблоны лямбд модулей (включая вложенные: их список пополняется по мере компиляции)
    for m in List.ofSeq env.Modules.Values do
        let mutable i = 0
        while i < m.Codes.Count do
            match m.Codes.[i] with
            | :? LambdaCode as code ->
                try Compiler.ensureCompiled code
                with ex -> failed.Add (m.Name + ": ошибка компиляции лямбды: " + ex.Message)
            | _ -> ()
            i <- i + 1
    [ yield! failed
      for m in env.Modules.Values do
        let missing =
            m.GlobalRefs
            |> Seq.filter (fun n -> (env.Lookup n).IsNone)
            |> Seq.sort
            |> List.ofSeq
        if not missing.IsEmpty then yield m.Name + ": " + String.concat " " missing ]

// Список builtins без дубликатов: каждое имя регистрируется ровно один раз
// (раньше последняя регистрация «перекрывала» предыдущую — этот паттерн убран в шаге 15a)
let private allBuiltinsList : (string * LispValue) list =
    allBuiltins @ ObjectBuiltins.objectBuiltins @ DebugBuiltins.debugBuiltins @ CasBuiltins.all @ PolyBuiltins.all @ AlgoBuiltins.all @ MathLangBuiltins.all @ ListBuiltins.all

// Шаг 21h'': имена всех builtin окружения (включая определяемые в newEnv) — для проверки справочника docs\lisp-library-guide.md
let builtinNames : string list =
    (allBuiltinsList |> List.map fst) @ [ "load"; "eval"; "m-callable?"; "bound?"; "fbound?"; "describe" ]

// Спецформы компилятора (не функции: аргументы не вычисляются заранее)
let specialFormNames : string list =
    [ "quote"; "quasiquote"; "unquote"; "unquote-splicing"; "define"; "set!"; "lambda"; "if"; "cond"; "case"; "and"; "or"
      "let"; "let*"; "letrec"; "begin"; "defmacro"; "defrule"; "defmethod"; "module"; "try"; "unwind-protect"; "time"; "profile" ]

// Шаг 21e: реестр быстрых входов заполняется один раз (Lazy потокобезопасен; тесты создают окружения параллельно)
let private fastInit : Lazy<unit> = lazy (FastBuiltins.register allBuiltinsList)

// Шаг 17b: скомпилированные условия правил: условие компилируется один раз (в области с переменными ?x)
type private CondCache = { Names: string[]; Node: Node; Size: int }
let private condCache = ConditionalWeakTable<Rules.Rule, CondCache>()

// Новое окружение со всеми встроенными функциями (используется globalEnv и AgentApi.makeSession)
// load добавляем ПОСЛЕ создания env: он выполняет файл в этом же env (рекурсия)
// Шаг D0: если загрузка prelude не удалась, сообщение сохраняется здесь (см. newEnv ниже);
// Host печатает его и завершается с кодом 1, не крашась. None — библиотека загружена (норма)
let mutable preludeError : string option = None

let newEnv () : Env =
    Compiler.install ()
    // Шаг 21h: упрощение суммы по корням (root-sum) — хук Simplify
    RootSum.install ()
    let env = Env.Empty()
    // Дубликат имени builtin — ошибка конфигурации: исключение при создании окружения
    let dups = allBuiltinsList |> List.countBy fst |> List.filter (fun (_, n) -> n > 1) |> List.map fst
    if not dups.IsEmpty then
        failwithf "Дубликаты builtin-функций: %s" (String.concat ", " dups)
    allBuiltinsList |> List.iter (fun (name, value) -> env.Define name value |> ignore)
    // Шаг 21e: быстрые входы горячих builtin (один раз на процесс; объекты-функции общие для всех окружений)
    fastInit.Force()
    // Шаг 15a: арифметика алгебраических чисел — методы + * = < > (механизм шага 14)
    CasBuiltins.registerAlgebraicMethods ()
    // load — выполняет файл в ЭТОМ окружении
    env.Define "load" (LispBuiltin (Builtin (fun args ->
        match args with
        | [LispStr path] ->
            Sandbox.checkRead "load" path               // подшаг 22.4: песочница --mcp
            loadIntoEnv path env
        | _ -> failwith "load: требуется один строковый аргумент"))) |> ignore
    // Шаг 20: (eval выражение) — вычислить данные как код в этом окружении (нужно series: пользовательские функции)
    env.Define "eval" (LispBuiltin (Builtin (fun args ->
        match args with
        | [e] -> eval e env
        | _ -> failwith "eval: один аргумент"))) |> ignore
    // Шаг 15a: (bound? 'sym) — символ связан в окружении; (fbound? 'sym) — связан с функцией
    // (builtin/lambda/macro). Нужны lib\tensor.lisp: список с такой головой — компонента-выражение
    let boundQuery (who: string) (onlyFunctions: bool) =
        LispBuiltin (Builtin (fun args ->
            match args with
            | [LispSym name] ->
                match env.Lookup name with
                | Some (LispFunc _ | LispBuiltin _ | LispMacro _) -> LispBool true
                | Some _ -> LispBool (not onlyFunctions)
                | None -> LispBool false
            | _ -> failwithf "%s: требуется один аргумент — символ" who))
    // Шаг 21b: (m-callable? 'sym) — символ связан с функцией или builtin (не макросом): вызов можно компилировать напрямую
    env.Define "m-callable?" (LispBuiltin (Builtin (fun args ->
        match args with
        | [LispSym name] ->
            match env.Lookup name with
            | Some (LispFunc _ | LispBuiltin _) -> LispBool true
            | _ -> LispBool false
        | _ -> failwith "m-callable?: требуется один аргумент — символ"))) |> ignore
    env.Define "bound?" (boundQuery "bound?" false) |> ignore
    env.Define "fbound?" (boundQuery "fbound?" true) |> ignore
    // Шаг 15b: (describe x) — нужен доступ к окружению (значение символа)
    env.Define "describe" (LispBuiltin (Builtin (fun args ->
        match args with
        | [x] -> DebugBuiltins.describe env.Lookup x
        | _ -> failwith "describe: один аргумент"))) |> ignore
    // Шаг 14: упроститель/принтер вызывают Lisp-методы через Objects.applyHook
    Objects.applyHook <- apply
    // Шаг 16: условие правила — Lisp-выражение в окружении определения; переменные образца ("?x" → значение)
    // — локальные переменные скомпилированного условия (слоты 0..n-1 по порядку имён)
    Rules.conditionHook <- (fun rule b ->
        match rule.Condition with
        | Some cond ->
            let names = b |> Map.toArray |> Array.map fst
            let vals = b |> Map.toArray |> Array.map snd
            let cc =
                match condCache.TryGetValue rule with
                | true, c when c.Names = names -> c
                | _ ->
                    let node, size = Compiler.compileWithVars rule.Module rule.Env names cond
                    let c = { Names = names; Node = node; Size = size }
                    condCache.Remove rule |> ignore
                    condCache.Add(rule, c)
                    c
            let run () =
                let slots = Compiler.topFrame (max cc.Size names.Length)
                Array.blit vals 0 slots 0 vals.Length
                cc.Node.Eval slots
            if Debug.active then run ()
            else guarded run
        | None -> LispBool true)
    // Шаг AC.3: правило :ac — (ac-match образец выражение :where условие) из lib\match.lisp, найденный в окружении определения
    // правила на момент применения (модуль match загружается prelude после rules, правила при этом уже определены).
    // Условие правила передаётся как :where-функция: привязки ((?x v) ...) → Bindings → conditionHook; в :where годится только #t
    // (unknown здесь молча отбрасывается, как у обычных правил: без записи условия на каждом упрощении)
    Rules.formatValue <- (fun v -> try MathPrinter.mathPrint v with _ -> Printer.prettyPrint v)
    Rules.acMatchHook <- (fun rule expr ->
        match rule.Env.Lookup "ac-match" with
        | Some fn ->
            let opts =
                match rule.Condition with
                | None -> []
                | Some _ ->
                    let whereFn =
                        LispBuiltin (Builtin (fun args ->
                            let items = (match args with [LispList items] -> items | _ -> [])
                            let b =
                                items |> List.choose (fun it ->
                                    match it with
                                    | LispList [LispSym n; v] -> Some (n, v)
                                    | _ -> None)
                                |> Map.ofList
                            (match Rules.conditionHook rule b with LispBool true -> LispBool true | _ -> LispBool false)))
                    [ LispSym ":where"; whereFn ]
            match apply fn ([ rule.Pattern; expr ] @ opts) with
            | LispBool false -> None
            | LispList items ->
                Some (items |> List.fold (fun (m: Map<string, LispValue>) it ->
                                match it with
                                | LispList [LispSym n; v] -> Map.add n v m
                                | _ -> m) Map.empty)
            | LispNil -> Some Map.empty
            | _ -> None
        | None -> None)
    // Шаг 14: библиотека на Lisp — lib/prelude.lisp рядом с исполняемым файлом (нет файла — не падаем)
    // Шаг 15: переменная lib-dir — каталог lib с разделителем на конце (prelude грузит из него tensor.lisp)
    let libDir = System.IO.Path.Combine(System.AppContext.BaseDirectory, "lib") + string System.IO.Path.DirectorySeparatorChar
    env.Define "lib-dir" (LispStr libDir) |> ignore
    let prelude = System.IO.Path.Combine(libDir, "prelude.lisp")
    if System.IO.File.Exists prelude then
        // Шаг D0: ошибка в файле prelude (кривой defrule, скобки, ...) раньше падала в статическом конструкторе
        // Evaluator (TypeInitializationException) — после этого ЛЮБОЙ запуск Lisp.exe падал с необработанным
        // исключением. Теперь: сообщение в stderr с именем файла и строкой ошибки, работа продолжается без
        // библиотеки (REPL/файлы/погрузчики -e по-прежнему работают; неопределённые имена дадут обычную ошибку).
        try loadIntoEnv prelude env |> ignore
        with ex ->
            preludeError <-
                "ОШИБКА ЗАГРУЗКИ БИБЛИОТЕКИ (lib\\prelude.lisp): " + Debug.formatError (Debug.wrap ex)
                |> Some
            System.Console.Error.WriteLine preludeError.Value
    env

// Шаг 15b: запомнить ошибку REPL/AgentApi — Debug.lastError и переменная *last-error* (объект ошибки)
let recordError (env: Env) (ex: exn) : unit =
    let obj = Debug.errorObject (Debug.wrap ex)
    Debug.lastError <- obj
    env.Define "*last-error*" obj |> ignore

// Глобальное окружение (общий синглтон)
let globalEnv : Env = newEnv ()
