// Шаг 17b: предкомпиляция S-выражений в дерево узлов (замена прямого интерпретатора evalCore).
//
// Идея: спецформы разбираются ОДИН раз при компиляции, а не при каждом вычислении; имена переменных
// разрешаются заранее: локальные → (глубина, индекс) во фреймах-массивах (Scope), глобальные → ячейка
// (Cell) из таблицы окружения. Поиска по строкам и Map во время выполнения нет.
//
// Основные решения:
//  * Фрейм — на ВЫЗОВ функции («плоский»): параметры, let/let*/letrec и внутренние define получают
//    слоты в том же массиве (каждое let-выражение вычисляется во фрейме не более одного раза —
//    повторные вычисления идут через новый вызов, т.е. новый фрейм), замыкание = ссылка на фрейм.
//  * Тела lambda компилируются ЛЕНИВО при первом вызове — макрос, определённый после функции,
//    но до её первого вызова, раскрывается. Макрос раскрывается при компиляции вызова; если голова —
//    не макрос на момент компиляции, но на момент вычисления оказалась макросом (локальная переменная,
//    переопределение) — раскрытие «на лету» (без TCO внутри раскрытия).
//  * TCO: хвостовой вызов пользовательской функции возвращает маркер tailMarker (аргументы и код
//    лежат в pendingScope — фрейм вызова, функция в его последнем элементе); трамплин (runBody) крутится в ближайшем нехвостовом вызове.
//    Кадр стека Debug при хвостовом вызове ЗАМЕНЯЕТСЯ (как раньше).
//  * Вызовы с trace/профилированием идут без TCO (callHooked).
module Compiler

open System
open System.Collections.Generic
open Types
open Numeric
open Builtins

// ====================== Рантайм ======================

// Маркер хвостового вызова (сравнивается по ссылке)
let tailMarker : LispValue = LispStr "#<tail-call>"
let inline isTailMarker (v: LispValue) : bool = obj.ReferenceEquals(v, tailMarker)

// Шаг 21i' (b): только фрейм — код берётся из функции в его последнем элементе (одна запись в статическое поле вместо двух)
let mutable private pendingScope : Scope = null

let inline private isUnbound (v: LispValue) : bool = obj.ReferenceEquals(v, null)

// Шаг 21d: позиция формы, компилируемой в данный момент (вложенные формы без своей позиции — например, из
// раскрытия макроса — наследуют позицию ближайшей объемлющей). Только время компиляции, на выполнение не влияет
let mutable private curPos : SrcPos = null
// Верхнеуровневая форма, прочитанная ридером, внутри которой идёт компиляция (null — форма построена программой):
// по ней вычисляются позиции вложенных форм (Types.TopPos)
let mutable private curTop : TopPos = null

// Шаг 21h': модуль, в области имён которого идёт компиляция (null — глобальный код: REPL, пользовательские файлы, eval).
// Лямбды запоминают модуль определения (LambdaCode.Module): их тела компилируются лениво, уже после загрузки файла.
// Правила: приватное имя модуля (определено в нём и не экспортировано) разрешается в ячейку «модуль::имя»; прочие
// глобальные имена — как раньше (поздняя привязка, ячейка создаётся при первом упоминании)
let mutable private curModule : ModuleInfo = null

// Ссылка на глобальное имя из кода модуля: приватное → «модуль::имя»; иначе — само имя (запоминается для проверки экспорта)
let private refName (name: string) : string =
    if isNull curModule then name
    elif curModule.Private.Contains name then curModule.Qualify name
    else
        curModule.GlobalRefs.Add name |> ignore
        name

// Имя, под которым определяется верхнеуровневое define/defmacro: экспортированное — глобальное, прочее — приватное
// (имена, уже содержащие «::», остаются как есть)
let private definedName (name: string) : string =
    if isNull curModule || name.Contains "::" then name
    elif curModule.Exports.Contains name then name
    else
        curModule.Private.Add name |> ignore
        curModule.Qualify name

// Позиция формы: из описания текущей верхнеуровневой формы, затем из слабой таблицы (AST языка); иначе null
let private lookupPos (expr: LispValue) : SrcPos =
    let p = if isNull curTop then null else curTop.PosOf expr
    if isNull p then weakPosOf expr else p

// Тело скомпилировано? (иначе — компилируем при первом вызове)
let inline ensureCompiled (code: LambdaCode) : unit =
    if isNull code.Body then code.Init ()

// Проверка числа аргументов (сообщения те же, что были у bindArgs)
let checkArity (code: LambdaCode) (n: int) : unit =
    if not (isNull code.Error) then failwith code.Error
    if code.HasRest then
        if n < code.NParams then
            failwithf "Функция ожидает не менее %d аргументов, получено %d" code.NParams n
    elif n <> code.NParams then
        failwithf "Функция ожидает %d аргументов, получено %d" code.NParams n

// Шаг 21i' (b): запись в слот фрейма без проверки ковариантности массива. Обычная запись `a.[i] <- v` в LispValue[]
// проверяет тип элемента (LispValue — базовый класс случаев DU, тип значения с ним не совпадает — медленная ветка
// CastHelpers.StelemRef, несколько нс на запись); здесь — прямая запись по ссылке на элемент с проверкой границ
let inline setSlot (a: LispValue[]) (i: int) (v: LispValue) : unit =
    if uint32 i >= uint32 a.Length then raise (IndexOutOfRangeException())
    Runtime.CompilerServices.Unsafe.Add(&Runtime.InteropServices.MemoryMarshal.GetArrayDataReference a, i) <- v

// Шаг 21i' (b): фрейм — массив слотов, последний элемент — вызванная функция (см. Types.Node): по ней находится
// родительский фрейм (Captured) и имя кадра стека. Новый фрейм скомпилированной функции fn (LispFunc/LispMacro)
let inline newFrame (code: LambdaCode) (fn: LispValue) : Scope =
    let n = code.FrameSize
    let f : LispValue[] = Array.zeroCreate (n + 1)
    setSlot f n fn
    f

// Фрейм верхнего уровня (без родителя) с size слотами
let topFrame (size: int) : Scope =
    let f : LispValue[] = Array.zeroCreate (size + 1)
    setSlot f size LispNil
    f

// Фрейм определения (родитель) или null
let inline parentOf (s: Scope) : Scope =
    match s.[s.Length - 1] with
    | LispFunc u -> u.Captured
    | LispMacro u -> u.Captured
    | _ -> null

// Фрейм из списка аргументов (медленный путь: &rest, первый вызов, apply); fn — вызываемая функция
let bindList (code: LambdaCode) (fn: LispValue) (args: LispValue list) : Scope =
    checkArity code (List.length args)
    ensureCompiled code
    let slots = newFrame code fn
    let mutable l = args
    for i in 0 .. code.NParams - 1 do
        setSlot slots i (List.head l)
        l <- List.tail l
    if code.HasRest then setSlot slots code.NParams (LispList l)
    slots

// Выполнить тело функции с трамплином хвостовых вызовов (кадр стека уже положен вызывающим)
let runBody (code: LambdaCode) (frame: Scope) : LispValue =
    let mutable r = code.Body.Eval frame
    while isTailMarker r do
        Cancel.check ()     // подшаг 22.4: бесконечный хвостовой цикл не проходит через checkStack
        let f = pendingScope
        match f.[f.Length - 1] with
        | LispFunc u -> r <- u.Code.Body.Eval f
        | _ -> failwith "внутренняя ошибка: фрейм хвостового вызова без функции"
    r

// Имя кадра для значения-функции, вызванного не через форму с символом в голове
let frameNameOf (fn: LispValue) : string =
    match fn with
    | LispFunc u -> u.Name
    | _ -> "<builtin>"

// Применение функции к списку аргументов: кадр на стек, снимается при нормальном выходе
let applyCore (name: string) (fn: LispValue) (args: LispValue list) : LispValue =
    let entry = Debug.depth
    let r =
        match fn with
        | LispBuiltin (Builtin f) ->
            Debug.push name args 0
            f args
        | LispFunc u ->
            Debug.push name args 0
            Debug.checkStack ()
            runBody u.Code (bindList u.Code fn args)
        | other -> failwithf "Невозможно применить как функцию: %s" (Printer.prettyPrint other)
    Debug.depth <- entry
    r

// Вызов с trace и/или профилированием (без TCO). Профилирование внутри trace
let callHooked (name: string) (fn: LispValue) (args: LispValue list) : LispValue =
    let inner () =
        if Debug.profiling then
            Debug.measure name (match fn with LispFunc _ -> false | _ -> true) (fun () -> applyCore name fn args)
        else applyCore name fn args
    if Debug.isTraced name then Debug.traceCall name args inner else inner ()

// Применение с учётом trace/профилирования
let applyT (fn: LispValue) (args: LispValue list) : LispValue =
    let name = frameNameOf fn
    if Debug.hooked && (Debug.profiling || Debug.isTraced name) then callHooked name fn args
    else applyCore name fn args

// Раскрытие макроса: тело вычисляется в его окружении над формами-аргументами (кадра нет).
// Тело макроса скомпилировано без хвостовых вызовов; mv — значение LispMacro m
let expandMacro (mv: LispValue) (m: UserFunction) (forms: LispValue list) : LispValue =
    let frame = bindList m.Code mv forms      // компилирует тело при первом раскрытии — до чтения Body
    m.Code.Body.Eval frame

// ====================== Структуры времени компиляции ======================

// Функция в смысле фрейма: счётчик слотов
[<AllowNullLiteral>]
type FnInfo() =
    member val NextSlot = 0 with get, set

[<AllowNullLiteral>]
type VarInfo(index: int, isChecked: bool) =
    member _.Index = index
    member _.Checked = isChecked      // слот может быть ещё пуст (внутренний define): проверять при чтении

// Блок видимости: имена → слоты. Принадлежит функции (Fn); Parent — внешний блок (возможно другой функции).
// IsTop — корневой блок верхнего уровня: define в нём — глобальный
[<AllowNullLiteral>]
type Block(fn: FnInfo, parent: Block, isTop: bool) =
    member _.Fn = fn
    member _.Parent = parent
    member _.IsTop = isTop
    member val Vars = Dictionary<string, VarInfo>()

let declare (b: Block) (name: string) (isChecked: bool) : int =
    match b.Vars.TryGetValue name with
    | true, v -> v.Index
    | _ ->
        let i = b.Fn.NextSlot
        b.Fn.NextSlot <- i + 1
        b.Vars.[name] <- VarInfo(i, isChecked)
        i

// Поиск локальной переменной: (глубина по границам функций, описание)
let resolveLocal (b: Block) (name: string) : (int * VarInfo) option =
    let mutable cur = b
    let mutable depth = 0
    let mutable res = None
    while res.IsNone && not (isNull cur) do
        match cur.Vars.TryGetValue name with
        | true, v -> res <- Some (depth, v)
        | _ ->
            let p = cur.Parent
            if not (isNull p) && not (obj.ReferenceEquals(p.Fn, cur.Fn)) then depth <- depth + 1
            cur <- p
    res

// ====================== Узлы ======================

/// Ключевое слово: имя начинается с «:» и длиннее одного знака (`:where`; `module::имя` — двоеточие не в начале)
let isKeywordName (name: string) = name.Length > 1 && name.[0] = ':'

let private unknownSymbol (name: string) : 'a =failwithf "Неизвестный символ: %s" name

let inline private scopeAt (s: Scope) (depth: int) : Scope =
    let mutable sc = s
    for _ in 1 .. depth do sc <- parentOf sc
    sc

type ConstNode(v: LispValue) =
    inherit Node()
    override _.Eval(_) = v

type Local0(i: int) =
    inherit Node()
    override _.Eval(s) = s.[i]

type Local1(i: int) =
    inherit Node()
    override _.Eval(s) = (parentOf s).[i]

type LocalN(depth: int, i: int) =
    inherit Node()
    override _.Eval(s) = (scopeAt s depth).[i]

// Переменная, которая может быть ещё не определена (внутренний define / letrec*)
type LocalChecked(depth: int, i: int, name: string) =
    inherit Node()
    override _.Eval(s) =
        let v = (scopeAt s depth).[i]
        if isUnbound v then unknownSymbol name else v

type GlobalRef(c: Cell) =
    inherit Node()
    member _.Cell = c
    override _.Eval(_) =
        let v = c.Value
        if isUnbound v then
            // ячейка могла быть создана в дочернем окружении раньше, чем имя определили в родителе
            match c.Owner.Lookup c.Name with
            | Some v2 -> v2
            | None -> unknownSymbol c.Name
        else v

type SetLocal(depth: int, i: int, value: Node, name: string) =
    inherit Node()
    override _.Eval(s) =
        let v = value.Eval s
        setSlot (scopeAt s depth) i v
        LispSym name

type SetGlobal(c: Cell, value: Node, name: string) =
    inherit Node()
    override _.Eval(s) =
        let v = value.Eval s
        if not (isUnbound c.Value) then c.Value <- v
        elif not (c.Owner.SetExisting name v) then failwithf "set!: переменная не определена: %s" name
        LispSym name

// Безымянная лямбда получает имя переменной (копия с Name)
let private nameLambda (name: string) (v: LispValue) : LispValue =
    match v with
    | LispFunc u when u.Name = "lambda" -> LispFunc { u with Name = name }
    | other -> other

type DefineGlobal(env: Env, name: string, value: Node, rename: bool) =
    inherit Node()
    override _.Eval(s) =
        let v = value.Eval s
        env.Define name (if rename then nameLambda name v else v) |> ignore
        LispSym name

type DefineLocal(i: int, value: Node, name: string, rename: bool) =
    inherit Node()
    override _.Eval(s) =
        let v = value.Eval s
        setSlot s i (if rename then nameLambda name v else v)
        LispSym name

type If3(c: Node, t: Node, e: Node) =
    inherit Node()
    override _.Eval(s) = if isTruthy (c.Eval s) then t.Eval s else e.Eval s

type If2(c: Node, t: Node) =
    inherit Node()
    override _.Eval(s) = if isTruthy (c.Eval s) then t.Eval s else LispNil

type BeginNode(nodes: Node[]) =
    inherit Node()
    override _.Eval(s) =
        let last = nodes.Length - 1
        for i in 0 .. last - 1 do nodes.[i].Eval s |> ignore
        nodes.[last].Eval s

type AndNode(nodes: Node[]) =
    inherit Node()
    override _.Eval(s) =
        let last = nodes.Length - 1
        let mutable i = 0
        let mutable res = LispNil
        let mutable fin = false
        while not fin && i < last do
            let v = nodes.[i].Eval s
            if isTruthy v then i <- i + 1
            else
                res <- v
                fin <- true
        if fin then res else nodes.[last].Eval s

type OrNode(nodes: Node[]) =
    inherit Node()
    override _.Eval(s) =
        let last = nodes.Length - 1
        let mutable i = 0
        let mutable res = LispNil
        let mutable fin = false
        while not fin && i < last do
            let v = nodes.[i].Eval s
            if isTruthy v then
                res <- v
                fin <- true
            else i <- i + 1
        if fin then res else nodes.[last].Eval s

// Ветка cond: test = null для else
type CondNode(tests: Node[], bodies: Node[]) =
    inherit Node()
    override _.Eval(s) =
        let mutable i = 0
        let mutable res = LispNil
        let mutable fin = false
        while not fin && i < tests.Length do
            if isNull tests.[i] || isTruthy (tests.[i].Eval s) then
                res <- bodies.[i].Eval s
                fin <- true
            else i <- i + 1
        res

// Ветка case: datums = null для else
type CaseNode(key: Node, datums: LispValue list[], bodies: Node[]) =
    inherit Node()
    override _.Eval(s) =
        let k = key.Eval s
        let mutable i = 0
        let mutable res = LispNil
        let mutable fin = false
        while not fin && i < bodies.Length do
            if obj.ReferenceEquals(datums.[i], null) || (datums.[i] |> List.exists (fun d -> structEqual d k)) then
                res <- bodies.[i].Eval s
                fin <- true
            else i <- i + 1
        res

// let / let*: инициализаторы по порядку в слоты текущего фрейма (у каждой привязки — свой слот)
type LetNode(slots: int[], inits: Node[], body: Node) =
    inherit Node()
    override _.Eval(s) =
        for k in 0 .. inits.Length - 1 do
            setSlot s slots.[k] (inits.[k].Eval s)
        body.Eval s

// letrec: сначала заглушки nil, значения вычисляются все, затем присваиваются
type LetrecNode(slots: int[], inits: Node[], body: Node) =
    inherit Node()
    override _.Eval(s) =
        for k in 0 .. slots.Length - 1 do s.[slots.[k]] <- LispNil
        let vals = inits |> Array.map (fun n -> n.Eval s)
        for k in 0 .. slots.Length - 1 do s.[slots.[k]] <- vals.[k]
        body.Eval s

type LambdaNode(code: LambdaCode, name: string, ps: string list, body: LispValue, env: Env) =
    inherit Node()
    override _.Eval(s) =
        LispFunc { Name = name; Params = ps; Body = body; Env = env; Code = code; Captured = s }

// Определение макроса (глобальное или локальное)
type DefMacroNode(code: LambdaCode, name: string, ps: string list, body: LispValue, env: Env, localSlot: int) =
    inherit Node()
    override _.Eval(s) =
        let m = LispMacro { Name = name; Params = ps; Body = body; Env = env; Code = code; Captured = s }
        if localSlot < 0 then env.Define name m |> ignore
        else s.[localSlot] <- m
        LispSym name

// Шаг 21h': владелец глобального определения, не привязанного к ячейке (метод defmethod, правило defrule). Модуль библиотеки
// не может молча переопределить определение другого модуля — ошибка с именами обоих; код вне модулей (REPL, пользовательские
// файлы) переопределяет что угодно и снимает владение (поздняя привязка — свойство системы)
let private claimOwner (env: Env) (key: string) (modl: ModuleInfo) : unit =
    let owners = env.Owners
    if isNull modl then owners.Remove key |> ignore
    else
        match owners.TryGetValue key with
        | true, o when o <> modl.Name ->
            failwithf "модуль %s: %s уже определён модулем %s (определения библиотечных модулей не должны пересекаться)" modl.Name key o
        | _ -> owners.[key] <- modl.Name

type DefMethodNode(op: string, types: string list, lam: Node, env: Env, modl: ModuleInfo) =
    inherit Node()
    override _.Eval(s) =
        claimOwner env ("метод " + op + "(" + String.concat " " types + ")") modl
        Objects.addMethod op types (lam.Eval s)
        LispSym op

type DefRuleNode(name: string, pattern: LispValue, replacement: LispValue, cond: LispValue option, ac: bool, title: string, env: Env, modl: ModuleInfo) =
    inherit Node()
    override _.Eval(_) =
        // :ac — образец не канонизируется (ac-match нормализует структуру сам и не должен терять sin²+cos²)
        let canon =
            if ac then pattern
            else
                Rules.suspended <- true
                try Simplify.simplify pattern finally Rules.suspended <- false
        match canon with
        | LispList (LispSym op :: _) when not (PatternMatching.isPatternVar op) ->
            claimOwner env ("правило " + name) modl
            Rules.add { Name = name; Op = op; Pattern = canon; Replacement = replacement
                        Condition = cond; Env = env; Module = modl; Ac = ac; Title = title }
            LispSym name
        | _ -> failwithf "defrule %s: образец должен быть выражением с оператором-символом в голове, получено %s" name (Printer.prettyPrint canon)

// (try выражение обработчик): стек кадров при ошибке цел (нигде не разматывается), снимок берём здесь.
// Подшаг 22.4: прерывание (таймаут/отмена, флаг Cancel.requested поднят) обработчиком не перехватывается
type TryNode(body: Node, handler: Node) =
    inherit Node()
    override _.Eval(s) =
        let depthAtTry = Debug.depth
        let outcome =
            try Choice1Of2 (body.Eval s)
            with ex when not Cancel.requested -> Choice2Of2 (Debug.wrap ex)
        match outcome with
        | Choice1Of2 v -> v
        | Choice2Of2 ex ->
            Debug.depth <- depthAtTry
            // Шаг D3c: отладочный режим — проглоченная ошибка в stderr/warnings (по умолчанию выключено)
            Debug.swallow ex
            applyT (handler.Eval s) [ Debug.errorObject ex ]

type UnwindNode(body: Node, cleanups: Node[]) =
    inherit Node()
    override _.Eval(s) =
        let depthAtEntry = Debug.depth
        let outcome =
            try Choice1Of2 (body.Eval s)
            with ex -> Choice2Of2 (Debug.wrap ex)
        Debug.depth <- depthAtEntry
        // подшаг 22.4: очистка после прерывания выполняется с опущенным флагом отмены (assuming восстанавливает декларации)
        if Cancel.requested then Cancel.suspended (fun () -> for c in cleanups do c.Eval s |> ignore)
        else for c in cleanups do c.Eval s |> ignore
        match outcome with
        | Choice1Of2 v -> v
        | Choice2Of2 ex -> raise ex

type TimeNode(body: Node) =
    inherit Node()
    override _.Eval(s) =
        let t0 = Diagnostics.Stopwatch.GetTimestamp()
        let v = body.Eval s
        let ms = float (Diagnostics.Stopwatch.GetTimestamp() - t0) * 1000.0 / float Diagnostics.Stopwatch.Frequency
        Debug.out().WriteLine(sprintf "время: %.1f мс" ms)
        v

// (profile выражение): профилирование включено только на время вычисления;
// отчёт печатается и при ошибке (затем ошибка пробрасывается)
type ProfileNode(body: Node) =
    inherit Node()
    override _.Eval(s) =
        Debug.profReset ()
        Debug.setProfiling true
        let t0 = Diagnostics.Stopwatch.GetTimestamp()
        let mutable total = 0L
        try
            try
                body.Eval s
            finally
                total <- Diagnostics.Stopwatch.GetTimestamp() - t0
                Debug.setProfiling false
        finally
            Debug.profileReport total

// Квазицитирование: части — элемент или вклеивание (,@)
type QQListNode(isSplice: bool[], nodes: Node[]) =
    inherit Node()
    override _.Eval(s) =
        let acc = ResizeArray<LispValue>()
        for i in 0 .. nodes.Length - 1 do
            let v = nodes.[i].Eval s
            if isSplice.[i] then
                match v with
                | LispList spliced -> acc.AddRange spliced
                | LispNil -> ()
                | other -> failwithf "unquote-splicing: ожидается список, получено %s" (Printer.prettyPrint other)
            else acc.Add v
        LispList (List.ofSeq acc)

// Раскрытие макроса «на лету»: компилирует раскрытие как лямбду без параметров в области вызова
let mutable compileThunk : Env -> Block -> LispValue -> LambdaCode =
    fun _ _ _ -> failwith "compileThunk не инициализирован"

// Вызов: голова вычисляется первой; функция / builtin / макрос (на лету)
// pos — позиция формы вызова в исходнике (null — неизвестна); нужна только кадру стека
type CallNode(head: Node, headName: string, args: Node[], argForms: LispValue list, env: Env, blk: Block, tail: bool, pos: SrcPos, top: TopPos, modl: ModuleInfo) =
    inherit Node()
    let posId = if isNull pos then 0 else pos.Id     // в кадр стека кладётся номер позиции (int), не ссылка
    let mutable cachedMacro : obj = null
    let mutable cachedCode : LambdaCode = null
    // Шаг 21e: кэш быстрого входа builtin для последнего увиденного значения головы (проверка по ссылке на функцию)
    let mutable fastKey : obj = null
    let mutable fastEntry : FastBuiltins.FastEntry = null

    // Обычный вызов builtin: кадр стека (имя, аргументы, позиция) и вызов со списком аргументов
    member _.CallBuiltinSlow(f: LispValue list -> LispValue, argl: LispValue list) : LispValue =
        let d = Debug.depth
        Debug.push headName argl posId
        let r = f argl
        Debug.depth <- d
        r

    member private _.ArgsList(s: Scope) : LispValue list =
        match args.Length with
        | 0 -> []
        | 1 -> [ args.[0].Eval s ]
        | 2 ->
            let a = args.[0].Eval s
            let b = args.[1].Eval s
            [ a; b ]
        | 3 ->
            let a = args.[0].Eval s
            let b = args.[1].Eval s
            let c = args.[2].Eval s
            [ a; b; c ]
        | n ->
            let vals : LispValue[] = Array.zeroCreate n
            for i in 0 .. n - 1 do vals.[i] <- args.[i].Eval s
            let mutable l = []
            for i in n - 1 .. -1 .. 0 do l <- vals.[i] :: l
            l

    // Быстрый путь вызова скомпилированной функции (без &rest, число аргументов совпало):
    // аргументы сразу в слоты нового фрейма (последний элемент — сама функция fv)
    [<Runtime.CompilerServices.MethodImpl(Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)>]
    member private _.CallFast(s: Scope, fv: LispValue, code: LambdaCode) : LispValue =
        let n = args.Length
        let slots = newFrame code fv
        for i in 0 .. n - 1 do setSlot slots i (args.[i].Eval s)
        if tail then
            // хвостовой вызов ЗАМЕНЯЕТ кадр текущей функции; трамплин выполнит тело.
            // Шаг 21i' (b): без checkStack — системный стек здесь не растёт (тело выполнит трамплин
            // уровнем выше), а каждый нехвостовой вызов внутри тела проверяет стек сам
            Debug.replaceTopArr slots n posId
            pendingScope <- slots
            tailMarker
        else
            let entry = Debug.depth
            Debug.pushArr slots n posId
            Debug.checkStack ()
            let r = runBody code slots
            Debug.depth <- entry
            r

    // Шаг 21i' (b): Eval содержит только быстрый путь — маленький кадр системного стека на каждый уровень рекурсии
    // Lisp (прочие ветки с их локальными переменными — в EvalGeneral)
    override this.Eval(s) =
        let fv = head.Eval s
        match fv with
        | LispFunc u when not Debug.hooked && u.Code.Fast && args.Length = u.Code.NParams -> this.CallFast(s, fv, u.Code)
        | _ -> this.EvalGeneral(s, fv)

    member this.EvalGeneral(s: Scope, fv: LispValue) : LispValue =
        match fv with
        | LispFunc u ->
            if Debug.hooked && (Debug.profiling || Debug.isTraced u.Name) then
                // trace/профилирование: без TCO, чтобы показать результат / измерить время
                callHooked u.Name fv (this.ArgsList s)
            else
                let code = u.Code
                if code.Fast && args.Length = code.NParams then this.CallFast(s, fv, code)
                else
                    // медленный путь: &rest, первый вызов (ленивая компиляция), неверное число аргументов
                    let argl = this.ArgsList s
                    if tail then
                        Debug.replaceTop u.Name argl posId
                        Debug.checkStack ()
                        let slots = bindList code fv argl
                        pendingScope <- slots
                        tailMarker
                    else
                        let entry = Debug.depth
                        Debug.push u.Name argl posId
                        Debug.checkStack ()
                        let r = runBody code (bindList code fv argl)
                        Debug.depth <- entry
                        r
        | LispBuiltin (Builtin f) ->
            let n = args.Length
            // Шаг 21e: быстрый вход builtin (1–2 аргумента, без trace/profile): без списка аргументов и кадра стека;
            // результат null — «не обработано» (ошибка, диспетчеризация), тогда обычный путь с уже вычисленными аргументами
            if (n = 1 || n = 2) && not Debug.hooked then
                if not (obj.ReferenceEquals(f, fastKey)) then
                    fastKey <- box f
                    fastEntry <-
                        (match FastBuiltins.table.TryGetValue (box f) with
                         | true, e -> e
                         | _ -> null)
                let fe = fastEntry
                if n = 1 then
                    let a = args.[0].Eval s
                    let r = if isNull fe || isNull fe.F1 then Unchecked.defaultof<LispValue> else fe.F1.Invoke a
                    if isUnbound r then this.CallBuiltinSlow(f, [ a ]) else r
                else
                    let a = args.[0].Eval s
                    let b = args.[1].Eval s
                    let r = if isNull fe || isNull fe.F2 then Unchecked.defaultof<LispValue> else fe.F2.Invoke(a, b)
                    if isUnbound r then this.CallBuiltinSlow(f, [ a; b ]) else r
            else
                let argl = this.ArgsList s
                if Debug.hooked && (Debug.profiling || Debug.isTraced headName) then
                    callHooked headName fv argl
                else
                    this.CallBuiltinSlow(f, argl)
        | LispMacro m ->
            if not (obj.ReferenceEquals(cachedMacro, m)) then
                let expansion = expandMacro fv m argForms
                // раскрытие без собственных позиций наследует позицию вызова макроса
                let saved = curPos
                let savedTop = curTop
                let savedMod = curModule
                curPos <- pos
                curTop <- top
                curModule <- modl
                cachedCode <- (try compileThunk env blk expansion finally (curPos <- saved; curTop <- savedTop; curModule <- savedMod))
                cachedMacro <- box m
            let code = cachedCode
            ensureCompiled code
            // родитель фрейма раскрытия — фрейм вызова s: его несёт функция-обёртка в последнем элементе фрейма
            // (редкий путь: голова оказалась макросом только при вычислении)
            let thunk = LispFunc { Name = "lambda"; Params = []; Body = LispNil; Env = env; Code = code; Captured = s }
            runBody code (newFrame code thunk)
        | other -> failwithf "Невозможно применить как функцию: %s" (Printer.prettyPrint other)

// Шаг 21i' (a): вызов builtin с быстрым входом по глобальному имени (car, cdr, null?, +, < …), 1 или 2 аргумента.
// При компиляции в ячейке имени лежал builtin `fv`; при каждом вызове проверяется, что он там же (поздняя привязка:
// переопределённое имя → общий CallNode `slow`), и при trace/profile (Debug.hooked) — тоже общий путь. Иначе — без
// вычисления головы через узел, проверки типа функции, кэша реестра; car / cdr / null? — без вызова делегата.
// Результат null быстрого входа — «не обработано»: обычный builtin с УЖЕ вычисленными аргументами (как в CallNode)
type Prim1Node(c: Cell, fv: LispValue, f: LispValue list -> LispValue, op: int, f1: Func<LispValue, LispValue>, arg: Node, slow: CallNode) =
    inherit Node()
    override _.Eval(s) =
        if obj.ReferenceEquals(c.Value, fv) && not Debug.hooked then
            let a = arg.Eval s
            let r =
                match op with
                | 1 -> FastBuiltins.fastCar a
                | 2 -> FastBuiltins.fastCdr a
                | 3 -> FastBuiltins.fastNull a
                | 4 -> FastBuiltins.fastCadr a
                | 5 -> FastBuiltins.fastPair a
                | _ -> f1.Invoke a
            if isUnbound r then slow.CallBuiltinSlow(f, [ a ]) else r
        else slow.Eval s

// Общая схема узла с двумя аргументами; op встраивается в Eval конкретного узла
let inline private prim2Eval (c: Cell) (fv: LispValue) (f: LispValue list -> LispValue) (arg1: Node) (arg2: Node) (slow: CallNode)
                             (s: Scope) ([<InlineIfLambda>] op: LispValue -> LispValue -> LispValue) : LispValue =
    if obj.ReferenceEquals(c.Value, fv) && not Debug.hooked then
        let a = arg1.Eval s
        let b = arg2.Eval s
        let r = op a b
        if isUnbound r then slow.CallBuiltinSlow(f, [ a; b ]) else r
    else slow.Eval s

type Prim2Node(c: Cell, fv: LispValue, f: LispValue list -> LispValue, f2: Func<LispValue, LispValue, LispValue>, arg1: Node, arg2: Node, slow: CallNode) =
    inherit Node()
    override _.Eval(s) = prim2Eval c fv f arg1 arg2 slow s (fun a b -> f2.Invoke(a, b))

// Шаг 21i' (b): cons и целочисленные + - < = — встроенно, без делегата; по узлу на операцию, а не выбор по номеру
// в одном узле: в общем узле временные BigInteger всех операций раздували бы кадр системного стека (узел стоит на пути
// рекурсии, например (+ 1 (f n)), — меньше допустимая глубина) и выбор стоил бы лишних нс
type PrimCons(c: Cell, fv: LispValue, f: LispValue list -> LispValue, arg1: Node, arg2: Node, slow: CallNode) =
    inherit Node()
    override _.Eval(s) = prim2Eval c fv f arg1 arg2 slow s FastBuiltins.fastCons

type PrimAdd(c: Cell, fv: LispValue, f: LispValue list -> LispValue, arg1: Node, arg2: Node, slow: CallNode) =
    inherit Node()
    override _.Eval(s) = prim2Eval c fv f arg1 arg2 slow s FastBuiltins.fastAdd

type PrimSub(c: Cell, fv: LispValue, f: LispValue list -> LispValue, arg1: Node, arg2: Node, slow: CallNode) =
    inherit Node()
    override _.Eval(s) = prim2Eval c fv f arg1 arg2 slow s FastBuiltins.fastSub

type PrimMul(c: Cell, fv: LispValue, f: LispValue list -> LispValue, arg1: Node, arg2: Node, slow: CallNode) =
    inherit Node()
    override _.Eval(s) = prim2Eval c fv f arg1 arg2 slow s FastBuiltins.fastMul

type PrimLt(c: Cell, fv: LispValue, f: LispValue list -> LispValue, arg1: Node, arg2: Node, slow: CallNode) =
    inherit Node()
    override _.Eval(s) = prim2Eval c fv f arg1 arg2 slow s FastBuiltins.fastLt

type PrimNumEq(c: Cell, fv: LispValue, f: LispValue list -> LispValue, arg1: Node, arg2: Node, slow: CallNode) =
    inherit Node()
    override _.Eval(s) = prim2Eval c fv f arg1 arg2 slow s FastBuiltins.fastNumEq

// Узел вызова: Prim1Node / Prim2Node, если голова — глобальное имя, сейчас связанное с builtin с быстрым входом нужной
// арности; иначе CallNode
let private makeCall (headNode: Node) (argNodes: Node[]) (call: CallNode) : Node =
    match headNode with
    // несвязанная ячейка (значение null): сопоставление DU с null бросило бы NullReferenceException
    | :? GlobalRef as g when (argNodes.Length = 1 || argNodes.Length = 2) && not (isUnbound g.Cell.Value) ->
        match g.Cell.Value with
        | LispBuiltin (Builtin f) as fv ->
            match FastBuiltins.table.TryGetValue (box f) with
            | true, fe when argNodes.Length = 1 && not (isNull fe.F1) ->
                let op =
                    match fe.Name with
                    | "car" -> 1
                    | "cdr" -> 2
                    | "null?" -> 3
                    | "cadr" -> 4
                    | "pair?" -> 5
                    | _ -> 0
                Prim1Node(g.Cell, fv, f, op, fe.F1, argNodes.[0], call) :> Node
            | true, fe when argNodes.Length = 2 && not (isNull fe.F2) ->
                let a1, a2 = argNodes.[0], argNodes.[1]
                match fe.Name with
                | "cons" -> PrimCons(g.Cell, fv, f, a1, a2, call) :> Node
                | "+" -> PrimAdd(g.Cell, fv, f, a1, a2, call) :> Node
                | "-" -> PrimSub(g.Cell, fv, f, a1, a2, call) :> Node
                | "*" -> PrimMul(g.Cell, fv, f, a1, a2, call) :> Node
                | "<" -> PrimLt(g.Cell, fv, f, a1, a2, call) :> Node
                | "=" -> PrimNumEq(g.Cell, fv, f, a1, a2, call) :> Node
                | _ -> Prim2Node(g.Cell, fv, f, fe.F2, a1, a2, call) :> Node
            | _ -> call :> Node
        | _ -> call :> Node
    | _ -> call :> Node

// ====================== Компилятор ======================

// Тело из нескольких форм → последовательность (последняя — в хвостовой позиции, если tail)
let rec compile (env: Env) (b: Block) (tail: bool) (expr: LispValue) : Node =
    match expr with
    | LispList (_ :: _) ->
        // Шаг 21d: позиция формы из побочной таблицы ридера (одно обращение на форму при компиляции)
        let p = lookupPos expr
        if isNull p then compileForm env b tail expr
        else
            let saved = curPos
            curPos <- p
            try compileForm env b tail expr
            finally curPos <- saved
    | _ -> compileForm env b tail expr

and compileForm (env: Env) (b: Block) (tail: bool) (expr: LispValue) : Node =
    match expr with
    | LispSym name -> compileSym env b name
    | LispList [] -> ConstNode LispNil :> Node
    | LispList (head :: rest) ->
        match head with
        // (quote x) → x
        | LispSym "quote" ->
            match rest with
            | [x] -> ConstNode x :> Node
            | _ -> failwith "quote: требуется один аргумент"

        // (if cond then [else]) — ветки в хвостовой позиции
        | LispSym "if" ->
            match rest with
            | [c; t] -> If2(compile env b false c, compile env b tail t) :> Node
            | [c; t; e] -> If3(compile env b false c, compile env b tail t, compile env b tail e) :> Node
            | _ -> failwith "if: требуется 2 или 3 аргумента"

        // (define name value) / (define (name params...) body...)
        | LispSym "define" ->
            match rest with
            | LispSym name :: _ when isKeywordName name ->
                failwithf "define: %s — ключевое слово, оно самовычисляется и не может быть именем переменной" name
            | LispList (LispSym name :: _) :: _ when isKeywordName name ->
                failwithf "define: %s — ключевое слово, оно самовычисляется и не может быть именем функции" name
            | [LispSym name; value] ->
                let slot = if b.IsTop then -1 else declare b name false
                // Шаг 21h': имя глобального define в модуле — «модуль::имя» для приватных (определяется ДО компиляции значения)
                let gname = if slot < 0 then definedName name else name
                // LANG.1: define на верхнем уровне, затеняющий builtin, — ошибка (как в модулях):
                // молчаливое переопределение (define (car x) x) ломало вызовы, уже скомпилированные в «быстрый» путь
                if slot < 0 then
                    match env.TryBound gname with
                    | null -> ()
                    | c -> (match c.Value with
                            | LispBuiltin _ -> failwithf "define: имя %s занято встроенной функцией (builtin): переименуйте" gname
                            | _ -> ())
                let v = compile env b false value
                (if slot < 0 then DefineGlobal(env, gname, v, true) :> Node
                 else DefineLocal(slot, v, name, true) :> Node)
            | LispList (LispSym name :: paramList) :: (_ :: _ as bodyForms) ->
                let slot = if b.IsTop then -1 else declare b name false
                let gname = if slot < 0 then definedName name else name
                if slot < 0 then
                    match env.TryBound gname with
                    | null -> ()
                    | c -> (match c.Value with
                            | LispBuiltin _ -> failwithf "define: имя %s занято встроенной функцией (builtin): переименуйте" gname
                            | _ -> ())
                let lam = compileLambda env b "define" gname paramList bodyForms
                (if slot < 0 then DefineGlobal(env, gname, lam, false) :> Node
                 else DefineLocal(slot, lam, name, false) :> Node)
            | _ -> failwith "define: неверный синтаксис"

        // Шаг 21h': (module имя (export ...)) разбирает загрузчик файла (Evaluator.loadIntoEnv) — только первой формой файла
        | LispSym "module" ->
            failwith "module: объявление модуля допустимо только первой формой загружаемого файла: (module имя (export имя ...))"

        // (defrule имя образец замена [условие] [:ac]) — ничего не вычисляется при определении;
        // :ac (Шаг AC.3) — сопоставление через ac-match (AC для + и *, сегментные ?r...)
        | LispSym "defrule" ->
            // опции :ac и :title "заголовок" (Подшаг «заголовки шагов») — после условия, в любом порядке
            let isAc x = (match x with LispSym ":ac" -> true | _ -> false)
            let rec splitOpts (xs: LispValue list) (ac: bool) (title: string) (plain: LispValue list) =
                match xs with
                | [] -> Some (ac, title, List.rev plain)
                | LispSym ":title" :: LispStr t :: more when title = "" -> splitOpts more ac t plain
                | x :: more when isAc x && not ac -> splitOpts more true title plain
                | LispSym ":title" :: _ -> None
                | x :: more -> splitOpts more ac title (x :: plain)
            match rest with
            | LispSym name :: pattern :: replacement :: tail2 ->
                match splitOpts tail2 false "" [] with
                | Some (ac, title, plain) when plain.Length <= 1 ->
                    DefRuleNode(name, pattern, replacement, List.tryHead plain, ac, title, env, curModule) :> Node
                | _ -> failwith "defrule: (defrule имя образец замена [условие] [:ac] [:title \"заголовок\"])"
            | _ -> failwith "defrule: (defrule имя образец замена [условие] [:ac] [:title \"заголовок\"])"

        | LispSym "unwind-protect" ->
            match rest with
            | body :: cleanups ->
                UnwindNode(compile env b false body, cleanups |> List.map (compile env b false) |> Array.ofList) :> Node
            | [] -> failwith "unwind-protect: (unwind-protect тело очистка...)"

        // (defmethod op (t1 t2 ...) (params...) body) — op, типы и параметры не вычисляются
        | LispSym "defmethod" ->
            match rest with
            | LispSym op :: LispList types :: LispList paramList :: (_ :: _ as bodyForms) ->
                let typeNames = types |> List.map (fun t ->
                    match t with LispSym s -> s | _ -> failwith "defmethod: типы должны быть символами")
                let paramNames = paramList |> List.map (fun p ->
                    match p with LispSym s -> s | _ -> failwith "defmethod: параметры должны быть символами")
                if paramNames.Length < typeNames.Length then
                    failwith "defmethod: параметров должно быть не меньше, чем типов"
                let name = op + "(" + String.concat " " typeNames + ")"
                let lam = compileLambdaNames env b name paramNames bodyForms true
                DefMethodNode(op, typeNames, lam, env, curModule) :> Node
            | _ -> failwith "defmethod: (defmethod op (типы...) (параметры...) тело)"

        // (defmacro (name params...) body) — аргументы при вызове НЕ вычисляются
        | LispSym "defmacro" ->
            match rest with
            | LispList (LispSym name :: paramList) :: (_ :: _ as bodyForms) ->
                let paramNames = paramList |> List.choose (fun p -> match p with LispSym s -> Some s | _ -> None)
                if paramNames.Length <> paramList.Length then failwith "defmacro: параметры должны быть символами"
                let slot = if b.IsTop then -1 else declare b name false
                let gname = if slot < 0 then definedName name else name
                let code = makeLambdaCode env b paramNames bodyForms false
                DefMacroNode(code, gname, paramNames, bodyOf bodyForms, env, slot) :> Node
            | _ -> failwith "defmacro: неверный синтаксис"

        // `шаблон — квазицитирование
        | LispSym "quasiquote" ->
            match rest with
            | [template] -> compileQQ env b template 1
            | _ -> failwith "quasiquote: требуется один аргумент"

        // (set! name value) — переприсвоение СУЩЕСТВУЮЩЕЙ переменной
        | LispSym "set!" ->
            match rest with
            | LispSym name :: _ when isKeywordName name ->
                failwithf "set!: %s — ключевое слово, оно самовычисляется и не может быть переменной" name
            | [LispSym name; value] ->
                let v = compile env b false value
                match resolveLocal b name with
                | Some (depth, vi) -> SetLocal(depth, vi.Index, v, name) :> Node
                | None ->
                    let gname = refName name
                    SetGlobal(env.Resolve gname, v, gname) :> Node
            | _ -> failwith "set!: неверный синтаксис"

        // (lambda (params...) body)
        | LispSym "lambda" ->
            match rest with
            | LispList paramList :: (_ :: _ as bodyForms) ->
                compileLambda env b "lambda" "lambda" paramList bodyForms
            | _ -> failwith "lambda: неверный синтаксис"

        // (let ((name val) ...) body) — значения в области ВНЕ let; тело хвостовое
        | LispSym "let" ->
            match rest with
            | LispList bindings :: (_ :: _ as bodyForms) ->
                let pairs = bindings |> List.choose (fun bd ->
                    match bd with LispList [LispSym n; v] -> Some (n, v) | _ -> None)
                if pairs.Length <> bindings.Length then failwith "let: неверный формат bindings"
                let inits = pairs |> List.map (fun (_, v) -> compile env b false v) |> Array.ofList
                let child = Block(b.Fn, b, false)
                let slots = pairs |> List.map (fun (n, _) -> declare child n false) |> Array.ofList
                prepassDefines child bodyForms
                LetNode(slots, inits, compileSeq env child tail bodyForms) :> Node
            // LANG.1: именованный let — (let name ((v init) ...) body...) раскрывается в
            // (letrec ((name (lambda (v ...) body...))) (name init ...)) — уже существующие узлы,
            // поэтому хвостовой вызов (name ...) внутри тела работает без роста стека (TCO)
            | LispSym loopName :: LispList bindings :: (_ :: _ as bodyForms) ->
                if isKeywordName loopName then failwithf "let: %s — ключевое слово" loopName
                let pairs = bindings |> List.choose (fun bd ->
                    match bd with LispList [LispSym n; v] -> Some (n, v) | _ -> None)
                if pairs.Length <> bindings.Length then failwith "let: неверный формат bindings"
                let lamForm = LispList (LispSym "lambda" :: LispList (List.map (fun (n, _) -> LispSym n) pairs) :: bodyForms)
                let callForm = LispList (LispSym loopName :: List.map (fun (_, v) -> v) pairs)
                let expanded = LispList [LispSym "letrec";
                                         LispList [LispList [LispSym loopName; lamForm]];
                                         callForm]
                compile env b tail expanded
            | _ -> failwith "let: неверный синтаксис"

        // (let* ...) — каждое значение видит предыдущие; свой блок на каждую привязку
        // (ленивая компиляция вложенных lambda не должна увидеть более позднее затенение)
        | LispSym "let*" ->
            match rest with
            | LispList bindings :: (_ :: _ as bodyForms) ->
                let mutable cur = b
                let inits = ResizeArray<Node>()
                let slots = ResizeArray<int>()
                for bd in bindings do
                    match bd with
                    | LispList [LispSym n; v] ->
                        inits.Add (compile env cur false v)
                        let child = Block(b.Fn, cur, false)
                        slots.Add (declare child n false)
                        cur <- child
                    | _ -> failwith "let*: неверный формат bindings"
                prepassDefines cur bodyForms
                LetNode(slots.ToArray(), inits.ToArray(), compileSeq env cur tail bodyForms) :> Node
            | _ -> failwith "let*: неверный синтаксис"

        // (letrec ((name val) ...) body) — все имена видны во всех значениях
        | LispSym "letrec" ->
            match rest with
            | LispList bindings :: (_ :: _ as bodyForms) ->
                let pairs = bindings |> List.choose (fun bd ->
                    match bd with LispList [LispSym n; v] -> Some (n, v) | _ -> None)
                if pairs.Length <> bindings.Length then failwith "letrec: неверный формат bindings"
                let child = Block(b.Fn, b, false)
                let slots = pairs |> List.map (fun (n, _) -> declare child n false) |> Array.ofList
                let inits = pairs |> List.map (fun (_, v) -> compile env child false v) |> Array.ofList
                prepassDefines child bodyForms
                LetrecNode(slots, inits, compileSeq env child tail bodyForms) :> Node
            | _ -> failwith "letrec: неверный синтаксис"

        // (begin expr1 expr2 ...) — последний хвостовой
        | LispSym "begin" -> compileSeq env b tail rest

        // (case key ((k1 k2...) expr1 ...) ... (else exprN ...))
        | LispSym "case" ->
            match rest with
            | keyForm :: clauses ->
                let key = compile env b false keyForm
                let datums = ResizeArray<LispValue list>()
                let bodies = ResizeArray<Node>()
                for cl in clauses do
                    match cl with
                    | LispList (LispSym "else" :: (_ :: _ as body)) ->
                        datums.Add (Unchecked.defaultof<LispValue list>)
                        bodies.Add (compileSeq env b tail body)
                    | LispList (LispList ds :: (_ :: _ as body)) ->
                        datums.Add ds
                        bodies.Add (compileSeq env b tail body)
                    | _ -> failwith "case: неверный формат ветки"
                CaseNode(key, datums.ToArray(), bodies.ToArray()) :> Node
            | [] -> failwith "case: требуется ключ"

        // (cond (test1 expr1 ...) ... (else exprN ...))
        | LispSym "cond" ->
            let tests = ResizeArray<Node>()
            let bodies = ResizeArray<Node>()
            for cl in rest do
                match cl with
                | LispList (LispSym "else" :: (_ :: _ as body)) ->
                    tests.Add null
                    bodies.Add (compileSeq env b tail body)
                | LispList (test :: (_ :: _ as body)) ->
                    tests.Add (compile env b false test)
                    bodies.Add (compileSeq env b tail body)
                | _ -> failwith "cond: неверный формат ветки"
            CondNode(tests.ToArray(), bodies.ToArray()) :> Node

        // (try выражение обработчик)
        | LispSym "try" ->
            match rest with
            | [body; handler] -> TryNode(compile env b false body, compile env b false handler) :> Node
            | _ -> failwith "try: (try выражение обработчик)"

        // Шаг 17b: (time выражение), (profile выражение)
        | LispSym "time" ->
            match rest with
            | [body] -> TimeNode(compile env b false body) :> Node
            | _ -> failwith "time: (time выражение)"
        | LispSym "profile" ->
            match rest with
            | [body] -> ProfileNode(compile env b false body) :> Node
            | _ -> failwith "profile: (profile выражение)"

        // (and ...), (or ...) — короткое замыкание; последний хвостовой
        | LispSym "and" ->
            match rest with
            | [] -> ConstNode (LispBool true) :> Node
            | _ -> AndNode(compileForms env b tail rest) :> Node
        | LispSym "or" ->
            match rest with
            | [] -> ConstNode (LispBool false) :> Node
            | _ -> OrNode(compileForms env b tail rest) :> Node

        // --- Обычный вызов (или макрос) ---
        | _ -> compileCall env b tail head rest

    // Остальные значения самоопределённые (числа, строки, bool, nil, объекты, векторы, функции)
    | other -> ConstNode other :> Node

// Символ: локальная переменная (глубина, индекс) или глобальная ячейка
and compileSym (env: Env) (b: Block) (name: string) : Node =
    // ключевое слово :имя (длиннее одного знака) самовычисляется; проверка один раз при компиляции
    if isKeywordName name then ConstNode (LispSym name) :> Node else
    match resolveLocal b name with
    | Some (depth, vi) ->
        if vi.Checked then LocalChecked(depth, vi.Index, name) :> Node
        elif depth = 0 then Local0 vi.Index :> Node
        elif depth = 1 then Local1 vi.Index :> Node
        else LocalN(depth, vi.Index) :> Node
    | None -> GlobalRef(env.Resolve (refName name)) :> Node

// Список форм; все, кроме последней, — нехвостовые
and compileForms (env: Env) (b: Block) (tail: bool) (forms: LispValue list) : Node[] =
    let n = forms.Length
    forms |> List.mapi (fun i f -> compile env b (tail && i = n - 1) f) |> Array.ofList

// Последовательность (неявный begin): пустая → nil
and compileSeq (env: Env) (b: Block) (tail: bool) (forms: LispValue list) : Node =
    match forms with
    | [] -> ConstNode LispNil :> Node
    | [one] -> compile env b tail one
    | _ -> BeginNode(compileForms env b tail forms) :> Node

// Тело из нескольких форм → одна форма (для поля UserFunction.Body)
and bodyOf (forms: LispValue list) : LispValue =
    match forms with
    | [one] -> one
    | many -> LispList (LispSym "begin" :: many)

// Внутренние define (и defmacro) в теле: имена объявляются заранее — семантика letrec*
and prepassDefines (blk: Block) (forms: LispValue list) : unit =
    for f in forms do
        match f with
        | LispList (LispSym "define" :: LispSym n :: _) -> declare blk n true |> ignore
        | LispList (LispSym "define" :: LispList (LispSym n :: _) :: _) -> declare blk n true |> ignore
        | LispList (LispSym "defmacro" :: LispList (LispSym n :: _) :: _) -> declare blk n true |> ignore
        | LispList (LispSym "begin" :: inner) -> prepassDefines blk inner
        | _ -> ()

// Шаблон лямбды: параметры разбираются сразу, тело компилируется при первом вызове
and makeLambdaCode (env: Env) (b: Block) (ps: string list) (bodyForms: LispValue list) (tail: bool) : LambdaCode =
    let code = LambdaCode()
    let restIdx = List.tryFindIndex (fun p -> p = "&rest") ps
    let slotNames =
        match restIdx with
        | None ->
            code.NParams <- ps.Length
            ps
        | Some i ->
            code.NParams <- i
            code.HasRest <- true
            if ps.Length <> i + 2 then
                code.Error <- "&rest: после маркера должно быть ровно одно имя"
                List.take i ps
            else List.take i ps @ [ ps.[i + 1] ]
    code.Pos <- curPos
    code.Top <- curTop
    code.Module <- curModule
    if not (isNull curModule) then curModule.Codes.Add (box code)
    code.Init <- fun () ->
        // тело компилируется лениво — позиция по умолчанию для его форм: место определения функции;
        // область имён — модуль определения (Шаг 21h')
        let saved = curPos
        let savedTop = curTop
        let savedMod = curModule
        curPos <- code.Pos
        curTop <- code.Top
        curModule <- code.Module
        try
            let fn = FnInfo()
            let blk = Block(fn, b, false)
            slotNames |> List.iteri (fun idx p -> blk.Vars.[p] <- VarInfo(idx, false))
            fn.NextSlot <- slotNames.Length
            prepassDefines blk bodyForms
            let body = compileSeq env blk tail bodyForms
            code.FrameSize <- fn.NextSlot
            code.Fast <- (not code.HasRest) && isNull code.Error
            code.Body <- body
        finally
            curPos <- saved
            curTop <- savedTop
            curModule <- savedMod
    code

// (lambda/define (params...) body...): параметры — символы
and compileLambda (env: Env) (b: Block) (who: string) (name: string) (paramList: LispValue list) (bodyForms: LispValue list) : Node =
    let paramNames = paramList |> List.choose (fun p -> match p with LispSym s -> Some s | _ -> None)
    if paramNames.Length <> paramList.Length then failwithf "%s: параметры должны быть символами" who
    compileLambdaNames env b name paramNames bodyForms true

and compileLambdaNames (env: Env) (b: Block) (name: string) (paramNames: string list) (bodyForms: LispValue list) (tail: bool) : Node =
    let code = makeLambdaCode env b paramNames bodyForms tail
    LambdaNode(code, name, paramNames, bodyOf bodyForms, env) :> Node

// Квазицитирование: ,x на depth=1 вычисляется; ,@x на depth=1 внутри списка — вклеивается;
// вложенные ` увеличивают depth
and compileQQ (env: Env) (b: Block) (template: LispValue) (depth: int) : Node =
    let mkList (parts: (bool * Node) list) : Node =
        QQListNode(parts |> List.map fst |> Array.ofList, parts |> List.map snd |> Array.ofList) :> Node
    match template with
    | LispList [LispSym "unquote"; u] ->
        if depth = 1 then compile env b false u
        else mkList [ (false, ConstNode (LispSym "unquote") :> Node); (false, compileQQ env b u (depth - 1)) ]
    | LispList [LispSym "quasiquote"; inner] ->
        mkList [ (false, ConstNode (LispSym "quasiquote") :> Node); (false, compileQQ env b inner (depth + 1)) ]
    | LispList items ->
        let parts =
            items |> List.map (fun it ->
                match it with
                | LispList [LispSym "unquote-splicing"; u] when depth = 1 ->
                    // ,@,b: внутренний unquote снимается
                    let e = match u with LispList [LispSym "unquote"; e2] -> e2 | other -> other
                    (true, compile env b false e)
                | h -> (false, compileQQ env b h depth))
        // шаблон без unquote — константа
        if parts |> List.forall (fun (sp, n) -> not sp && (n :? ConstNode)) then ConstNode template :> Node
        else mkList parts
    | other -> ConstNode other :> Node

// Вызов: макрос (на момент компиляции) раскрывается сразу, иначе — узел вызова
and compileCall (env: Env) (b: Block) (tail: bool) (head: LispValue) (rest: LispValue list) : Node =
    let pos = curPos
    let macroOpt =
        match head with
        | LispSym n when (resolveLocal b n).IsNone ->
            match env.Lookup (refName n) with
            | Some (LispMacro m as mv) -> Some (mv, m)
            | _ -> None
        | _ -> None
    match macroOpt with
    | Some (mv, m) -> compile env b tail (expandMacro mv m rest)
    | None ->
        let headNode = compile env b false head
        let headName = match head with LispSym s -> s | _ -> "<builtin>"
        let argNodes = rest |> List.map (compile env b false) |> Array.ofList
        makeCall headNode argNodes (CallNode(headNode, headName, argNodes, rest, env, b, tail, pos, curTop, curModule))

// Раскрытие «на лету» компилируется без хвостовых вызовов (кадра у макроса нет).
// Подключается явно (Evaluator.newEnv), а не инициализатором модуля
let install () : unit =
    compileThunk <- fun env blk expansion -> makeLambdaCode env blk [] [ expansion ] false

// ====================== Точки входа ======================

// Верхний уровень: выражение компилируется как тело функции без параметров (его let/define
// получают слоты в собственном фрейме); define в корневом блоке — глобальный
// modl — модуль, в области имён которого компилируется форма (загрузка файла модуля); null — глобальный код
let compileTop (modl: ModuleInfo) (env: Env) (expr: LispValue) : Node * int =
    let fn = FnInfo()
    let blk = Block(fn, null, true)
    // Шаг 21d: форма, прочитанная ридером, несёт позиции своих вложенных форм (TopPos); построенная программой — нет
    let savedTop = curTop
    let savedPos = curPos
    let savedMod = curModule
    curTop <- topOf expr
    curPos <- null
    curModule <- modl
    let node =
        try compile env blk false expr
        finally
            curTop <- savedTop
            curPos <- savedPos
            curModule <- savedMod
    node, fn.NextSlot

// Вычисление формы в области имён модуля modl (null — глобальная)
let evalTopIn (modl: ModuleInfo) (expr: LispValue) (env: Env) : LispValue =
    let node, size = compileTop modl env expr
    node.Eval(topFrame size)

// eval / REPL / JSON: всегда глобальная область имён (приватные имена модулей — только квалифицированно)
let evalTop (expr: LispValue) (env: Env) : LispValue = evalTopIn null expr env

// Выражение в области с заданными локальными именами (условия правил: переменные ?x); modl — модуль правила.
// Возвращает узел и размер фрейма; значения имён кладутся в слоты 0..n-1
let compileWithVars (modl: ModuleInfo) (env: Env) (names: string[]) (expr: LispValue) : Node * int =
    let fn = FnInfo()
    let blk = Block(fn, null, false)
    names |> Array.iteri (fun i n -> blk.Vars.[n] <- VarInfo(i, false))
    fn.NextSlot <- names.Length
    let savedMod = curModule
    curModule <- modl
    let node =
        try compile env blk false expr
        finally curModule <- savedMod
    node, fn.NextSlot
