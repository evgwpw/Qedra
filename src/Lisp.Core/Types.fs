// Типы Lisp-значений — S-выражения и числовая башня
module Types

open System.Numerics

// Шаг 21d: позиция формы в исходнике (имя файла или псевдоимя «<repl>»/«<json>», строка и столбец с 1).
// Класс, а не запись: null означает «позиция неизвестна»
// Позиции интернируются (одна на (файл, строка, столбец)) и получают номер Id > 0: кадр стека хранит только int —
// запись ссылки в массив кадров (барьер записи GC, лишнее поле) замедляла вызовы функций на ~20 %.
// Реестр ограничен числом РАЗЛИЧНЫХ позиций (размером исходников), а не числом прочитанных форм
[<AllowNullLiteral>]
type SrcPos private (file: string, line: int, col: int, id: int) =
    static let table = System.Collections.Generic.Dictionary<struct (string * int * int), SrcPos>()
    static let byId = System.Collections.Generic.List<SrcPos>([ null ])
    member _.File = file
    member _.Line = line
    member _.Col = col
    member _.Id = id
    override _.ToString() = file + ":" + string line
    static member Make(file: string, line: int, col: int) : SrcPos =
        match table.TryGetValue(struct (file, line, col)) with
        | true, p -> p
        | _ ->
            let p = SrcPos(file, line, col, byId.Count)
            byId.Add p
            table.[struct (file, line, col)] <- p
            p
    // Позиция по номеру (0 — неизвестна → null)
    static member ById(id: int) : SrcPos = byId.[id]

// Шаг 21d: прочитанный ридером текст: имя, начала строк и индексы символов, с которых начинаются списочные формы
// (в порядке открытия скобки/знака '), «номер» формы = её порядковый номер в этом массиве)
[<AllowNullLiteral>]
type SrcFile(name: string, lineStarts: int[]) =
    member _.Name = name
    member val Starts : int[] = null with get, set      // заполняется по окончании чтения
    member this.PosOfRank(rank: int) : SrcPos =
        let idx = this.Starts.[rank]
        let k = System.Array.BinarySearch(lineStarts, idx)
        let line = if k >= 0 then k else ~~~k - 1
        SrcPos.Make(name, line + 1, idx - lineStarts.[line] + 1)

// Шаг 21h' (бывший шаг 23): модуль библиотеки Lisp. Файл начинается с (module имя (export f g ...)); определения файла
// (define, defmacro) принадлежат модулю. Экспортированные имена — обычные глобальные; неэкспортированные — ПРИВАТНЫЕ:
// привязываются к ячейке «модуль::имя», а ссылки на них внутри модуля разрешает компилятор. Извне доступны только
// квалифицированно (модуль::имя). Несколько файлов могут быть частями одного модуля (одинаковое имя в заголовке)
[<AllowNullLiteral>]
type ModuleInfo(name: string) =
    member _.Name = name
    // экспортированные (глобальные) имена
    member val Exports = System.Collections.Generic.HashSet<string>()
    // имена, определённые в модуле и не экспортированные (хранятся как «имя модуля::имя»)
    member val Private = System.Collections.Generic.HashSet<string>()
    // глобальные имена, на которые ссылается скомпилированный код модуля (проверка экспорта: Evaluator.checkModules)
    member val GlobalRefs = System.Collections.Generic.HashSet<string>()
    // файлы, составляющие модуль
    member val Files = System.Collections.Generic.List<string>()
    // шаблоны лямбд (LambdaCode), созданные при компиляции кода модуля: тела вложенных лямбд компилируются лениво,
    // проверка экспорта (Evaluator.checkModules) принудительно компилирует их все
    member val Codes = System.Collections.Generic.List<obj>()
    // квалифицированное имя приватной привязки
    member _.Qualify(n: string) : string = name + "::" + n

// Шаг 17b: ячейка глобальной переменной. Значение null — «не связана» (ячейка создаётся при первом
// упоминании имени компилятором, чтобы код ссылался на неё напрямую; define меняет значение ячейки)
[<AllowNullLiteral>]
type Cell(name: string, owner: Env) =
    member _.Name = name
    member _.Owner = owner
    [<DefaultValue(false)>]
    val mutable Value : LispValue

// Окружение — таблица ячеек (имя → ячейка) со ссылкой на родителя.
// Корневое окружение (Parent = null) — глобальная таблица; дочернее (Extend) — для тестов/вложенных областей.
// Локальные переменные функций (лексическая адресация) живут во фреймах Scope и сюда не попадают.
and [<AllowNullLiteral>] Env(parent: Env) =
    let table = System.Collections.Generic.Dictionary<string, Cell>()
    // Шаг 21h': модули, загруженные в это окружение (в корневом); у дочернего окружения — таблица корня
    let modules = if isNull parent then System.Collections.Generic.Dictionary<string, ModuleInfo>() else null
    let owners = if isNull parent then System.Collections.Generic.Dictionary<string, string>() else null
    // Подшаг 22.4: декларации доменов сессии — алист ((x D ...) ...) (lib\domain.lisp, builtins decl-table/decl-table-set!);
    // состояние корневого окружения, у дочернего — таблица корня
    let mutable decls : LispValue = LispList []
    member _.Parent = parent

    member this.Decls
        with get () : LispValue = if isNull parent then decls else parent.Decls
        and set (v: LispValue) = if isNull parent then decls <- v else parent.Decls <- v

    member this.Modules : System.Collections.Generic.Dictionary<string, ModuleInfo> =
        if isNull parent then modules else parent.Modules

    // Владельцы глобальных определений, не привязанных к ячейкам (методы defmethod, правила defrule): ключ → имя модуля.
    // Нужны для обнаружения конфликтов между модулями библиотеки
    member this.Owners : System.Collections.Generic.Dictionary<string, string> =
        if isNull parent then owners else parent.Owners

    // Все ячейки этого окружения (без родителей): для диагностики модулей
    member _.OwnCells : seq<Cell> = table.Values :> seq<Cell>

    // Своя ячейка имени (создаётся несвязанной, если ещё нет)
    member this.OwnCell(name: string) : Cell =
        match table.TryGetValue name with
        | true, c -> c
        | _ ->
            let c = Cell(name, this)
            table.[name] <- c
            c

    // Ячейка для компилятора: первая СВЯЗАННАЯ по цепочке окружений; иначе своя (несвязанная) ячейка
    member this.Resolve(name: string) : Cell =
        let mutable e = this
        let mutable found : Cell = null
        while isNull found && not (isNull e) do
            match e.TryBound name with
            | null -> e <- e.Parent
            | c -> found <- c
        if isNull found then this.OwnCell name else found

    // Связанная ячейка в этом окружении (без поиска по родителям) или null
    member _.TryBound(name: string) : Cell =
        match table.TryGetValue name with
        | true, c when not (obj.ReferenceEquals(c.Value, null)) -> c
        | _ -> null

    member this.Lookup(name: string) : LispValue option =
        match this.TryBound name with
        | null -> if isNull parent then None else parent.Lookup name
        | c -> Some c.Value

    // Мутирует текущее окружение, возвращает его же
    member this.Define(name: string) (value: LispValue) : Env =
        (this.OwnCell name).Value <- value
        this

    // Переприсваивает СУЩЕСТВУЮЩУЮ переменную (set!): ищем по цепочке окружений
    // Возвращает true если нашли, false если переменной нет
    member this.SetExisting(name: string) (value: LispValue) : bool =
        match this.TryBound name with
        | null -> if isNull parent then false else parent.SetExisting name value
        | c ->
            c.Value <- value
            true

    member this.Extend(pairs: (string * LispValue) list) : Env =
        let e = Env(this)
        for (k, v) in pairs do e.Define k v |> ignore
        e

    static member Empty () = Env(null)

// Фрейм вызова функции (лексическая адресация) — массив LispValue[] (сокращение Scope ниже): значения параметров и
// локальных переменных (let/define внутри тела тоже лежат здесь — «плоский» фрейм), ПОСЛЕДНИЙ элемент — вызванная
// функция (LispFunc/LispMacro; её Captured — фрейм определения, т.е. родитель для замыкания) или LispNil (фрейм
// верхнего уровня, родителя нет). По нему же стек Debug узнаёт имя кадра — имя в кадр отдельно не пишется.
// Шаг 21i' (b): раньше фрейм был объектом Scope(Slots, Parent) — второе выделение памяти на каждый вызов

// Узел предкомпилированного дерева (Compiler.fs); аргумент — фрейм (Scope)
and [<AbstractClass; AllowNullLiteral>] Node() =
    abstract Eval : LispValue[] -> LispValue

// Шаблон лямбды: тело компилируется лениво при первом вызове (Init) — тогда макрос,
// определённый после функции, но до её первого вызова, уже раскрывается
and [<AllowNullLiteral>] LambdaCode() =
    member val Body : Node = null with get, set
    member val FrameSize : int = 0 with get, set
    member val NParams : int = 0 with get, set          // позиционные параметры (без &rest)
    member val HasRest : bool = false with get, set
    member val Error : string = null with get, set      // неверный список параметров (&rest) — ошибка при вызове
    member val Fast : bool = false with get, set        // скомпилировано, без &rest и ошибок
    member val Init : (unit -> unit) = ignore with get, set
    member val Pos : SrcPos = null with get, set        // Шаг 21d: где определена функция (null — неизвестно)
    member val Top : TopPos = null with get, set        // Шаг 21d: верхнеуровневая форма определения — для позиций форм тела
    member val Module : ModuleInfo = null with get, set // Шаг 21h': модуль определения (null — глобальный код): правила разрешения имён тела

// Шаг 21d: верхнеуровневая форма, прочитанная ридером: файл и номер первой её списочной формы (BaseRank).
// Вложенные формы нумеруются при обходе в порядке открытия (список — сам, затем элементы; вектор #(...) тоже занимает
// номер), как и при чтении; индекс «форма → номер» строится лениво при первом запросе вложенной формы
and [<AllowNullLiteral>] TopPos(file: SrcFile, baseRank: int, form: LispValue) =
    let mutable index : System.Collections.Generic.Dictionary<LispValue, int> = null
    member _.File = file
    member _.Form = form
    member _.RankOf(v: LispValue) : int =
        if obj.ReferenceEquals(v, form) then baseRank
        else
            if isNull index then
                index <- System.Collections.Generic.Dictionary<LispValue, int>(HashIdentity.Reference)
                let rank = ref baseRank
                let rec walk (x: LispValue) =
                    match x with
                    | LispList items ->
                        index.[x] <- rank.Value
                        rank.Value <- rank.Value + 1
                        for it in items do walk it
                    | LispVector arr ->
                        rank.Value <- rank.Value + 1
                        for it in arr do walk it
                    | _ -> ()
                walk form
            match index.TryGetValue v with
            | true, r -> r
            | _ -> -1
    member this.PosOf(v: LispValue) : SrcPos =
        let r = this.RankOf v
        if r < 0 || isNull file.Starts then null else file.PosOfRank r

and LispRational = bigint * bigint

and LispValue =
    | LispInteger of BigInteger
    | LispRational of LispRational
    | LispFloat of double
    | LispComplex of (LispValue * LispValue)
    // Алгебраическое число: (многочлен, изолирующий интервал)
    // poly = bigint list — коэффициенты от старшей степени к младшей (формат builtins poly-*)
    // (bigint*bigint) — нижняя граница (числитель, знаменатель > 0)
    // (bigint*bigint) — верхняя граница (числитель, знаменатель > 0)
    | LispAlgebraic of (bigint list * (bigint * bigint) * (bigint * bigint))
    | LispBool of bool
    | LispStr of string
    | LispSym of string
    | LispNil
    | LispList of LispValue list
    | LispFunc of UserFunction
    | LispBuiltin of BuiltinFunction
    // Макрос: Params — имена, Body — шаблон, аргументы НЕ вычисляются при вызове
    | LispMacro of UserFunction
    // Шаг 14: помеченный объект пользовательского типа (неизменяемый с точки зрения Lisp)
    | LispObject of LispObj
    // Шаг 14: вектор-массив (хранилище компонент, O(1) доступ; vset! изменяет на месте)
    | LispVector of LispValue[]
    // Шаг 21d: точечная пара (a . b) — создаётся только `cons` с НЕ списочным вторым аргументом и ридером «(a . b)».
    // Прочий код (simplify, MPoly, порядок, хеш, печать выражений) трактует пару как атом
    | LispPair of LispValue * LispValue

and LispObj = { Type: string; Fields: LispValue[] }

and UserFunction =
    { // Шаг 15b: имя для стека вызовов и печати ("lambda" — безымянная)
      Name: string
      Params: string list
      Body: LispValue
      Env: Env
      // Шаг 17b: шаблон скомпилированного тела (общий для копий) и фрейм определения (замыкание; null — нет)
      Code: LambdaCode
      Captured: LispValue[] }

and BuiltinFunction =
    | Builtin of (LispValue list -> LispValue)

// Фрейм вызова (см. Node): слоты и последним элементом — вызванная функция (или LispNil)
type Scope = LispValue[]

// Подшаг 22.4: окружение (сессия), в котором идёт вычисление. Evaluator.eval переключает его на входе самого внешнего
// вызова, AgentApi — в начале запроса. По нему builtins decl-table / decl-table-set! находят декларации доменов сессии:
// функции библиотеки (методы, правила, defrule-условия) — общие для процесса замыкания последнего созданного окружения,
// поэтому таблицу нельзя держать в переменной модуля — только в состоянии текущей сессии
[<Sealed; AbstractClass>]
type ActiveSession private () =
    static member val Env : Env = null with get, set

// Шаг 21d: позиции списочных форм — ПОБОЧНЫЕ таблицы по ссылке на объект формы (представление LispValue не меняется).
// Ридер запоминает только индексы символов (в порядке открытия скобок) и регистрирует в ConditionalWeakTable лишь
// ВЕРХНЕУРОВНЕВЫЕ формы (запись TopPos). Позиция вложенной формы вычисляется лениво при компиляции: форма обходится
// в том же порядке, что и чтение (номер = порядок открытия) — см. TopPos.PosOf.
// Почему так: у ConditionalWeakTable каждая запись — GC-хэндл, и запись на КАЖДУЮ форму (десятки тысяч в prelude)
// замедляла все сборки мусора (аллоцирующие бенчмарки +20 %); строгий Dictionary вместо неё протекал бы при каждом
// новом окружении (тесты и сессии перечитывают prelude). Здесь стоимость чтения — один int на скобку и одна запись
// на форму верхнего уровня, а записи живут ровно столько, сколько сама форма
let private topPositions = System.Runtime.CompilerServices.ConditionalWeakTable<LispValue, TopPos>()

// Слабая таблица отдельных форм с готовой позицией: AST входного языка (MathReader) и формы, сгенерированные
// компилятором языка (m-at). Записей немного
let private weakPositions = System.Runtime.CompilerServices.ConditionalWeakTable<LispValue, SrcPos>()
let mutable private anyWeak = false

// Запомнить позицию отдельной формы (слабая таблица)
let setPos (form: LispValue) (pos: SrcPos) : unit =
    anyWeak <- true
    weakPositions.AddOrUpdate(form, pos)

// Позиция из слабой таблицы или null
let weakPosOf (v: LispValue) : SrcPos =
    if not anyWeak then null
    else
        match weakPositions.TryGetValue v with
        | true, p -> p
        | _ -> null

// Зарегистрировать форму верхнего уровня, прочитанную ридером
let registerTop (form: LispValue) (top: TopPos) : unit = topPositions.AddOrUpdate(form, top)

// Описание прочитанной верхнеуровневой формы или null (форма построена программой / вложенная)
let topOf (form: LispValue) : TopPos =
    match topPositions.TryGetValue form with
    | true, t -> t
    | _ -> null

// Позиция формы (верхнеуровневой или из слабой таблицы) или null
let posOf (v: LispValue) : SrcPos =
    match topPositions.TryGetValue v with
    | true, t -> t.PosOf v
    | _ ->
        match v with
        | LispList (_ :: _) -> weakPosOf v
        | _ -> null

// Шаг 15b: кадр стека вызовов Lisp (имя функции + вычисленные аргументы)
// Шаг 21d: Pos — где находится вызывающая форма (null — неизвестно)
type Frame = { Name: string; Args: LispValue list; Pos: SrcPos }

// Шаг 15b: ошибка Lisp со снимком стека кадров (самый глубокий кадр — первый) и данными (raise)
exception LispError of message: string * stack: Frame list * data: LispValue
    with override this.Message = this.message
