// Шаг 21b: примитивы для lib\mathlang.lisp (быстрый путь входного языка).
// Ячейка имени языка — LispVector из 9 слотов (создаёт m-new-cell в mathlang.lisp):
//   0 имя | 1 значение переменной | 2 состояние: () — не присвоена, #f — присвоена и «замкнута» (символов нет),
//   #t — присвоена и содержит символы (нужно пересчитывать) | 3 «значение принадлежит только этой переменной»
//   (векторы можно менять на месте) | 4 функция языка (вектор замыканий по числу аргументов) или #f | 5.. — сведения о функции.
// Тензор — LispObject типа tensor: Fields = [| вектор формы; вектор компонент (row-major) |].
module MathLangBuiltins

open System.Collections.Generic
open Types
open Builtins

// Шаг 21d: (m-at ast форма) — форма получает позицию формы ast из побочной таблицы (если у неё своей позиции нет);
// возвращает форму. Нужен компилятору AST → Lisp: кадры стека показывают строку исходного .mth
let private mAt (args: LispValue list) : LispValue =
    match args with
    | [src; form] ->
        // AST языка лежит только в слабой таблице; без позиций (anyWeak = false) — одна проверка флага
        let p = weakPosOf src
        if not (isNull p) then
            match form with
            | LispList (_ :: _) when isNull (weakPosOf form) -> setPos form p
            | _ -> ()
        form
    | _ -> failwith "m-at: два аргумента"

let private vFalse = LispBool false
let private vTrue = LispBool true

let private isTensor (o: LispObj) : bool = o.Type = "tensor"

// Содержит ли значение символы (голова списка не считается — как m-free? до шага 21b)
let rec private hasSymbol (v: LispValue) : bool =
    match v with
    | LispSym _ -> true
    | LispList (_ :: tl) -> List.exists hasSymbol tl
    | LispObject o when isTensor o ->
        (match o.Fields.[1] with LispVector d -> Array.exists hasSymbol d | _ -> false)
    | LispObject o when o.Type = "set" ->
        (match o.Fields.[0] with LispVector d -> Array.exists hasSymbol d | _ -> false)
    | _ -> false

// Упоминается ли символ name в значении (голова списка не считается)
let rec private mentions (name: string) (v: LispValue) : bool =
    match v with
    | LispSym s -> s = name
    | LispList (_ :: tl) -> List.exists (mentions name) tl
    | LispObject o when isTensor o ->
        (match o.Fields.[1] with LispVector d -> Array.exists (mentions name) d | _ -> false)
    | LispObject o when o.Type = "set" ->
        (match o.Fields.[0] with LispVector d -> Array.exists (mentions name) d | _ -> false)
    | _ -> false

let private cellOf (who: string) (v: LispValue) : LispValue[] =
    match v with
    | LispVector c when c.Length >= 5 -> c
    | _ -> failwithf "%s: ожидается ячейка" who

let private shapeDims (o: LispObj) : int[] =
    match o.Fields.[0] with
    | LispVector sh -> sh |> Array.map (function LispInteger n -> int n | _ -> 0)
    | _ -> [||]

let private dataOf (o: LispObj) : LispValue[] =
    match o.Fields.[1] with
    | LispVector d -> d
    | _ -> [||]

let private bnd (n: int) = LispInteger (bigint n)

// Проверка индексов по форме (тексты ошибок — как у m-check-idx); возвращает смещение до последнего индекса
let private checkAndOffset (dims: int[]) (idx: LispValue list) : int =
    let mutable off = 0
    let mutable i = 0
    for ix in idx do
        if i >= dims.Length then failwith "индексация: индексов больше, чем измерений"
        match ix with
        | LispInteger n ->
            if n < 1I || n > bigint dims.[i] then
                failwithf "индекс %s вне границ 1..%d" (n.ToString()) dims.[i]
            off <- off * dims.[i] + (int n - 1)
        | _ -> ()
        i <- i + 1
    off

let private allInts (idx: LispValue list) : bool =
    idx |> List.forall (function LispInteger _ -> true | _ -> false)

// (m-ix v i ...) — v[i, ...]: компонента, подтензор (индексов меньше ранга) или невычисленная форма (m-index v i ...)
let private mIx (args: LispValue list) : LispValue =
    match args with
    | LispObject o :: idx when isTensor o && allInts idx ->
        let dims = shapeDims o
        let off = checkAndOffset dims idx
        let k = idx.Length
        if k = dims.Length then (dataOf o).[off]
        else
            let rest = dims.[k..]
            let block = Array.fold (*) 1 rest
            let slice = Array.sub (dataOf o) (off * block) block
            LispObject { Type = "tensor"; Fields = [| LispVector (rest |> Array.map bnd); LispVector slice |] }
    | v :: idx -> LispList (LispSym "m-index" :: v :: idx)
    | [] -> failwith "m-ix: нужен вектор"

// Записать компоненту: copy = копия данных (иначе на месте); все проверки — как в m-assign-elem
let private setElem (t: LispValue) (copy: bool) (name: string) (value: LispValue) (idx: LispValue list) : LispValue =
    match t with
    | LispObject o when isTensor o ->
        let dims = shapeDims o
        if not (allInts idx) then failwith "присваивание элементу: индексы — целые числа"
        if idx.Length <> dims.Length then failwith "присваивание элементу: нужно по одному индексу на каждое измерение"
        (match value with
         | LispObject vo when isTensor vo -> failwith "присваивание элементу: значение элемента — не вектор"
         | _ -> ())
        let off = checkAndOffset dims idx
        let data = if copy then Array.copy (dataOf o) else dataOf o
        data.[off] <- value
        if copy then LispObject { Type = "tensor"; Fields = [| o.Fields.[0]; LispVector data |] } else t
    | _ -> failwithf "%s — не вектор и не матрица, присваивание элемента невозможно" name

let private symName (v: LispValue) : string =
    match v with
    | LispSym s -> s
    | _ -> failwith "ожидалось имя"

let all : (string * LispValue) list = [
    // (make-table) — изменяемая таблица имя → значение; сама таблица — функция:
    // (t 'get имя) → значение или (), (t 'put имя значение), (t 'values) → список значений
    builtin "make-table" (fun _ ->
        let d = Dictionary<string, LispValue>()
        LispBuiltin (Builtin (fun args ->
            match args with
            | [LispSym "get"; LispSym k] ->
                (match d.TryGetValue k with
                 | true, v -> v
                 | _ -> LispNil)
            | [LispSym "put"; LispSym k; v] ->
                d.[k] <- v
                v
            | [LispSym "values"] -> if d.Count = 0 then LispNil else LispList (List.ofSeq d.Values)
            | _ -> failwith "таблица: (t 'get имя), (t 'put имя значение), (t 'values)")))
    // (m-gread ячейка) — значение «замкнутой» переменной (и снятие признака «значение только мое»);
    // иначе сама ячейка (признак «медленный путь»: не присвоена или нужен пересчёт)
    builtin "m-at" mAt
    builtin "m-has-pos?" (fun args ->
        match args with
        | [ast] -> LispBool (not (isNull (weakPosOf ast)))
        | _ -> failwith "m-has-pos?: один аргумент")
    builtin "m-gread" (fun args ->
        match args with
        | [LispVector c as cv] ->
            (match c.[2] with
             | LispBool false ->
                (match c.[3] with LispBool true -> c.[3] <- vFalse | _ -> ())
                c.[1]
             | _ -> cv)
        | _ -> failwith "m-gread: ожидается ячейка")
    // то же без снятия признака владения: чтение для v[i] не выдаёт вектор наружу
    builtin "m-gread-idx" (fun args ->
        match args with
        | [LispVector c as cv] ->
            (match c.[2] with
             | LispBool false -> c.[1]
             | _ -> cv)
        | _ -> failwith "m-gread-idx: ожидается ячейка")
    // (m-gset-closed! ячейка v) — присвоить значение без символов
    builtin "m-gset-closed!" (fun args ->
        match args with
        | [cv; v] ->
            let c = cellOf "m-gset-closed!" cv
            c.[1] <- v
            c.[2] <- vFalse
            c.[3] <- vFalse
            v
        | _ -> failwith "m-gset-closed!: ячейка и значение")
    // (m-cell-store! ячейка v свободно?) — присвоить значение; свободно? — содержит символы
    builtin "m-cell-store!" (fun args ->
        match args with
        | [cv; v; free] ->
            let c = cellOf "m-cell-store!" cv
            c.[1] <- v
            c.[2] <- (match free with LispBool true -> vTrue | _ -> vFalse)
            c.[3] <- vFalse
            v
        | _ -> failwith "m-cell-store!: ячейка, значение, признак")
    // (m-cell-own! ячейка) — значение переменной принадлежит только ей (свежая копия): можно менять на месте
    builtin "m-cell-own!" (fun args ->
        match args with
        | [cv] ->
            let c = cellOf "m-cell-own!" cv
            c.[3] <- vTrue
            LispBool true
        | _ -> failwith "m-cell-own!: ячейка")
    builtin "m-has-symbol?" (fun args ->
        match args with
        | [v] -> LispBool (hasSymbol v)
        | _ -> failwith "m-has-symbol?: один аргумент")
    builtin "m-mentions?" (fun args ->
        match args with
        | [v; LispSym s] -> LispBool (mentions s v)
        | _ -> failwith "m-mentions?: значение и имя")
    builtin "m-real?" (fun args ->
        match args with
        | [LispInteger _ | LispRational _ | LispFloat _] -> vTrue
        | [_] -> vFalse
        | _ -> failwith "m-real?: один аргумент")
    builtin "m-ix" mIx
    // (m-tset t копия? имя значение i ...) — тензор с записанной компонентой (копия или на месте)
    builtin "m-tset" (fun args ->
        match args with
        | t :: copy :: name :: value :: idx ->
            setElem t (match copy with LispBool true -> true | _ -> false) (symName name) value idx
        | _ -> failwith "m-tset: тензор, признак копии, имя, значение, индексы")
    // (m-gtset! ячейка имя значение i ...) — v[i] := значение для глобальной «замкнутой» переменной-тензора:
    // на месте, если вектор принадлежит только этой переменной, иначе копия (после неё вектор принадлежит переменной).
    // Значение, равное значению элемента-выражения с символами, или переменная без значения/с пересчётом —
    // медленный путь: возвращается сама ячейка
    builtin "m-gtset!" (fun args ->
        match args with
        | (LispVector c as cv) :: name :: value :: idx ->
            (match c.[2] with
             | LispBool false when not (hasSymbol value) ->
                let owned = (match c.[3] with LispBool true -> true | _ -> false)
                let r = setElem c.[1] (not owned) (symName name) value idx
                if not owned then
                    c.[1] <- r
                    c.[3] <- vTrue
                value
             | _ -> cv)
        | _ -> failwith "m-gtset!: ячейка, имя, значение, индексы")
]
