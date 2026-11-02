// Шаг 21e: быстрые входы горячих builtin (вызовы с 1–2 аргументами без построения списка аргументов)
//
// Тип builtin (`Builtin of (LispValue list -> LispValue)`) не менялся. Побочный реестр: ссылка на функцию-builtin
// (объект, лежащий в ячейке имени) → быстрые делегаты Func<LispValue, LispValue> / Func<LispValue, LispValue, LispValue>.
// Компилятор (CallNode) смотрит ТЕКУЩЕЕ значение ячейки при каждом вызове (поздняя привязка сохранена: переопределённое
// пользователем `car` — другой объект, его в реестре нет) и, если у него есть быстрый вход, зовёт его напрямую.
// Контракт делегата: он обрабатывает только «чистый» успешный случай (типы аргументов, при которых обычный builtin не
// бросает исключение и не идёт через диспетчеризацию/упроститель) и возвращает результат; для всего остального
// (ошибки, алгебраические числа, объекты, символьные аргументы) возвращает null — тогда компилятор вызывает обычный
// builtin с уже вычисленными аргументами (кадр стека, сообщения об ошибках, trace/profile — как раньше). Поэтому
// поведение идентично, а Debug.push (кадр builtin) в быстром пути не нужен: исключений в нём не бывает.
module FastBuiltins

open System
open System.Collections.Generic
open System.Numerics
open System.Runtime.CompilerServices
open Types
open Numeric

[<AllowNullLiteral>]
type FastEntry(name: string, f1: Func<LispValue, LispValue>, f2: Func<LispValue, LispValue, LispValue>) =
    member _.Name = name
    member _.F1 = f1
    member _.F2 = f2

// Реестр: заполняется один раз (register) до первого вычисления; после этого только читается
let table = Dictionary<obj, FastEntry>(HashIdentity.Reference)

let vTrue = LispBool true
let vFalse = LispBool false
let inline ofBool (b: bool) : LispValue = if b then vTrue else vFalse
let nul : LispValue = Unchecked.defaultof<LispValue>

// Шаг 21i: сравнения BigInteger — только BigInteger.Compare: операторы F# < > <= >= на BigInteger идут через
// обобщённое сравнение (LanguagePrimitives.HashCompare.GenericLessThan → IComparable.CompareTo(obj), упаковка
// обоих аргументов) — ≈ 50 нс на сравнение против ≈ 5; = (IEquatable) этим не страдает
let inline cmpI (x: BigInteger) (y: BigInteger) : int = BigInteger.Compare(x, y)

// Шаг 21i' (c): малые целые. Внутри System.Numerics.BigInteger значение, умещающееся в int32, хранится прямо в поле
// _sign (поле _bits = null); обычные операции + - * сравнения проходят через общий код (возврат структуры через
// скрытый буфер, проверки обоих операндов): сложение двух малых ≈ 9 нс сверх выделения обёртки LispInteger. Здесь
// «малость» читается прямо из структуры (Unsafe.As на зеркальную структуру: ссылка _bits, затем int _sign — порядок
// полей CoreCLR для структуры с ссылкой), арифметика — на int64 (результат двух int32 не переполняет int64 ни при
// сложении, ни при умножении), результат — BigInteger(int64) (сам вернёт малое или большое представление).
// Раскладка проверяется при регистрации (checkBigIntegerLayout) — несовпадение (другая версия среды выполнения) даёт
// явную ошибку при запуске, а не молчаливо неверную арифметику
[<Struct; NoEquality; NoComparison>]
type BigIntegerView =
    val mutable Bits: obj
    val mutable Sign: int

let inline smallOf (x: BigInteger) (v: byref<int>) : bool =
    let mutable xx = x
    let view = &Unsafe.As<BigInteger, BigIntegerView>(&xx)
    if isNull view.Bits then
        v <- view.Sign
        true
    else false

let checkBigIntegerLayout () : bool =
    let mutable v = 0
    let ok =
        [ 0; 1; -1; 5; -7; Int32.MaxValue; Int32.MinValue ]
        |> List.forall (fun n ->
            let r = smallOf (BigInteger n) &v
            // int.MinValue в BigInteger — большое представление (массив), остальные — малое
            if n = Int32.MinValue then not r || v = n else r && v = n)
        && not (smallOf (BigInteger.Pow(BigInteger 10, 30)) &v)
        && not (smallOf (BigInteger Int64.MaxValue) &v)
        && not (smallOf (BigInteger 4294967296L) &v)
    // WASM.1: в браузере раскладка BigInteger иная — быстрый путь не включаем (общий путь корректен),
    // настольная сборка проверку проходит и работает как раньше
    ok

let inline addInt (x: BigInteger) (y: BigInteger) : BigInteger =
    let mutable a = 0
    let mutable b = 0
    if smallOf x &a && smallOf y &b then BigInteger(int64 a + int64 b) else x + y
let inline subInt (x: BigInteger) (y: BigInteger) : BigInteger =
    let mutable a = 0
    let mutable b = 0
    if smallOf x &a && smallOf y &b then BigInteger(int64 a - int64 b) else x - y
let inline mulInt (x: BigInteger) (y: BigInteger) : BigInteger =
    let mutable a = 0
    let mutable b = 0
    if smallOf x &a && smallOf y &b then BigInteger(int64 a * int64 b) else x * y
// порядок и равенство
let inline cmpInt (x: BigInteger) (y: BigInteger) : int =
    let mutable a = 0
    let mutable b = 0
    if smallOf x &a && smallOf y &b then (if a < b then -1 elif a > b then 1 else 0) else BigInteger.Compare(x, y)
let inline eqInt (x: BigInteger) (y: BigInteger) : bool =
    let mutable a = 0
    let mutable b = 0
    if smallOf x &a && smallOf y &b then a = b else x.Equals y

// Шаг 21i' (a): «чистые» случаи car / cdr / null? — общие для реестра и узлов-примитивов компилятора (Compiler.Prim1Node)
let inline fastCar (v: LispValue) : LispValue =
    match v with
    | LispList (h :: _) -> h
    | LispPair (a, _) -> a
    | _ -> nul
let inline fastCdr (v: LispValue) : LispValue =
    match v with
    | LispList (_ :: t) -> LispList t
    | LispPair (_, b) -> b
    | LispNil -> LispNil
    | _ -> nul
let inline fastNull (v: LispValue) : LispValue =
    match v with
    | LispList [] | LispNil -> vTrue
    | _ -> vFalse
// Шаг 21i' (b): cadr / pair? / cons и целочисленные + - < = — тоже встраиваются в узлы-примитивы
let inline fastCadr (v: LispValue) : LispValue =
    match v with
    | LispList (_ :: h :: _) -> h
    | _ -> nul
let inline fastPair (v: LispValue) : LispValue =
    match v with
    | LispPair _ | LispList (_ :: _) -> vTrue
    | _ -> vFalse
let inline fastCons (h: LispValue) (t: LispValue) : LispValue =
    match t with
    | LispList l -> LispList (h :: l)
    | LispNil -> LispList [h]
    | _ -> LispPair (h, t)
let inline fastAdd (a: LispValue) (b: LispValue) : LispValue =
    match a, b with
    | LispInteger x, LispInteger y -> LispInteger (addInt x y)
    | LispFloat x, LispFloat y -> LispFloat (x + y)
    | _ -> nul
let inline fastSub (a: LispValue) (b: LispValue) : LispValue =
    match a, b with
    | LispInteger x, LispInteger y -> LispInteger (subInt x y)
    | LispFloat x, LispFloat y -> LispFloat (x - y)
    | _ -> nul
let inline fastMul (a: LispValue) (b: LispValue) : LispValue =
    match a, b with
    | LispInteger x, LispInteger y -> LispInteger (mulInt x y)
    | LispFloat x, LispFloat y -> LispFloat (x * y)
    | _ -> nul
let inline fastLt (a: LispValue) (b: LispValue) : LispValue =
    match a, b with
    | LispInteger x, LispInteger y -> ofBool (cmpInt x y < 0)
    | _ -> nul
let inline fastNumEq (a: LispValue) (b: LispValue) : LispValue =
    match a, b with
    | LispInteger x, LispInteger y -> ofBool (eqInt x y)
    | _ -> nul

let private f1 (f: LispValue -> LispValue) = Func<LispValue, LispValue>(f)
let private f2 (f: LispValue -> LispValue -> LispValue) = Func<LispValue, LispValue, LispValue>(f)

// Пути по малой раскладке BigInteger (сложение, вычитание, умножение и сравнения целых). В браузере раскладка
// другая (см. checkBigIntegerLayout), поэтому эти входы там не регистрируются — арифметика идёт общим путём.
// На десктопе несовпадение раскладки остаётся ошибкой запуска (register), а не тихим отключением ускорения.
let private entriesSmallInt : (string * Func<LispValue, LispValue> * Func<LispValue, LispValue, LispValue>) list =
    [
      ("+", null, f2 (fun a b -> fastAdd a b))
      ("-", null, f2 (fun a b -> fastSub a b))
      ("*", null, f2 (fun a b -> fastMul a b))
      ("max", null, f2 (fun a b -> match a, b with LispInteger x, LispInteger y -> (if cmpInt x y >= 0 then a else b) | _ -> nul))
      ("min", null, f2 (fun a b -> match a, b with LispInteger x, LispInteger y -> (if cmpInt x y <= 0 then a else b) | _ -> nul))
      ("<", null, f2 (fun a b -> fastLt a b))
      (">", null, f2 (fun a b -> match a, b with LispInteger x, LispInteger y -> ofBool (cmpInt x y > 0) | _ -> nul))
      ("<=", null, f2 (fun a b -> match a, b with LispInteger x, LispInteger y -> ofBool (cmpInt x y <= 0) | _ -> nul))
      (">=", null, f2 (fun a b -> match a, b with LispInteger x, LispInteger y -> ofBool (cmpInt x y >= 0) | _ -> nul))
      ("=", null, f2 (fun a b -> fastNumEq a b))
    ]

// (имя, быстрый вход с одним аргументом, с двумя); null — нет такой арности
let private entriesPlain : (string * Func<LispValue, LispValue> * Func<LispValue, LispValue, LispValue>) list =
    let pred (name: string) (p: LispValue -> bool) = (name, f1 (fun v -> ofBool (p v)), null)
    [
      // --- списки ---
      ("car", f1 (fun v -> fastCar v), null)
      ("cdr", f1 (fun v -> fastCdr v), null)
      ("cons", null, f2 (fun h t -> fastCons h t))
      ("cadr", f1 (fun v -> fastCadr v), null)
      // шаг 21i: caddr, cddr, nth, length — раньше общий путь (список аргументов, nth через перевод в массив)
      ("caddr", f1 (fun v ->
                match v with
                | LispList (_ :: _ :: h :: _) -> h
                | _ -> nul), null)
      ("cddr", f1 (fun v ->
                match v with
                | LispList (_ :: _ :: t) -> if t.IsEmpty then LispNil else LispList t
                | _ -> nul), null)
      ("nth", null, f2 (fun l i ->
                match l, i with
                | LispList xs, LispInteger n when n.Sign >= 0 && cmpI n (BigInteger 1000000) < 0 ->
                    let rec go (xs: LispValue list) k =
                        match xs with
                        | h :: t -> if k = 0 then h else go t (k - 1)
                        | [] -> nul
                    go xs (int n)
                | _ -> nul))
      ("length", f1 (fun v ->
                match v with
                | LispList xs -> LispInteger (BigInteger xs.Length)
                | LispNil -> LispInteger BigInteger.Zero
                | _ -> nul), null)
      ("list", f1 (fun a -> LispList [a]), f2 (fun a b -> LispList [a; b]))
      ("null?", f1 (fun v -> fastNull v), null)
      pred "not" (function LispBool false -> true | _ -> false)
      ("pair?", f1 (fun v -> fastPair v), null)
      pred "list?" (function LispList _ | LispNil -> true | _ -> false)
      pred "number?" isNumber
      pred "integer?" (function LispInteger _ -> true | _ -> false)
      pred "symbol?" (function LispSym _ -> true | _ -> false)
      pred "vector?" (function LispVector _ -> true | _ -> false)
      pred "m-real?" (function LispInteger _ | LispRational _ | LispFloat _ -> true | _ -> false)
      ("equal?", null, f2 (fun a b -> ofBool (structEqual a b)))
      // --- остальное ---
      ("mod", null, f2 (fun a b ->
                match a, b with
                | LispInteger x, LispInteger y when not y.IsZero -> LispInteger (x % y)
                | _ -> nul))
      // --- векторы ---
      ("vref", null, f2 (fun v i ->
                match v, i with
                | LispVector arr, LispInteger n when n.Sign >= 0 && cmpI n (BigInteger arr.Length) < 0 -> arr.[int n]
                | _ -> nul))
      // ячейка «замкнутой» переменной языка (как m-gread в MathLangBuiltins): значение или признак медленного пути
      ("m-gread", f1 (fun v ->
                match v with
                | LispVector c when c.Length > 3 ->
                    (match c.[2] with
                     | LispBool false ->
                        (match c.[3] with LispBool true -> c.[3] <- vFalse | _ -> ())
                        c.[1]
                     | _ -> v)
                | _ -> nul), null)
    ]

// Регистрация: берём объекты-функции из списка builtin (те же, что кладутся в окружение). Вызывать один раз.
// Замечание ревью 1.2: в браузере отключается только путь малых целых (раскладка BigInteger иная),
// остальные быстрые входы (car/cdr/cons/null?/cadr/предикаты/векторы/mod) работают. На десктопе несовпадение
// раскладки — ошибка запуска, а не тихое отключение ускорения.
let register (all: (string * LispValue) list) : unit =
    let browser = OperatingSystem.IsBrowser()
    let layoutOk = if browser then false else checkBigIntegerLayout ()
    if not browser && not layoutOk then
        failwith
            "FastBuiltins: раскладка BigInteger не совпала с ожидаемой — быстрый путь малых целых отключён, \
             чтобы не считать неверно (проверьте версию среды выполнения)"
    let byName = dict (all |> List.map (fun (n, v) -> (n, v)))
    let install (name: string) (a1: Func<LispValue, LispValue>) (a2: Func<LispValue, LispValue, LispValue>) =
        match byName.TryGetValue name with
        | true, LispBuiltin (Builtin f) -> table.[box f] <- FastEntry(name, a1, a2)
        | _ -> ()
    for (name, a1, a2) in entriesPlain do install name a1 a2
    if layoutOk then
        for (name, a1, a2) in entriesSmallInt do install name a1 a2
