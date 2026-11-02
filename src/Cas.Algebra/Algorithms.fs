// Единый переключатель алгоритмов (шаг 21h'). Раньше — одна переменная окружения LISP_GCD = zippel | brown и тестовая
// функция setZippelMode. Теперь переключатель регистрируется под именем с набором допустимых значений:
//   F#:    Algorithms.gcd.Set "zippel"      Lisp: (set-algorithm 'gcd 'zippel)      язык: set_algorithm(gcd, zippel)
//   среда: LISP_<ИМЯ> (имя заглавными, «-» → «_»): LISP_GCD=zippel — начальное значение переключателя «gcd» в каждом потоке.
// Значение — по потокам (ThreadLocal): алгебра тестируется параллельно; умолчания не изменились (gcd = auto).
module Algorithms

open System
open System.Collections.Concurrent
open System.Threading

[<Sealed; AllowNullLiteral>]
type Switch internal (name: string, values: string[], defaultValue: string) =
    // начальное значение потока: переменная окружения LISP_<ИМЯ>, если она допустима, иначе умолчание
    let initial () : int =
        let env = Environment.GetEnvironmentVariable ("LISP_" + name.ToUpperInvariant().Replace('-', '_'))
        match Array.tryFindIndex ((=) env) values with
        | Some i -> i
        | None -> Array.IndexOf(values, defaultValue)
    let current = new ThreadLocal<int>(fun () -> initial ())
    member _.Name = name
    member _.Values = values
    member _.Default = defaultValue
    // индекс значения в списке Values (быстрый путь: проверка в алгоритме)
    member _.Index : int = current.Value
    member _.Value : string = values.[current.Value]
    // установить значение текущего потока; неизвестное значение — ArgumentException со списком допустимых
    member _.Set(value: string) : unit =
        match Array.tryFindIndex ((=) value) values with
        | Some i -> current.Value <- i
        | None ->
            raise (ArgumentException (sprintf "алгоритм %s: неизвестное значение %s (допустимо: %s)" name value (String.Join(", ", values))))
    // вернуть начальное значение (среда / умолчание)
    member _.Reset() : unit = current.Value <- initial ()

let private registry = ConcurrentDictionary<string, Switch>()

// Зарегистрировать переключатель: values — допустимые значения, defaultValue — одно из них
let register (name: string) (values: string[]) (defaultValue: string) : Switch =
    if not (Array.contains defaultValue values) then
        invalidArg "defaultValue" (sprintf "умолчание %s не входит в %A" defaultValue values)
    registry.GetOrAdd(name, fun _ -> Switch(name, values, defaultValue))

let all () : Switch list = registry.Values |> Seq.sortBy (fun s -> s.Name) |> List.ofSeq

let tryFind (name: string) : Switch option =
    match registry.TryGetValue name with
    | true, s -> Some s
    | _ -> None

// Установить значение переключателя по имени (для Lisp): неизвестный переключатель/значение — исключение с подсказкой
let set (name: string) (value: string) : unit =
    match tryFind name with
    | Some s -> s.Set value
    | None ->
        let known = all () |> List.map (fun s -> s.Name) |> String.concat ", "
        raise (ArgumentException (sprintf "неизвестный алгоритм %s (есть: %s)" name known))

// --- переключатели ---

// НОД многочленов от нескольких переменных (Zippel.zippelWanted): auto — эвристика (Зиппель при n >= 3 переменных и при
// n = 2 с границей степени >= 3), zippel — всегда Зиппель (если есть переменные кроме главной), brown — только Браун
let gcd : Switch = register "gcd" [| "auto"; "zippel"; "brown" |] "auto"

// Базисы Грёбнера (шаг 21i): fsharp — Groebner.fs (по умолчанию), lisp — эталонная Lisp-версия lib\groebner.lisp
// (тот же алгоритм; базисы и счётчики совпадают — проверяется тестом)
let groebner : Switch = register "groebner" [| "fsharp"; "lisp" |] "fsharp"

// Диагностика Бухбергера (шаг 21i'' (1)): off — только дешёвые счётчики; stats — ещё счётчики арифметики коэффициентов
// (ratops, coefbits, maxbits: длины в битах на каждой операции); trace — stats + строка на каждую редукцию S-многочлена
// (stderr в F#, stdout в Lisp). Одинаково в обеих реализациях (LISP_GROEBNER_DIAG).
let groebnerDiag : Switch = register "groebner-diag" [| "off"; "stats"; "trace" |] "off"
