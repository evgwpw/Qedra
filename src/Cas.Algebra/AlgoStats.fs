// Единый реестр счётчиков алгоритмов (шаг 21h'). Раньше у каждого алгоритма был свой «безымянный» массив счётчиков
// (probeStats, zippelStats, PolyFactor.stats ...). Теперь группа счётчиков регистрируется под именем, с именами счётчиков;
// значения — по потокам (ThreadLocal): алгебра тестируется параллельно, счётчик принадлежит вызывающему потоку.
// Доступ из Lisp: (algo-stats), (algo-stats-reset); из F#: AlgoStats.snapshot / AlgoStats.reset.
module AlgoStats

open System.Collections.Concurrent
open System.Threading

// Группа счётчиков алгоритма: имя группы, имена счётчиков, значения текущего потока (массив — для быстрых инкрементов
// по константным индексам, как и раньше: st.[ZCalls] <- st.[ZCalls] + 1)
[<Sealed; AllowNullLiteral>]
type StatGroup internal (name: string, counters: string[]) =
    let values = new ThreadLocal<int[]>(fun () -> Array.zeroCreate counters.Length)
    member _.Name = name
    member _.Counters = counters
    member _.Values : int[] = values.Value
    member this.Reset() : unit = System.Array.Clear(this.Values, 0, this.Values.Length)

// Реестр групп (процесс); регистрация идемпотентна: повторная регистрация возвращает ту же группу
let private registry = ConcurrentDictionary<string, StatGroup>()

// Зарегистрировать группу счётчиков; counters — имена по индексам массива Values
let register (name: string) (counters: string[]) : StatGroup =
    registry.GetOrAdd(name, fun _ -> StatGroup(name, counters))

// Все зарегистрированные группы (по имени)
let groups () : StatGroup list =
    registry.Values |> Seq.sortBy (fun g -> g.Name) |> List.ofSeq

let tryFind (name: string) : StatGroup option =
    match registry.TryGetValue name with
    | true, g -> Some g
    | _ -> None

// Значения счётчиков текущего потока: [(группа, [(счётчик, значение)])]; group — только эта группа
let snapshot (group: string option) : (string * (string * int) list) list =
    groups ()
    |> List.filter (fun g -> group.IsNone || group = Some g.Name)
    |> List.map (fun g -> g.Name, [ for i in 0 .. g.Counters.Length - 1 -> g.Counters.[i], g.Values.[i] ])

// Обнулить счётчики текущего потока (все группы или одну); false — такой группы нет
let reset (group: string option) : bool =
    match group with
    | None ->
        for g in groups () do g.Reset()
        true
    | Some name ->
        match tryFind name with
        | Some g -> g.Reset(); true
        | None -> false
