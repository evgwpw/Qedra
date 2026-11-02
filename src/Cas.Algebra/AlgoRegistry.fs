// Инициализация реестров алгоритмов (шаг 21h'). F# инициализирует файлы библиотеки лениво — при первом обращении к
// значениям файла, поэтому счётчики и переключатели алгоритма регистрируются только после первого его запуска. init()
// обращается к каждому из них, чтобы реестры (AlgoStats, Algorithms) были полными до первого запроса (algo-stats) и т. п.
module AlgoRegistry

let init () : unit =
    ModGcd.probeStats () |> ignore
    Zippel.zippelStats () |> ignore
    PolyFactor.stats () |> ignore
    Algorithms.gcd |> ignore
    Algorithms.groebner |> ignore
    Groebner.stats |> ignore
