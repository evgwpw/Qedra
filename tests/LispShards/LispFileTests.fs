// Шаг 15b: Lisp-тесты из tests\lisp\*.lisp — по одному xUnit-кейсу на каждый deftest.
// Имена deftest извлекаются разбором файла Reader'ом; выполнение — в свежем окружении:
// загрузка файла (deftest только регистрирует), затем запуск тела нужного теста.
module LispFileTests

open System.IO
open Xunit
open Types
open Reader
open Evaluator

let private lispDir = Path.Combine(System.AppContext.BaseDirectory, "lisp")

// Шаг 21h': медленные Lisp-тесты (> 3 с в Debug) вынесены во вторую теорию с признаком Category=Slow
// (xUnit не умеет помечать отдельные строки MemberData): быстрый набор — --filter "Category!=Slow"
let private slowCases : Set<string * string> =
    set [ "ratint.lisp", "случайные: Π f^k и случайные числители — производная первообразной"
          // ускорение тестов: > 1,4 с каждый (Debug)
          "limit.lisp", "пределы: Грунц берёт то, что старый каскад не брал (x → +∞)"
          "limit.lisp", "пределы: перекрёстная проверка classic и gruntz — где отвечают оба, ответы совпадают"
          "groebner.lisp", "fglm: katsura-5 (5 переменных) и cyclic-5 — инварианты lex-базиса"
          "curves.lisp", "parametrize-curve: астроида (x²+y²−1)³ + 27x²y² = 0 — каспы r=2, адъюнкты" ]

// Тесты: параллельные процессы. Этот файл компилируется в проекты-осколки Lisp.Tests.Lisp1..shardCount (tests\LispShards\Shard.props):
// каждая сборка — отдельный процесс vstest; осколок выполняет только свою долю пар (файл, имя), так что глобальное
// состояние интерпретатора остаётся в своём процессе. Раздел детерминирован (одинаков во всех процессах):
// единицы — файлы целиком (окружение файла строится один раз), плюс «тяжёлые» отдельные тесты, закреплённые за
// разными осколками; жадное распределение по убыванию веса. Веса — замеры trx (с), остальные файлы — вес 1.
let private shardCount = 4

let private heavyCases : (string * string * float) list =
    // curves.lisp: два теста ≈ 20–30 с каждый (Debug, замер 2026-10-25) — на разные осколки
    [ "curves.lisp", "singular-points: астроид", 25.0
      "curves.lisp", "curve-genus: астроид", 25.0 ]

let private fileWeights : Map<string, float> =
    // замер trx 2026-10-25 (с, Debug)
    Map [ "intdiv.lisp", 16.0; "risch.lisp", 24.5; "puiseux.lisp", 22.2; "curves.lisp", 20.0; "intalg.lisp", 10.0
          "summation.lisp", 13.8; "ratint.lisp", 6.2; "genus0.lisp", 5.1; "interval.lisp", 4.8; "integrate.lisp", 4.6
          "limit.lisp", 3.0; "intbasis.lisp", 6.0; "galois.lisp", 35.0; "groebner.lisp", 2.5; "solve.lisp", 2.3; "forms.lisp", 2.3 ]

// Номер осколка (0-based) — по имени сборки «Lisp.Tests.LispK»; без номера (-1) — выполнять всё
let private shardIndex : int =
    let n = System.Reflection.Assembly.GetExecutingAssembly().GetName().Name
    let tail = n |> Seq.rev |> Seq.takeWhile System.Char.IsDigit |> Seq.rev |> Seq.toArray |> System.String
    if tail = "" then -1 else int tail - 1

// файл → осколок
let private fileShard : Map<string, int> =
    let loads = Array.zeroCreate<float> shardCount
    heavyCases |> List.iteri (fun i (_, _, w) -> loads[i % shardCount] <- loads[i % shardCount] + w)
    // медленные тоже нагружают свой осколок (slowIndex — по кругу): грубые веса по замеру trx 2026-10-25
    Set.toList slowCases |> List.iteri (fun i (f, _) ->
        let w = match f with "curves.lisp" -> 25.0 | "ratint.lisp" -> 6.0 | _ -> 2.0
        loads[i % shardCount] <- loads[i % shardCount] + w)
    Directory.GetFiles(lispDir, "*.lisp")
    |> Array.map Path.GetFileName
    |> Array.sortBy (fun f -> -(Map.tryFind f fileWeights |> Option.defaultValue 1.0), f)
    |> Array.fold (fun (m: Map<string, int>) f ->
        let k = loads |> Array.indexed |> Array.minBy snd |> fst
        loads[k] <- loads[k] + (Map.tryFind f fileWeights |> Option.defaultValue 1.0)
        m.Add(f, k)) Map.empty

// медленные тесты — по одному на осколок (по кругу в порядке множества): у каждого осколка непустая теория
// «Lisp-тест (медленный)» и общее число строк не зависит от разбиения
let private slowIndex (c: string * string) = Set.toList slowCases |> List.tryFindIndex ((=) c)

let private inShard (file: string, name: string) =
    shardIndex < 0
    || (match heavyCases |> List.tryFindIndex (fun (f, p, _) -> f = file && name.StartsWith p) with
        | Some i -> i % shardCount = shardIndex
        | None ->
            match slowIndex (file, name) with
            | Some i -> i % shardCount = shardIndex
            | None -> fileShard[file] = shardIndex)

// Все пары (файл, имя теста) этого осколка: формы верхнего уровня вида (deftest "имя" ...)
let private allCases () : (string * string) list =
    Directory.GetFiles(lispDir, "*.lisp")
    |> Array.sort
    |> List.ofArray
    |> List.collect (fun path ->
        readAll (File.ReadAllText path)
        |> List.choose (function
            | LispList (LispSym "deftest" :: LispStr name :: _) -> Some (Path.GetFileName path, name)
            | _ -> None))
    |> List.filter inShard

let cases () : seq<obj[]> =
    allCases () |> Seq.filter (fun c -> not (slowCases.Contains c)) |> Seq.map (fun (f, n) -> [| box f; box n |])

// Теория без строк xUnit считает ошибкой: если медленных тестов меньше осколков — одна пустая строка-заглушка ("", "")
let slowOnly () : seq<obj[]> =
    match allCases () |> List.filter slowCases.Contains with
    | [] -> Seq.singleton [| box ""; box "" |]
    | l -> l |> Seq.map (fun (f, n) -> [| box f; box n |])

// Ускорение тестов: окружение (newEnv — основная стоимость короткого теста) и загрузка файла — один раз на файл,
// тесты одного файла идут последовательно (xunit.runner.json); тесты не делят состояние (правило 9 STATUS).
// Если файл не загрузился — ошибка запоминается и показывается в каждом его тесте.
let private fileEnvs = System.Collections.Generic.Dictionary<string, Result<Env, exn>>()

let private envFor (file: string) : Env =
    lock fileEnvs (fun () ->
        // порядок (FileOrderer) — по файлам: окружения прочих файлов больше не нужны, освобождаем память
        for k in List.ofSeq fileEnvs.Keys do
            if k <> file then fileEnvs.Remove k |> ignore
        let r =
            match fileEnvs.TryGetValue file with
            | true, r -> r
            | _ ->
                let r =
                    try
                        let env = newEnv ()
                        loadIntoEnv (Path.Combine(lispDir, file)) env |> ignore
                        Ok env
                    with ex -> Error ex
                fileEnvs[file] <- r
                r
        match r with
        | Ok env -> env
        | Error ex -> raise ex)

let private runLispTest (file: string) (name: string) =
    if file <> "" then
        try
            let env = envFor file
            match env.Lookup "run-test" with
            | Some runTest -> apply runTest [ LispStr name ] |> ignore
            | None -> Assert.Fail "run-test не определён (lib\test.lisp не загружен?)"
        with
        | ex -> Assert.Fail(file + ": " + name + "\n" + Debug.formatError (Debug.wrap ex))

[<Theory>]
[<MemberData(nameof cases)>]
let ``Lisp-тест`` (file: string, name: string) = runLispTest file name

[<Theory>]
[<Trait("Category", "Slow")>]
[<MemberData(nameof slowOnly)>]
let ``Lisp-тест (медленный)`` (file: string, name: string) = runLispTest file name

// Порядок выполнения — по (файл, имя): в процессе одновременно живёт одно окружение файла (см. envFor).
// По умолчанию xUnit упорядочивает кейсы по хешу идентификатора, то есть вперемешку.
// Подключается атрибутом сборки из Shard.props (имя сборки у каждого осколка своё).
type FileOrderer() =
    interface Xunit.Sdk.ITestCaseOrderer with
        member _.OrderTestCases<'T when 'T :> Xunit.Abstractions.ITestCase>(cases: seq<'T>) : seq<'T> =
            let key (c: 'T) =
                match c.TestMethodArguments with
                | [| :? string as f; :? string as n |] -> f, n
                | _ -> "", c.DisplayName
            cases |> Seq.sortBy key |> Seq.toList :> seq<'T>
