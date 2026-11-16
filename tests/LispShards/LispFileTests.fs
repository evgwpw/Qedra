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

// Тесты: параллельные процессы. Этот файл компилируется в проекты-осколки Lisp.Tests.Lisp1..shardCount (tests\LispShards\Shard.props):
// каждая сборка — отдельный процесс vstest; осколок выполняет только свою долю пар (файл, имя), так что глобальное
// состояние интерпретатора остаётся в своём процессе. Раздел детерминирован (одинаков во всех процессах):
// единицы — файлы целиком (окружение файла строится один раз) и «тяжёлые» отдельные тесты (heavyCases, свой осколок
// у каждого); жадное распределение по убыванию веса (LPT). Веса — замеры trx в секундах (Debug), остальные файлы — вес 1.
// Пересчёт весов: прогнать осколки с --logger trx, затем `node tools/tests/profile.mjs <каталог trx>` (топ тестов и файлов).
let private shardCount = 4

// Тяжёлые тесты (≥ 9 с, замер 2026-11-16, Debug): отдельные единицы раздачи и категория Slow (см. slowCases).
// Вес файла в fileWeights — без них.
let private heavyCases : (string * string * float) list =
    [ "curves.lisp", "parametrize-curve: астроида (x²+y²−1)³ + 27x²y² = 0 — каспы r=2, адъюнкты", 39.0
      "ode-specfun.lisp", "ODE.9: покрытие — 6 построенных (ν, α, m) класса (Б) и 6 класса (Э)", 38.0
      "risch.lisp", "INT.FIX2.b/риш: производные log(рациональная от exp(c·x)) — не «неэлементарны»", 36.0
      "intalg.lisp", "intalg: √(x³+1) и 1/√(x³+x+1) — без неверных ответов", 35.0
      "integrate-steps.lisp", "шаги Риша: ST.1c —сертификат закона сложения на E в шаге главности (порядок 7, порядок 1, не кручение)", 35.0
      "definite-jumps.lisp", "1/(sin⁴+cos⁴) на [0,2π] = 2√2π (регрессия: был 0)", 30.0
      "definite.lisp", "Ньютон — Лейбниц: расходящиеся ∫₁⁴ dx/sin²x и ∫₀² tan x остаются невычисленными", 28.0
      "definite-jumps.lisp", "1/(sin⁶+cos⁶) на [0,2π], [0,π], [0,π/2]: верно или отказ", 27.0
      "intdiv.lisp", "intdiv: R5.2 — таблицы Жюши и орбиты Фробениуса: Σ(1+χ(P(a))) = dv-count-generic, x примитивен", 26.0
      "integrate-steps.lisp", "шаги Риша: проверяемость — R(t) разложен, m, точки над F_p, n | B, L(−n·δ), результат не изменился", 25.0
      "curves.lisp", "curve-genus: астроид (x²+y²−1)³ + 27x²y² — g = 0", 23.0
      "ansatz.lisp", "ansatz/8: условие risch-nonelementary от сертификата — в integrate; у элементарных его нет", 22.0
      "curves.lisp", "singular-points: астроид — 4 вещественные каспиды δ=1", 22.0
      "complex-analysis.lisp", "ca.c: запасной путь integrate — период тригонометрии", 21.0
      "rubi-ell1.lisp", "rubi-ell1/3: (A + B x^2)/(b x^2 + c x^4)^(3/2) (1.1.4.3/156) — без 0^(-1), верно при x < 0 и x > 0", 20.0
      "risch.lisp", "INT.FIX2.b/риш: hebisch/6763 — «не знаю» или ответ, но не «неэлементарен»", 20.0
      "complex-analysis.lisp", "ca.b: integrate не отдаёт главное значение как обычный ответ", 19.0
      "multiint.lisp", "multiint: кратный integrate-multi — порядок диапазонов и переменные пределы", 18.0
      "prob.lisp", "prob: среднее и дисперсия — таблица = общий движок (sum/integrate), точно", 18.0
      "prob.lisp", "prob: нормировка — сумма/интеграл плотности = 1 (два набора параметров на распределение)", 17.0
      "definite-jumps.lisp", "полюс подынтегральной внутри отрезка: 1/(sin x + cos x) на [0,3] — не значение", 15.0
      "definite.lisp", "integrate: ∫₀² tan x расходится (полюс π/2), а не −log cos 2; ∫₀¹ tan x = −log cos 1", 15.0
      "definite.lisp", "integrate: ветви — log(x−1) на [0, 3] и (x−1)^{−1/3} на [0, 2] не дают комплексного «значения»", 14.0
      "cantor.lisp", "cantor R5.3b: шаги — Кантор в brief (порядок, q, над ℚ, таблица), английский без русских букв, ответ не меняется", 14.0
      "polylog-parts.lisp", "polylog-parts/12: ∫(a + b·atanh(c/x²))² (Google №1) — Li₂ от комплексных аргументов, x² > c", 14.0
      "intbasis.lisp", "intbasis: (y²−x³)² − x⁷ — базис, сертификат и подделка", 14.0
      "int-branch-sqrt.lisp", "int-branch: x^n*sqrt(a-b*x^2) и sqrt(a-b*x^2)/x^n, x^n/sqrt(a-b*x^2) - обе стороны нуля", 13.0
      "integrate-rubi.lisp", "integrate/rubi: интегралы, которые каскад не брал, берутся запасной ступенью", 12.0
      "ratint.lisp", "INT.RS: rootsum раскрыт в радикалах — без root-sum и %i, производная = подынтегральная, ответ вещественный", 12.0
      "integrate-steps.lisp", "шаги Риша: кручение 7 — R(t) = c·t^6·(t^2 − 49), результат тот же", 12.0
      "multiint.lisp", "multiint: Фубини — классические области, точное значение и численный оракул", 12.0
      "ratint.lisp", "случайные: Π f^k и случайные числители — производная первообразной", 12.0
      "rubi-det.lisp", "rubi-det: Rubi 9.3 #24 берётся в свежем состоянии, ответ равен ответу после прогрева", 11.0
      "polylog.lisp", "integrate: честные отказы сохранены", 11.0
      "risch.lisp", "INT.FIX3.c/риш: степени sinh и cosh от логарифма снова интегрируются", 11.0
      "ratint.lisp", "x^n + c с числителями 1 и x^k (дефектные PRS), x^n + x + 1", 10.0
      "multiint.lisp", "multiint: площадь поверхности и поверхностный интеграл", 10.0
      "dimensional.lisp", "dimensional: ζ(3) и Γ(1/4) опознаются — ∫₀^∞ x²/(e^(ax)−1) и ∫₀^∞ e^(−a x⁴)", 10.0
      "genus0.lisp", "genus0: шесть примеров задания", 10.0
      "definite.lisp", "integrate: 1/sin x на [0, π] и 1/x на [−1, 1] расходятся (главное значение — не ответ)", 9.0
      "polylog-parts.lisp", "polylog-parts/11: ∫atan(a+bx)²/(c+dx)² (Google №5) — по частям и разложение на простые дроби", 9.0 ]

// Шаг 21h': медленные Lisp-тесты вынесены во вторую теорию с признаком Category=Slow
// (xUnit не умеет помечать отдельные строки MemberData): быстрый набор — --filter "Category!=Slow".
// Slow = тяжёлые (heavyCases) + прежние тесты > 1,4 с.
let private slowCases : Set<string * string> =
    set [ // ускорение тестов: > 1,4 с каждый (Debug)
          "limit.lisp", "пределы: Грунц берёт то, что старый каскад не брал (x → +∞)"
          "limit.lisp", "пределы: перекрёстная проверка classic и gruntz — где отвечают оба, ответы совпадают"
          "groebner.lisp", "fglm: katsura-5 (5 переменных) и cyclic-5 — инварианты lex-базиса" ]
    |> Set.union (heavyCases |> List.map (fun (f, n, _) -> f, n) |> Set.ofList)

// Остальные файлы: вес = сумма времени их тестов без тяжёлых (замер 2026-11-16, Debug, с); не перечисленные — 1.
let private fileWeights : Map<string, float> =
    Map [ "integrate.lisp", 88.0; "risch.lisp", 77.0; "ratint.lisp", 47.0; "intdiv.lisp", 36.0; "intalg.lisp", 34.0
          "cantor.lisp", 34.0; "integrate-steps.lisp", 34.0; "dimensional.lisp", 31.0; "chebyshev.lisp", 26.0
          "complex-analysis.lisp", 26.0; "mixed.lisp", 24.0; "galois.lisp", 23.0; "integrate-rubi.lisp", 22.0
          "curves.lisp", 21.0; "ansatz.lisp", 20.0; "polylog-parts.lisp", 19.0; "placesnf.lisp", 18.0
          "summation.lisp", 17.0; "two-rad.lisp", 15.0; "multiint.lisp", 14.0; "ode-reduction.lisp", 14.0
          "sf2.lisp", 12.0; "elliptic.lisp", 11.0; "fourier.lisp", 11.0; "subst.lisp", 11.0; "intsq.lisp", 11.0
          "rubi-ch4.lisp", 10.0; "ode-specfun.lisp", 9.0; "plot.lisp", 9.0; "definite-jumps.lisp", 9.0
          "steps-comments.lisp", 9.0; "laplace.lisp", 9.0; "blake.lisp", 8.0; "interval.lisp", 8.0
          "diff-branch-asin.lisp", 7.0; "repr.lisp", 7.0; "algebra-steps.lisp", 7.0; "definite.lisp", 7.0
          "rubi-flat.lisp", 7.0; "limit.lisp", 7.0; "puiseux.lisp", 6.0; "homology.lisp", 6.0; "diffgeom.lisp", 6.0
          "sf-real.lisp", 6.0; "rubi-c.lisp", 5.0; "stats.lisp", 5.0; "ode-kovacic.lisp", 5.0; "rubi.lisp", 5.0
          "integrate-refusal-steps.lisp", 5.0; "rubi-ch2.lisp", 4.0; "rubi-det.lisp", 4.0; "solve.lisp", 4.0
          "rubi-backtrack.lisp", 4.0; "attempts.lisp", 4.0; "genus0.lisp", 4.0; "group.lisp", 4.0
          "variational.lisp", 4.0; "forms.lisp", 4.0; "hypergeometric.lisp", 3.0; "ode-steps.lisp", 3.0
          "curvature.lisp", 3.0; "sos.lisp", 3.0; "groebner.lisp", 3.0; "ode-exact.lisp", 3.0
          "ode-numeric.lisp", 3.0; "ode-series.lisp", 3.0; "constzero.lisp", 3.0; "algnum.lisp", 2.0 ]

// Номер осколка (0-based) — по имени сборки «Lisp.Tests.LispK»; без номера (-1) — выполнять всё
let private shardIndex : int =
    let n = System.Reflection.Assembly.GetExecutingAssembly().GetName().Name
    let tail = n |> Seq.rev |> Seq.takeWhile System.Char.IsDigit |> Seq.rev |> Seq.toArray |> System.String
    if tail = "" then -1 else int tail - 1

// Раздача: единицы (файл целиком | тяжёлый тест) по убыванию веса — каждая на наименее нагруженный осколок.
type private Work =
    | WholeFile of string
    | Heavy of string * string

let private assignment : Map<Work, int> =
    let loads = Array.zeroCreate<float> shardCount
    let fileUnits =
        Directory.GetFiles(lispDir, "*.lisp")
        |> Array.map (fun p -> let f = Path.GetFileName p in WholeFile f, (Map.tryFind f fileWeights |> Option.defaultValue 1.0))
    let heavyUnits = heavyCases |> List.map (fun (f, n, w) -> Heavy (f, n), w) |> List.toArray
    Array.append fileUnits heavyUnits
    |> Array.sortBy (fun (u, w) -> -w, u)
    |> Array.fold (fun (m: Map<Work, int>) (u, w) ->
        let k = loads |> Array.indexed |> Array.minBy snd |> fst
        loads[k] <- loads[k] + w
        m.Add(u, k)) Map.empty

let private heavySet = heavyCases |> List.map (fun (f, n, _) -> f, n) |> Set.ofList

let private inShard (file: string, name: string) =
    shardIndex < 0
    || (if heavySet.Contains (file, name) then assignment[Heavy (file, name)] = shardIndex
        else assignment[WholeFile file] = shardIndex)

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
