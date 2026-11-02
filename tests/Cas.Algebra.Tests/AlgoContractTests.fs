// Тесты единого контракта алгоритмов (шаг 21h'): исход Outcome, реестр счётчиков AlgoStats, переключатели Algorithms,
// журнал шагов StepLog. Параллельность: всё состояние — по потокам (ThreadLocal / ThreadStatic)
module AlgoContractTests

open System
open System.Threading.Tasks
open Xunit
open Outcome
open MPoly
open PolyText

// Выполнить f в НОВОМ потоке и вернуть результат (Task.Result может выполнить задачу inline в вызывающем потоке)
let private onNewThread (f: unit -> 'a) : 'a =
    let mutable result = Unchecked.defaultof<'a>
    let mutable error : exn = null
    let t = Threading.Thread((fun () -> try result <- f () with ex -> error <- ex))
    t.Start()
    t.Join()
    if not (isNull error) then raise error
    result

// --- Outcome ---

[<Fact>]
let ``Outcome: map, bind, toOption, ofOption`` () =
    let a : Outcome<int> = Answer 2
    Assert.Equal(Answer 4, map ((*) 2) a)
    Assert.Equal(Answer 3, bind (fun x -> Answer (x + 1)) a)
    Assert.Equal<Outcome<int>>(Unknown "нет", bind (fun x -> Answer (x + 1)) (Unknown "нет"))
    Assert.Equal<Outcome<int>>(NoSolution "доказано", bind (fun x -> Answer (x + 1)) (NoSolution "доказано"))
    Assert.Equal(Some 2, toOption a)
    Assert.Equal(None, toOption (Unknown "x" : Outcome<int>))
    Assert.Equal<Outcome<int>>(Unknown "причина", ofOption "причина" None)
    Assert.Equal<Outcome<int>>(Answer 5, ofOption "причина" (Some 5))
    Assert.True(isAnswer a)
    Assert.False(isAnswer (NoSolution "x" : Outcome<int>))

[<Fact>]
let ``Outcome: firstAnswer — первый ответ; «доказано, что нет» важнее «не знаю»; причины копятся`` () =
    let calls = ResizeArray<string>()
    let alt (name: string) (o: Outcome<int>) = fun () -> (calls.Add name; o)
    Assert.Equal<Outcome<int>>(Answer 7, firstAnswer [ alt "a" (Unknown "1"); alt "b" (Answer 7); alt "c" (Answer 9) ])
    Assert.Equal<string list>([ "a"; "b" ], List.ofSeq calls)                       // третья альтернатива не вызывалась
    Assert.Equal<Outcome<int>>(NoSolution "нет решения", firstAnswer [ alt "d" (Unknown "x"); alt "e" (NoSolution "нет решения") ])
    Assert.Equal<Outcome<int>>(Unknown "x; y", firstAnswer [ alt "f" (Unknown "x"); alt "g" (Unknown "y") ])
    Assert.Equal<Outcome<int>>(Unknown "", firstAnswer [])

[<Fact>]
let ``Outcome: describe и getOrFail`` () =
    Assert.Equal("ответ: 5", describe string (Answer 5))
    Assert.Equal("не знаю: нет метода", describe string (Unknown "нет метода" : Outcome<int>))
    Assert.Equal("доказано, что решения нет: x", describe string (NoSolution "x" : Outcome<int>))
    Assert.Equal(5, getOrFail "f" (Answer 5))
    Assert.Contains("не знаю (причина)", (Assert.ThrowsAny<exn>(fun () -> getOrFail "f" (Unknown "причина" : Outcome<int>) |> ignore)).Message)
    Assert.Contains("доказано, что решения нет (док)", (Assert.ThrowsAny<exn>(fun () -> getOrFail "f" (NoSolution "док" : Outcome<int>) |> ignore)).Message)

[<Fact>]
let ``Outcome в алгебре: divExactOutcome (NoSolution) и модулярный НОД (Answer / Unknown)`` () =
    let ctx = ctxOf [ "x+y" ] []
    let a = polyIn ctx "(x+y)*(x-y)"
    Assert.Equal(Answer (polyIn ctx "x-y"), MPoly.divExactOutcome a (polyIn ctx "x+y"))
    match MPoly.divExactOutcome a (polyIn ctx "x+3") with
    | NoSolution _ -> ()
    | other -> failwithf "ожидалось NoSolution, получено %A" other
    // ответы прежние: divExactExn по-прежнему бросает то же сообщение
    Assert.Equal("MPoly: деление нацело невозможно", (Assert.ThrowsAny<exn>(fun () -> MPoly.divExactExn a (polyIn ctx "x+3") |> ignore)).Message)
    // модулярный НОД: Answer на примитивных многочленах; та же пара, что и в gcd
    let g = polyIn ctx "x^2+y+1"
    let pa, pb = mul g (polyIn ctx "x+3"), mul g (polyIn ctx "x-5")
    match PolyGcd.modularPrimitiveGcdOutcome PolyGcd.gcd PolyGcd.contentMain pa pb with
    | Answer r -> Assert.Equal(unitNormal g, r)
    | other -> failwithf "ожидался ответ, получено %A" other
    Assert.Equal(PolyGcd.tryModularPrimitiveGcd pa pb, toOption (PolyGcd.modularPrimitiveGcdOutcome PolyGcd.gcd PolyGcd.contentMain pa pb))

// --- AlgoStats ---

[<Fact>]
let ``AlgoStats: регистрация идемпотентна, имена счётчиков, снимок и сброс`` () =
    let g1 = AlgoStats.register "test.stats.a" [| "x"; "y" |]
    let g2 = AlgoStats.register "test.stats.a" [| "другие"; "имена" |]
    Assert.True(obj.ReferenceEquals(g1, g2))
    Assert.Equal<string[]>([| "x"; "y" |], g1.Counters)
    g1.Reset()
    g1.Values.[0] <- g1.Values.[0] + 3
    let snap = AlgoStats.snapshot (Some "test.stats.a")
    Assert.Equal(1, snap.Length)
    Assert.Equal<(string * int) list>([ ("x", 3); ("y", 0) ], snd snap.Head)
    Assert.True(AlgoStats.reset (Some "test.stats.a"))
    Assert.Equal(0, g1.Values.[0])
    Assert.False(AlgoStats.reset (Some "нет-такой-группы"))

[<Fact>]
let ``AlgoStats: счётчики по потокам — параллельные потоки не мешают друг другу`` () =
    let g = AlgoStats.register "test.stats.threads" [| "n" |]
    g.Reset()
    g.Values.[0] <- 100
    let work (k: int) = onNewThread (fun () -> g.Reset(); (for _ in 1 .. k do g.Values.[0] <- g.Values.[0] + 1); g.Values.[0])
    let rs = [ work 10; work 20; work 30 ]
    Assert.Equal<int list>([ 10; 20; 30 ], rs)
    Assert.Equal(100, g.Values.[0])                       // значение этого потока не тронуто

[<Fact>]
let ``AlgoStats: счётчики алгоритмов зарегистрированы (gcd.probe, gcd.zippel, factor.wang) и растут`` () =
    AlgoRegistry.init ()
    let names = AlgoStats.groups () |> List.map (fun g -> g.Name)
    Assert.Contains("gcd.probe", names)
    Assert.Contains("gcd.zippel", names)
    Assert.Contains("factor.wang", names)
    // прежние функции-доступы возвращают массивы тех же групп
    Assert.True(obj.ReferenceEquals(ModGcd.probeStats (), (AlgoStats.tryFind "gcd.probe").Value.Values))
    Assert.True(obj.ReferenceEquals(Zippel.zippelStats (), (AlgoStats.tryFind "gcd.zippel").Value.Values))
    Assert.True(obj.ReferenceEquals(PolyFactor.stats (), (AlgoStats.tryFind "factor.wang").Value.Values))
    AlgoStats.reset None |> ignore
    let ctx = ctxOf [ "x+y+z" ] []
    let g = polyIn ctx "(x^2+y*z+1)*(x+y)"
    let a, b = mul g (polyIn ctx "x+z+2"), mul g (polyIn ctx "x*y-3*z+5")
    PolyGcd.gcd a b |> ignore
    Assert.True((ModGcd.probeStats ()).[0] > 0, "проба одной точкой вызывалась")

// --- Algorithms ---

[<Fact>]
let ``Algorithms: gcd — умолчание auto, допустимые значения, установка и ошибка со списком допустимых`` () =
    let s = Algorithms.gcd
    Assert.Equal<string[]>([| "auto"; "zippel"; "brown" |], s.Values)
    Assert.Equal("auto", s.Default)
    s.Reset()
    let initial = s.Value
    try
        s.Set "zippel"
        Assert.Equal("zippel", s.Value)
        Assert.Equal(1, s.Index)
        Algorithms.set "gcd" "brown"
        Assert.Equal(2, s.Index)
        let ex = Assert.Throws<ArgumentException>(fun () -> s.Set "magic")
        Assert.Contains("допустимо: auto, zippel, brown", ex.Message)
        Assert.Equal("brown", s.Value)                                  // неудачная установка не меняет значение
        Assert.Contains("неизвестный алгоритм nope", (Assert.Throws<ArgumentException>(fun () -> Algorithms.set "nope" "x")).Message)
        // прежний числовой вход тестов
        Zippel.setZippelMode 1
        Assert.Equal("zippel", s.Value)
        Zippel.setZippelMode 0
        Assert.Equal("auto", s.Value)
    finally
        s.Reset()
    Assert.Equal(initial, s.Value)

[<Fact>]
let ``Algorithms: значение по потокам; начальное значение — переменная среды LISP_<ИМЯ>`` () =
    let sw = Algorithms.register "test-switch-env" [| "a"; "b"; "c" |] "a"
    Assert.Equal("a", sw.Value)
    Environment.SetEnvironmentVariable("LISP_TEST_SWITCH_ENV", "c")
    try
        // новый поток читает переменную среды при первом обращении
        let fromNew = onNewThread (fun () -> sw.Value)
        Assert.Equal("c", fromNew)
        // недопустимое значение переменной игнорируется (умолчание)
        Environment.SetEnvironmentVariable("LISP_TEST_SWITCH_ENV", "zzz")
        Assert.Equal("a", onNewThread (fun () -> sw.Value))
    finally
        Environment.SetEnvironmentVariable("LISP_TEST_SWITCH_ENV", null)
    sw.Set "b"
    Assert.Equal("b", sw.Value)
    Assert.Equal("a", onNewThread (fun () -> sw.Value))                 // другой поток не видит установку этого

// --- StepLog ---

[<Fact>]
let ``StepLog: выключен — Record ничего не записывает; включён — записывает по порядку; Clear`` () =
    StepLog.Journal.Enabled <- false
    StepLog.Journal.Clear()
    StepLog.Journal.Record("правило", "комментарий", box 1, box 2)
    Assert.Empty(StepLog.Journal.Steps)
    StepLog.Journal.Enabled <- true
    try
        StepLog.Journal.Record("раскрыть скобки", "раскрываем (x+1)^2", box "до", box "после")
        StepLog.Journal.Record("свернуть", "коммент", box 1, box 2)
        // шаг S.1: старая запись из 4 полей — приём-текст становится заголовком, rule = "step";
        // приём-идентификатор — rule с пустым заголовком
        StepLog.Journal.Record("expand-power", "коммент", box 1, box 2)
        let steps = StepLog.Journal.Steps
        Assert.Equal(3, steps.Length)
        Assert.Equal("step", steps.[0].Rule)
        Assert.Equal("раскрыть скобки", steps.[0].Title)
        Assert.Equal(StepLog.Main, steps.[0].Level)
        Assert.Empty(steps.[0].Children)
        Assert.Equal("expand-power", steps.[2].Rule)
        Assert.Equal("", steps.[2].Title)
        Assert.Equal("раскрываем (x+1)^2", steps.[0].Comment)
        Assert.Equal<obj>(box "до", steps.[0].Before)
        Assert.Equal<obj>(box 2, steps.[1].After)
        StepLog.Journal.Clear()
        Assert.Empty(StepLog.Journal.Steps)
    finally
        StepLog.Journal.Enabled <- false
        StepLog.Journal.Clear()

[<Fact>]
let ``StepLog: при выключенном журнале аргументы не вычисляются (защита if Enabled), Capture восстанавливает состояние`` () =
    StepLog.Journal.Enabled <- false
    let mutable evaluated = 0
    let expensive () = evaluated <- evaluated + 1; box 0
    // идиома нулевой стоимости: аргументы вычисляются только внутри if
    if StepLog.Journal.Enabled then StepLog.Journal.Record("п", "к", expensive (), expensive ())
    Assert.Equal(0, evaluated)
    let (r, steps) =
        StepLog.Journal.Capture(fun () ->
            Assert.True(StepLog.Journal.Enabled)
            if StepLog.Journal.Enabled then StepLog.Journal.Record("п", "к", expensive (), expensive ())
            42)
    Assert.Equal(42, r)
    Assert.Equal(1, steps.Length)
    Assert.Equal(2, evaluated)
    Assert.False(StepLog.Journal.Enabled)                          // состояние восстановлено
    Assert.Empty(StepLog.Journal.Steps)
    // вложенный Capture не портит внешний журнал
    StepLog.Journal.Enabled <- true
    try
        StepLog.Journal.Record("внешний", "1", box 0, box 0)
        let (_, inner) = StepLog.Journal.Capture(fun () -> StepLog.Journal.Record("внутренний", "2", box 0, box 0))
        Assert.Equal(1, inner.Length)
        Assert.Equal("внутренний", inner.Head.Title)
        Assert.Equal(1, StepLog.Journal.Steps.Length)
        Assert.Equal("внешний", StepLog.Journal.Steps.Head.Title)
    finally
        StepLog.Journal.Enabled <- false
        StepLog.Journal.Clear()

// --- Шаг S.1: рамки, отбор по уровню, лимиты ---

let private leaf (rule: string) (level: StepLog.Level) =
    StepLog.Journal.Record(rule, "Заголовок " + rule, "", box 0, box 0, level)

[<Fact>]
let ``StepLog: рамки — вложенность, отбрасывание неудачной, Within, метка рамки`` () =
    let (_, steps) =
        StepLog.Journal.Capture(fun () ->
            let t1 = StepLog.Journal.Open("outer", "Внешний", box "до", StepLog.Main)
            leaf "a" StepLog.Main
            let t2 = StepLog.Journal.Open("failed", "Неудача", box 0, StepLog.Main)
            leaf "noise" StepLog.Detail
            StepLog.Journal.Discard t2                               // неудачная попытка — вместе с детьми
            let t3 = StepLog.Journal.Open("inner", "Внутренний", box 1, StepLog.Detail)
            leaf "b" StepLog.Main
            StepLog.Journal.Close(t3, "пояснение", box 2)
            StepLog.Journal.Discard 99                               // чужая метка — ничего
            StepLog.Journal.Close(t1, "", box "после")
            // Within: None — отбросить, исключение — отбросить и пробросить
            StepLog.Journal.Within("w-none", "", box 0, StepLog.Main, (fun () -> leaf "x" StepLog.Main; 0), (fun _ -> None)) |> ignore
            (try StepLog.Journal.Within("w-exn", "", box 0, StepLog.Main, (fun () -> leaf "y" StepLog.Main; failwith "сбой"), (fun _ -> None)) |> ignore
             with _ -> ())
            StepLog.Journal.Within("w-ok", "", box 0, StepLog.Main, (fun () -> 5), (fun r -> Some ("r = " + string r, box r))) |> ignore
            Assert.Equal(0, StepLog.Journal.Depth))
    Assert.Equal<string list>([ "outer"; "w-ok" ], steps |> List.map (fun s -> s.Rule))
    let outer = steps.Head
    Assert.Equal<string list>([ "a"; "inner" ], outer.Children |> List.map (fun s -> s.Rule))
    Assert.Equal<obj>(box "после", outer.After)
    let inner = outer.Children.[1]
    Assert.Equal(StepLog.Detail, inner.Level)
    Assert.Equal("пояснение", inner.Comment)
    Assert.Equal<string list>([ "b" ], inner.Children |> List.map (fun s -> s.Rule))
    Assert.Equal("r = 5", steps.[1].Comment)
    // выключенный журнал: Open → 0, Close/Discard ничего не делают, Within просто вызывает f
    StepLog.Journal.Enabled <- false
    Assert.Equal(0, StepLog.Journal.Open("z", "", null, StepLog.Main))
    Assert.Equal(7, StepLog.Journal.Within("z", "", null, StepLog.Main, (fun () -> 7), (fun _ -> failwith "не вызывается")))
    Assert.Empty(StepLog.Journal.Steps)

[<Fact>]
let ``StepLog: select — brief, full, глубина 8, лимит 200 узлов, пометки`` () =
    let (_, steps) =
        StepLog.Journal.Capture(fun () ->
            // 1: main с цепочкой глубины 10; 2: detail верхнего уровня; 3..: 250 листьев main
            let rec chain (d: int) =
                if d > 0 then
                    let t = StepLog.Journal.Open(sprintf "d%d" d, "", null, StepLog.Main)
                    chain (d - 1)
                    StepLog.Journal.Close(t, "", null)
            chain 10
            leaf "top-detail" StepLog.Detail
            for i in 1 .. 250 do leaf (sprintf "leaf%d" i) StepLog.Main)
    let brief = StepLog.select StepLog.Brief steps
    Assert.Equal(200, brief.Steps.Length)                            // detail верхнего уровня не входит, лимит 200
    Assert.Equal("d10", brief.Steps.Head.Rule)
    Assert.Empty(brief.Steps.Head.Children)
    Assert.Equal(251, brief.Total)
    let full = StepLog.select StepLog.Full steps
    Assert.Equal(10 + 1 + 250, full.Total)
    Assert.Equal(200, full.Shown)
    Assert.True(full.DepthCut)
    // цепочка обрезана на глубине 8: у узла d3 (глубина 8) скрыто 2 вложенных
    let rec depthOf (s: StepLog.Step) = if s.Children.IsEmpty then (1, s) else let (d, l) = depthOf s.Children.Head in (d + 1, l)
    let d, last = depthOf full.Steps.Head
    Assert.Equal(8, d)
    Assert.Equal("d3", last.Rule)
    Assert.Equal(2, last.Omitted)
    Assert.Equal(StepLog.countNodes full.Steps, full.Shown)
    Assert.Equal(full.Total - full.Shown - 2, full.TopOmitted)
    let note = (StepLog.truncationNote full).Value
    Assert.Contains("показано 200 из 261", note)
    Assert.Contains("глубина до 8", note)
    // без обрезки — пометки нет
    let small = StepLog.select StepLog.Full (List.truncate 1 (List.skip 1 steps))
    Assert.Equal(None, StepLog.truncationNote small)

[<Fact>]
let ``StepLog: журнал и признак — по потокам`` () =
    StepLog.Journal.Enabled <- true
    StepLog.Journal.Clear()
    try
        StepLog.Journal.Record("этот поток", "", box 0, box 0)
        let other = onNewThread (fun () -> (StepLog.Journal.Enabled, StepLog.Journal.Steps.Length))
        Assert.Equal((false, 0), other)
        Assert.Equal(1, StepLog.Journal.Steps.Length)
    finally
        StepLog.Journal.Enabled <- false
        StepLog.Journal.Clear()
