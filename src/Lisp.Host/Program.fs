// Точка входа: REPL, загрузка .lisp файлов, CLI-JSON режим
module Program

open System
open System.Text.Json
open Types
open Reader
open Evaluator
open Printer
open AgentApi
open MathPrinter

// Проверяем — завершить ли REPL
let isExitCommand (input: string) : bool =
    let trimmed = input.Trim()
    trimmed = "exit" || trimmed = "quit" || trimmed = ",q"

// Загружаем и выполняем .lisp-файл (через Evaluator.loadIntoEnv); Шаг D1: печать результата — с лимитом
// Шаг D0: возвращает код возврата (0 ок / 1 ошибка) — раньше битый файл (скобки) печатал сообщение, но код был 0
let loadFile (path: string) : int =
    try
        loadIntoEnv path globalEnv |> fun v -> Printer.limitPrint v (prettyPrint v) |> Console.WriteLine
        0
    with
    | ex ->
        recordError globalEnv ex
        Console.WriteLine("  ОШИБКА: " + Debug.formatError (Debug.wrap ex))
        1

// Шаг 21: показывать ли стек Lisp в ошибках математического режима (команда :debug)
let mutable private showStack = false

// Выполнить текст программы входного языка, печатая значение каждого оператора (синтаксис языка).
// Ошибка — сообщение без стека Lisp (со стеком — при :debug); возвращает false при ошибке
let private runMathText (env: Env) (file: string) (text: string) : bool =
    try
        for ast in MathReader.mathParseProgramFrom file text do
            let v = evalMathTree env ast
            Console.WriteLine(Printer.limitPrint v (mathPrintLang v))
        true
    with
    | ex ->
        recordError env ex
        if showStack then Console.WriteLine("ОШИБКА: " + Debug.formatError (Debug.wrap ex))
        else Console.WriteLine("ОШИБКА: " + plainErrorMessage ex)
        false

// Ввод продолжается на следующей строке, если не закрыта скобка или строка, либо строка заканчивается
// бинарным оператором (a +, f(x) :=, ... and); строки и // комментарии пропускаются
let private needsMoreInput (text: string) : bool =
    let mutable depth = 0
    let mutable i = 0
    let mutable inStr = false
    let signif = System.Text.StringBuilder()        // значимые символы вне комментариев (хвост — для проверки оператора)
    while i < text.Length do
        let c = text.[i]
        if inStr then
            if c = '\\' then i <- i + 1
            elif c = '"' then inStr <- false
        elif c = '"' then inStr <- true
        elif c = '/' && i + 1 < text.Length && text.[i + 1] = '/' then
            while i < text.Length && text.[i] <> '\n' do i <- i + 1
        elif c = '(' || c = '[' || c = '{' then depth <- depth + 1
        elif c = ')' || c = ']' || c = '}' then depth <- depth - 1
        if not inStr && not (Char.IsWhiteSpace c) && i < text.Length then signif.Append text.[i] |> ignore
        i <- i + 1
    let s = signif.ToString()
    let danglingOp =
        s.Length > 0 && ("+-*/^=,<>:∪∩\\≤≥≠∈∉".IndexOf s.[s.Length - 1] >= 0)
    depth > 0 || inStr || danglingOp

// Чтение ввода в математическом режиме: продолжаем, пока скобки не закрыты
let private readMathInput () : string =
    let first = Console.ReadLine()
    if first = null then null
    else
        let mutable text = first
        let mutable eof = false
        while not eof && needsMoreInput text do
            Console.Write("...> ")
            let next = Console.ReadLine()
            if next = null then eof <- true
            else text <- text + "\n" + next
        text

// Главный цикл REPL; Шаг 21: два режима — Lisp (lisp> ) и математический (math> ); переключение :math / :lisp
// Шаг D1: ограничение печати результата 2000 (0 — без лимита, меняется (set-print-limit n))
let repl (env: Env) (startMath: bool) =
    Printer.PrintLimit <- 2000
    let mutable mathMode = startMath
    let mutable running = true
    while running do
        Console.Write(if mathMode then "math> " else "lisp> ")
        let input = if mathMode then readMathInput () else Console.ReadLine()
        if input = null then running <- false  // EOF
        elif isExitCommand input then
            Console.WriteLine("Пока!")
            running <- false
        else
            match input.Trim() with
            | ":math" ->
                mathMode <- true
                Console.WriteLine("Математический режим (вернуться: :lisp)")
            | ":lisp" ->
                mathMode <- false
                Console.WriteLine("Режим Lisp (математический: :math)")
            | ":debug" ->
                showStack <- not showStack
                Console.WriteLine(if showStack then "Стек Lisp в ошибках: вкл" else "Стек Lisp в ошибках: выкл")
            | _ when mathMode -> runMathText env "<repl>" input |> ignore
            | _ ->
                try
                    let exprs = readAllFrom "<repl>" input
                    if exprs.IsEmpty then
                        Console.WriteLine("  ; пустой ввод")
                    else
                        for expr in exprs do
                            let result = eval expr env
                            Console.WriteLine("  => " + Printer.limitPrint result (prettyPrint result))
                with
                | ex ->
                    // Шаг 15b: ошибка со стеком; объект ошибки сохраняется в *last-error* (см. (backtrace))
                    recordError env ex
                    Console.WriteLine("  ОШИБКА: " + Debug.formatError (Debug.wrap ex))

// Шаг 21: выполнить файл входного языка (.mth); ошибка разбора — до выполнения; код возврата 1 при ошибке
let private runMathFile (path: string) : int =
    if not (IO.File.Exists path) then
        Console.WriteLine("ОШИБКА: файл не найден: " + path)
        1
    elif runMathText globalEnv path (IO.File.ReadAllText path) then 0
    else 1

// Шаг 17b: бенчмарки — bench\*.lisp рядом с исполняемым файлом.
//   --bench                 все задачи: 1 прогрев + N повторов (по умолчанию 7), медиана
//   --bench --profile       каждая задача один раз под (profile ...) — таблица и доля «чистой интерпретации»
//   --bench --reps N        число повторов; остальные аргументы без «--» — фильтр по подстроке имени файла
let private median (xs: float[]) : float =
    let s = Array.sort xs
    s.[s.Length / 2]

let private timeMs (f: unit -> unit) : float =
    let sw = Diagnostics.Stopwatch.StartNew()
    f ()
    sw.Stop()
    sw.Elapsed.TotalMilliseconds

let private runBench (argv: string[]) : unit =
    let profileMode = Array.contains "--profile" argv
    let reps =
        match Array.tryFindIndex ((=) "--reps") argv with
        | Some i when i + 1 < argv.Length -> int argv.[i + 1]
        | _ -> 7
    let filters =
        argv |> Array.mapi (fun i a -> i, a)
             |> Array.filter (fun (i, a) -> i > 0 && not (a.StartsWith "--") && not (i > 0 && argv.[i - 1] = "--reps"))
             |> Array.map snd
    let dir = IO.Path.Combine(AppContext.BaseDirectory, "bench")
    // Задачи с «_slow» в имени (десятки секунд, например cyclic-6) — только по явному фильтру со словом slow или полному имени
    let isSlow (f: string) = IO.Path.GetFileName(f).Contains "_slow"
    let files =
        IO.Directory.GetFiles(dir, "*.lisp") |> Array.sort
        |> Array.filter (fun f ->
            let name = IO.Path.GetFileNameWithoutExtension f
            if isSlow f then filters |> Array.exists (fun s -> (s.Contains "slow" && name.Contains s) || s = name)
            else filters.Length = 0 || filters |> Array.exists (fun s -> IO.Path.GetFileName(f).Contains s))
    let env = globalEnv
    // e: загрузка prelude (newEnv): прогрев + повторы
    if filters.Length = 0 || filters |> Array.exists (fun s -> "e_prelude".Contains s) then
        let warm = Diagnostics.Stopwatch.StartNew()
        while warm.ElapsedMilliseconds < 400L do newEnv () |> ignore
        let ts = Array.init reps (fun _ -> timeMs (fun () -> newEnv () |> ignore))
        Console.WriteLine(sprintf "%-16s медиана %9.1f мс  (мин %.1f)" "e_prelude" (median ts) (Array.min ts))
    for f in files do
        let name = IO.Path.GetFileNameWithoutExtension f
        let exprs = readAll (IO.File.ReadAllText f)
        let run () = for e in exprs do eval e env |> ignore
        // прогрев (JIT, определения): не менее 2 прогонов и не менее ~400 мс — иначе короткие задачи
        // меряются на неоптимизированном (tier-0) коде
        let warm = Diagnostics.Stopwatch.StartNew()
        run ()
        run ()
        while warm.ElapsedMilliseconds < 400L do run ()
        if profileMode then
            Console.WriteLine("=== " + name)
            // Шаг 21i' (d): под профилем вызовы идут без TCO (измеряется каждый), хвостовой цикл растёт стеком —
            // поднимаем логический лимит глубины (системный стек 256 МБ защищён checkStack)
            Debug.maxDepth <- 2000000
            eval (LispList [ LispSym "profile"; LispList (LispSym "begin" :: exprs) ]) env |> ignore
        else
            let ts = Array.init reps (fun _ -> timeMs run)
            Console.WriteLine(sprintf "%-16s медиана %9.1f мс  (мин %.1f)" name (median ts) (Array.min ts))

// REL.1a: версия продукта — из <Version> Directory.Build.props (AssemblyVersion), в коде строкой не дублируется
let private versionText () : string =
    let asm = Reflection.Assembly.GetEntryAssembly()
    if isNull asm then "Qedra" else "Qedra " + asm.GetName().Version.ToString()

// REL.1a: --sandbox и повторяемый --allow-dir — во всех режимах, кроме --mcp (у него свои ключи).
// Ключи вынимаются из argv до выбора режима, поэтому их место в командной строке неважно.
let private splitSandboxArgs (argv: string[]) : Result<bool * string list * string[], string> =
    let mutable enabled = false
    let dirs = ResizeArray<string>()
    let rest = ResizeArray<string>()
    let mutable i = 0
    let mutable bad = None
    while i < argv.Length && bad.IsNone do
        match argv.[i] with
        | "--sandbox" ->
            enabled <- true
            i <- i + 1
        | "--allow-dir" ->
            if i + 1 < argv.Length then
                let d = argv.[i + 1]
                if IO.Directory.Exists d then
                    dirs.Add d
                    i <- i + 2
                else bad <- Some ("--allow-dir: каталог не найден: " + d)
            else bad <- Some "--allow-dir требует аргумент: путь к каталогу"
        | a ->
            rest.Add a
            i <- i + 1
    match bad with
    | Some m -> Error m
    | None -> Ok (enabled, List.ofSeq dirs, rest.ToArray())

// Тело main: режимы запуска
let private helpText () : string =
    [| "Lisp — интерпретатор Lisp/Scheme + CAS (F#/.NET)"
       "Использование: Lisp [ключи] [файл] [-e \"выражение\"]..."
       ""
       "Режимы:"
       "  lisp                     → REPL (Lisp)"
       "  lisp --math              → REPL в математическом режиме (math>)"
       "  lisp file.lisp           → выполнить файл Lisp"
       "  lisp file.mth            → выполнить файл входного математического языка"
       "  lisp --check [--json] файл.lisp ... → статическая проверка без выполнения: скобки, имена, арность; код 1 при ошибках"
       "  lisp --guide [тема]                → справка для LLM: ядро и список тем (ресурс MCP lisp://guide); с темой или синонимом (DSolve) — карточка (как инструмент MCP guide)"
       "  lisp --query вид арг [--json] [--no-body] [--depth N] → запросы к коду lib\: def sig refs callers callees module outline search deps unused"
       "  lisp --json              → CLI-JSON режим (stdin/stdout, для агентов)"
       "  lisp --mcp               → MCP-сервер на stdio (--allow-dir, --unsafe, --max-memory-mb)"
       "  lisp --bench [--reps N] [--profile] [фильтр] → бенчмарки bench\\*.lisp"
       "  lisp --lean out.lean --math -e \"integrate(f, x)\" → .lean для Lean 4 (генератор — lib\\lean, Lean не запускается)"
       "  lisp --lean-results файл.jsonl [режим] → принять результаты прогона Lean (статусы по хешу текста .lean)"
       "  lisp --version           → версия продукта (Qedra 1.109.7.11)"
       ""
       "Песочница (защита от ошибок LLM, не изоляция ОС):"
       "  lisp --sandbox [--allow-dir <путь>]... [режим] — load/load-math только из lib\\ и --allow-dir;"
       "  --allow-dir можно повторять; в режиме --mcp песочница включена по умолчанию (снимает --unsafe)"
       ""
       "Быстрая проба (без временного файла):"
       "  lisp -e \"(integrate '(exp (^ x 2)) 'x)\"     выполнить выражения Lisp, напечатать последнее"
       "  lisp --math -e \"integrate(exp(x^2), x)\"     то же во входном языке"
       "  lisp --latex -e \"x^2/2\"                     ответ в LaTeX (KaTeX; с --math — и для входного языка)"
       "  lisp lib.lisp -e \"(f 3)\"                    сначала загрузить файл, потом выражения"
       "  несколько -e выполняются по порядку в одном окружении"
       ""
       "Ограничение печати результата (REPL, -e, show): по умолчанию 2000 символов, 0 — без лимита;"
       "меняется из Lisp: (set-print-limit 100) или (set-print-limit 0)"
       "В REPL: 'exit'/',q' — выход, :math / :lisp — режимы, :debug — стек ошибок." |]
    |> String.concat "\n"

// Шаг D1: разбор аргументов (файл + список -e/--eval строк); режимные ключи пропускакются
// (их обрабатывает run). Неизвестный ключ с «-» — Error
let private parseArgs (argv: string[]) : Result<string option * string list, string> =
    let mutable file = None
    let mutable evals = []
    let mutable i = 0
    let mutable bad = None
    while i < argv.Length && bad.IsNone do
        let a = argv.[i]
        if a = "-e" || a = "--eval" then
            if i + 1 < argv.Length then evals <- evals @ [ argv.[i + 1] ]; i <- i + 2
            else bad <- Some "-e/--eval требует аргумент: выражение в кавычках"
        elif a = "--math" || a = "--json" || a = "--mcp" || a = "--bench" || a = "--help" || a = "-h"
             || a = "--latex" || a = "--reps" || a = "--profile" || a = "--allow-dir" || a = "--unsafe" || a = "--max-memory-mb"
             || a = "--lean" || a = "--lean-results" then
            // аргументы-значения режимных ключей пропускаем вместе с ключом
            if a = "--reps" || a = "--allow-dir" || a = "--max-memory-mb" || a = "--lean" || a = "--lean-results" then i <- i + 2 else i <- i + 1
        elif a.StartsWith "-" && a.Length > 1 && not (IO.File.Exists a) then
            bad <- Some ("неизвестный ключ: " + a + ", см. --help")
        elif file.IsNone then
            file <- Some a
            i <- i + 1
        else bad <- Some ("лишний аргумент: " + a)
    match bad with
    | Some m -> Error m
    | None -> Ok(file, evals)

// Шаг D1: выполнить выражения из -e (Lisp): в одном окружении, напечатать последнее (как REPL, без «  => »);
// ошибка — сообщение со стеком как в loadFile, код 1. По умолчанию ограничение печати 2000.
// Шаг TEX.1: latex = true — результат печатается в LaTeX (KaTeX) вместо обычной записи
let private runEvalLisp (latex: bool) (evals: string list) : int =
    Printer.PrintLimit <- 2000
    let mutable result = LispNil
    try
        for text in evals do
            for expr in readAllFrom "<-e>" text do
                result <- eval expr globalEnv
        Console.WriteLine(Printer.limitPrint result (if latex then LatexPrinter.latexPrint result else prettyPrint result))
        0
    with
    | ex ->
        recordError globalEnv ex
        Console.WriteLine("  ОШИБКА: " + Debug.formatError (Debug.wrap ex))
        1

// Шаг D1: то же для входного языка (--math -e): каждое выражение печатается через mathPrintLang
// Шаг D0: разбор (MathReader.fail) тоже под try — битый синтаксис был необработанным исключением (крах процесса)
let private runEvalMath (latex: bool) (evals: string list) : int =
    Printer.PrintLimit <- 2000
    let mutable ok = true
    for text in evals do
        try
            for ast in MathReader.mathParseProgramFrom "<-e>" text do
                let v = evalMathTree globalEnv ast
                Console.WriteLine(Printer.limitPrint v (if latex then LatexPrinter.latexPrint v else mathPrintLang v))
        with
        | ex ->
            recordError globalEnv ex
            Console.WriteLine("ОШИБКА: " + Debug.formatError (Debug.wrap ex))
            ok <- false
    if ok then 0 else 1

// CHK: статическая проверка файлов (код не выполняется): --check [--json] файл...; код 1 — есть ошибки
let private runCheck (argv: string[]) : int =
    let json = Array.contains "--json" argv
    let files = argv |> Array.filter (fun a -> not (a.StartsWith "--")) |> List.ofArray
    if files.IsEmpty then
        Console.WriteLine("ОШИБКА: --check требует имена файлов: Lisp --check [--json] файл.lisp ...")
        2
    else
        let diags =
            files |> List.collect (fun f ->
                if not (IO.File.Exists f) then
                    [ Checker.fileNotFound f ]
                elif f.EndsWith(".mth", StringComparison.OrdinalIgnoreCase) then
                    Console.Error.WriteLine("пропущен " + f + ": проверка .mth не поддерживается (только .lisp)")
                    []
                else Checker.checkTextEnv globalEnv f (IO.File.ReadAllText f))
        if json then Console.WriteLine(Checker.formatJson diags)
        else for d in diags do Console.WriteLine(Checker.formatDiag d)
        if diags |> List.exists (fun d -> d.Severity = Checker.SevError) then 1 else 0

// LEAN.L1: --lean out.lean --math -e "integrate(f, x)" — сгенерировать .lean (генератор — lib\lean\emit.lisp).
// Хост только находит integrate в AST, вызывает Lisp-генератор и пишет файл; Lean здесь не запускается.
let private runLean (argv: string[]) : int =
    let idx = Array.IndexOf(argv, "--lean")
    if idx < 0 || idx + 1 >= argv.Length then
        Console.WriteLine("ОШИБКА: --lean требует файл: --lean out.lean --math -e \"integrate(f, x)\"")
        2
    else
        let outPath = argv.[idx + 1]
        let mathMode = Array.contains "--math" argv
        let evals = ResizeArray<string>()
        let mutable i = 0
        while i < argv.Length do
            if (argv.[i] = "-e" || argv.[i] = "--eval") && i + 1 < argv.Length then
                evals.Add argv.[i + 1]
                i <- i + 2
            elif argv.[i] = "--lean" then i <- i + 2
            else i <- i + 1
        if not mathMode then
            Console.WriteLine("ОШИБКА: --lean работает с --math -e \"integrate(f, x)\"")
            2
        elif evals.Count = 0 then
            Console.WriteLine("ОШИБКА: --lean: нет выражения (-e)")
            2
        else
            let stem = IO.Path.GetFileNameWithoutExtension outPath
            let id = Text.RegularExpressions.Regex.Replace(stem, "[^A-Za-z0-9_]", "_")
            let mutable written = false
            try
                for text in evals do
                    for ast in MathReader.mathParseProgramFrom "<lean>" text do
                        match ast with
                        | LispList (LispSym "integrate" :: f :: LispSym x :: []) ->
                            let q (v: LispValue) = LispList [ LispSym "quote"; v ]
                            eval (LispList [ LispSym "conditions-clear" ]) globalEnv |> ignore
                            let F = eval (LispList [ LispSym "integrate"; q f; q (LispSym x) ]) globalEnv
                            let conds = eval (LispList [ LispSym "conditions" ]) globalEnv
                            let res =
                                eval (LispList [ LispSym "lean-emit-antiderivative"; q f; q F; q (LispSym x); q conds; LispStr id ]) globalEnv
                            match res with
                            | LispStr source ->
                                IO.File.WriteAllText(outPath, source)
                                Console.WriteLine($"Lean: {outPath} → qedra_int_{id}")
                                written <- true
                            | LispList (LispSym "unsupported" :: LispStr why :: _) ->
                                Console.WriteLine("Lean: unsupported — " + why)
                            | other ->
                                Console.WriteLine("Lean: не удалось: " + prettyPrint other)
                        | LispList (LispSym "integrate" :: _) ->
                            Console.WriteLine("Lean: поддерживается только неопределённый integrate(f, x)")
                        | _ -> ()
                if written then 0 else 1
            with ex ->
                recordError globalEnv ex
                Console.WriteLine("ОШИБКА: " + plainErrorMessage ex)
                1

// LEAN.L3: --lean-results файл.jsonl — принять результаты Lean (записи по хешу текста .lean).
// Разбор JSONL — здесь, хранилище и сопоставление — в lib\lean\emit.lisp (lean-results-add).
let private loadLeanResults (path: string) : int =
    if not (IO.File.Exists path) then
        Console.Error.WriteLine("ОШИБКА: файл результатов не найден: " + path)
        1
    else
        let mutable n = 0
        let mutable bad = 0
        let entries = ResizeArray<string * string * string * string * string * string>()
        for line in IO.File.ReadAllLines path do
            let t = line.Trim()
            if t <> "" then
                try
                    use doc = JsonDocument.Parse t
                    let p = doc.RootElement
                    let str (name: string) =
                        match p.TryGetProperty(name) with
                        | true, v when v.ValueKind = JsonValueKind.String -> v.GetString()
                        | _ -> ""
                    let hash = str "hash"
                    if hash = "" then bad <- bad + 1
                    else
                        let entry = (hash, str "status", str "file", str "lemma", str "lean", str "log")
                        entries.Add entry
                        eval (LispList [ LispSym "lean-results-add"; LispStr hash; LispStr (str "status");
                                          LispStr (str "file"); LispStr (str "lemma"); LispStr (str "lean"); LispStr (str "log") ])
                            globalEnv |> ignore
                        n <- n + 1
                with _ ->
                    bad <- bad + 1
        // MCP/--json создают отдельный Env: результаты должны попасть и в новые сессии
        AgentApi.leanResults <- List.ofSeq entries
        Console.Error.WriteLine($"Lean: принято результатов {n} из {path}" + (if bad > 0 then $"; пропущено строк: {bad}" else ""))
        if n > 0 || bad = 0 then 0 else 1

// Ключи --lean-results <файл> вынимаются до выбора режима (работает и с --mcp, и с -e)
let private extractLeanResults (argv: string[]) : string option * string[] =
    let i = Array.IndexOf(argv, "--lean-results")
    if i >= 0 && i + 1 < argv.Length then
        let rest = argv |> Array.indexed |> Array.filter (fun (j, _) -> j <> i && j <> i + 1) |> Array.map snd
        Some argv.[i + 1], rest
    else None, argv

let private runModes (argv: string[]) : int =
    // Режимы запуска:
    //   lisp                    → REPL (Lisp)
    //   lisp --math             → REPL в математическом режиме (math> )
    //   lisp file.lisp          → выполнить файл Lisp
    //   lisp file.mth           → выполнить файл входного математического языка (Шаг 21)
    //   lisp --json             → CLI-JSON режим (stdin/stdout, для агентов)
    //   lisp --mcp              → MCP-сервер на stdio (Шаг 22.3, McpServer.fs); песочница, --allow-dir, --unsafe — 22.4
    //   lisp -e "expr" ...      → выполнить выражения (после файла, если указан), напечатать последнее (Шаг D1)
    //   lisp --math -e "expr"   → то же во входном языке; --help / -h — справка, неизвестный ключ — код 2
    if argv.Length > 0 && argv.[0] = "--guide" then
        // Шаг GD.1: lisp --guide [тема] — тот же текст, что у инструмента MCP guide
        match Guide.text (if argv.Length > 1 then Some argv.[1] else None) with
        | Ok text ->
            Console.WriteLine text
            0
        | Error msg ->
            Console.WriteLine("ОШИБКА: " + msg)
            1
    elif Array.contains "--query" argv then
        QueryCli.runCli globalEnv argv
    elif Array.contains "--check" argv then
        runCheck (argv |> Array.filter (fun a -> a <> "--check"))
    elif argv.Length > 0 && argv.[0] = "--json" then
        runCliJsonLoop ()
        0
    elif argv.Length > 0 && argv.[0] = "--mcp" then
        // подшаг 22.4: --mcp [--allow-dir <путь>]... [--unsafe] [--max-memory-mb <N>]
        McpHost.run (List.ofArray argv.[1..])
    elif argv.Length > 0 && argv.[0] = "--bench" then
        runBench argv
        0
    elif argv.Length > 0 && (argv.[0] = "--help" || argv.[0] = "-h") then
        Console.WriteLine(helpText ())
        0
    elif Array.contains "--lean" argv then
        runLean argv
    elif Array.contains "-e" argv || Array.contains "--eval" argv then
        // Шаг D0: prelude не загрузился — интерпретатор без библиотеки, задание -e почти наверняка
        // не выполнится осмысленно; явный отказ с кодом 1 (не крах)
        if preludeError.IsSome then 1
        else
        // Шаг D1: -e [--math]: файл (если есть) и выражения собирает parseArgs из всего argv
        let mathMode = Array.contains "--math" argv
        let latexMode = Array.contains "--latex" argv
        match parseArgs argv with
        | Error msg ->
            Console.WriteLine("ОШИБКА: " + msg)
            2
        | Ok (file, evals) ->
            let runEvals () = if mathMode then runEvalMath latexMode evals else runEvalLisp latexMode evals
            match file with
            | Some f when not (IO.File.Exists f) ->
                Console.WriteLine("ОШИБКА: файл не найден: " + f)
                2
            | Some f when f.EndsWith(".mth", StringComparison.OrdinalIgnoreCase) ->
                let code = runMathFile f
                if code = 0 then runEvals () else code
            | Some f ->
                // тихая загрузка (без печати результата файла — для -e важен только вывод выражений)
                let okFile =
                    try
                        loadIntoEnv f globalEnv |> ignore
                        true
                    with
                    | ex ->
                        recordError globalEnv ex
                        Console.WriteLine("  ОШИБКА: " + Debug.formatError (Debug.wrap ex))
                        false
                if okFile then runEvals () else 1
            | None -> runEvals ()
    elif argv.Length > 0 && argv.[0] = "--math" then
        // Шаг D0: prelude не загрузился — REPL без библиотеки малополезен; явный отказ с кодом 1
        if preludeError.IsSome then 1
        else
        Console.WriteLine("Математический режим. :lisp — режим Lisp, :debug — стек ошибок, exit — выход.")
        repl globalEnv true
        0
    elif argv.Length > 0 && argv.[0].EndsWith(".mth", StringComparison.OrdinalIgnoreCase) then
        runMathFile argv.[0]
    elif argv.Length > 0 && argv.[0].StartsWith "-" && argv.[0].Length > 1 && not (IO.File.Exists argv.[0]) then
        // Шаг D1: неизвестный ключ — не пытаемся грузить как файл; код 2
        Console.WriteLine("ОШИБКА: неизвестный ключ: " + argv.[0] + ", см. --help")
        2
    elif argv.Length > 0 then
        Printer.PrintLimit <- 2000
        // Шаг D0: prelude не загрузился — файл почти наверняка зависит от библиотеки; отказ с кодом 1
        // (не крах; сообщение об ошибке библиотеки уже напечатано в stderr при старте)
        if preludeError.IsSome then 1 else loadFile argv.[0]
    else
        // Шаг D0: REPL без библиотеки (preludeError) — печатаем предупреждение, но запускаем (интерактивный
        // режим сам покажет ошибки неопределённых имён; сообщения об ошибке библиотеки уже в stderr)
        if preludeError.IsSome then
            Console.WriteLine("ВНИМАНИЕ: библиотека lib\\prelude.lisp не загрузилась — базовые функции могут быть неопределены.")
        Console.WriteLine("MiniLisp — F# Lisp/Scheme интерпретатор (CAS)")
        Console.WriteLine("Режимы: lisp | lisp --math | lisp file.lisp | lisp file.mth | lisp --json | lisp --mcp")
        Console.WriteLine("В REPL напишите 'exit' или ',q' для выхода; :math / :lisp — переключение режима.")
        Console.WriteLine()
        repl globalEnv false
        0

// REL.1a: общие ключи до выбора режима — --version и песочница; --mcp сохраняет свои --allow-dir/--unsafe
let private run (argv: string[]) : int =
    let resultsPath, argv = extractLeanResults argv
    match resultsPath with
    | Some p -> loadLeanResults p |> ignore
    | None -> ()
    if Array.contains "--version" argv then
        Console.WriteLine(versionText ())
        0
    elif Array.contains "--mcp" argv then
        runModes argv
    else
        match splitSandboxArgs argv with
        | Error msg ->
            Console.WriteLine("ОШИБКА: " + msg)
            2
        | Ok (enabled, dirs, rest) ->
            Sandbox.configure enabled dirs
            runModes rest

// Шаг 15b: интерпретатор работает в потоке с большим стеком (256 МБ): глубокая нехвостовая рекурсия
// упирается в логический лимит глубины или EnsureSufficientExecutionStack, а не роняет процесс
[<EntryPoint>]
let main (argv: string[]) =
    // Шаг 16: домены печатаются как ℕ ℤ ℚ ℝ ℂ — консоль в UTF-8
    Console.OutputEncoding <- System.Text.Encoding.UTF8
    let code = ref 0
    let t = System.Threading.Thread((fun () -> code.Value <- run argv), 256 * 1024 * 1024)
    t.Start()
    t.Join()
    code.Value
