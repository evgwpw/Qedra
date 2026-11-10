// Шаг 16: условные правила переписывания (defrule) — хранилище, поиск и применение.
//
// Правило: (defrule имя образец замена [условие]). Образец канонизируется при регистрации
// (Evaluator вызывает Simplify.simplify), индексация — по символу-голове образца.
// Simplify после алгоритмического упрощения узла пробует правила его оператора по порядку определения;
// первое сработавшее правило даёт замену, которая упрощается заново.
// Условие вычисляет Lisp: ruleHook присваивает Evaluator (модуль компилируется до него).
// Правила глобальные (как таблица методов); интерпретатор однопоточный.
module Rules

open System.Collections.Generic
open Types
open PatternMatching
open Numeric

type Rule =
    { Name: string
      Op: string
      Pattern: LispValue
      Replacement: LispValue
      Condition: LispValue option
      Env: Env
      // Шаг 21h': модуль, в котором определено правило (условие компилируется в его области имён); null — глобальный код
      Module: ModuleInfo
      // Шаг AC.3: правило с флагом :ac сопоставляется через ac-match (lib\match.lisp), а не структурно;
      // образец не канонизируется (simplify свернул бы sin²+cos²), условие уходит в :where и проверяется на каждом кандидате
      Ac: bool
      // Человеческий заголовок шага правила (опция :title "…" у defrule); "" — «правило имя»
      Title: string }

// Все правила в порядке определения (замена по имени — на том же месте)
let private all = ResizeArray<Rule>()
// Индекс: оператор → правила в порядке определения
let private byOp = Dictionary<string, Rule list>()
// Быстрая проверка в горячем пути simplify: есть ли хоть одно правило
let mutable private any = false

let private reindex () =
    byOp.Clear()
    for r in all do
        match byOp.TryGetValue r.Op with
        | true, l -> byOp.[r.Op] <- l @ [ r ]
        | _ -> byOp.[r.Op] <- [ r ]
    any <- all.Count > 0

// Добавить правило; одноимённое заменяется (с сохранением позиции)
let add (rule: Rule) : unit =
    let i = all.FindIndex(fun r -> r.Name = rule.Name)
    if i >= 0 then all.[i] <- rule else all.Add rule
    reindex ()

let remove (name: string) : bool =
    let n = all.RemoveAll(fun r -> r.Name = name)
    reindex ()
    n > 0

let names () : string list = all |> Seq.map (fun r -> r.Name) |> List.ofSeq

let rulesOf (op: string) : string list =
    match byOp.TryGetValue op with
    | true, l -> l |> List.map (fun r -> r.Name)
    | _ -> []

// Приостановка правил: образец при регистрации канонизируется без применения уже имеющихся правил
// (иначе он мог бы переписаться сам)
let mutable suspended : bool = false

// Нет правил для оператора — одна проверка словаря (а при пустой таблице — один bool)
let hasRules (op: string) : bool = any && not suspended && byOp.ContainsKey op

// Вычисление условия: правило, связи переменных образца → истинно ли (ровно #t); присваивает Evaluator
let mutable conditionHook : Rule -> Bindings -> LispValue =
    fun _ _ -> failwith "conditionHook не инициализирован"

// --- trace-rules ---

let mutable tracing : bool = false

// --- Защита от зацикливания: глубина цепочки переписываний ---

let maxChain = 100
let mutable private chain = 0

// Вход в применение правила (бросает при превышении лимита); обязательно парный leave в finally
let enter (rule: Rule) : unit =
    if chain >= maxChain then
        raise (LispError (sprintf "правило %s: превышен лимит последовательных переписываний (%d) — возможно зацикливание" rule.Name maxChain,
                          Debug.snapshot (), LispNil))
    chain <- chain + 1

let leave () : unit = chain <- chain - 1

// Сбросить счётчик (после ошибки на самом внешнем уровне)
let resetChain () : unit = chain <- 0

// Шаг AC.3: AC-сопоставление правила :ac — правило, выражение → привязки (условие правила уже проверено внутри, на каждом
// кандидате); присваивает Evaluator (ac-match написан на Lisp)
let mutable acMatchHook : Rule -> LispValue -> Bindings option =
    fun _ _ -> failwith "acMatchHook не инициализирован"

// Запись значения в пояснении шага (Evaluator подставляет математическую печать)
let mutable formatValue : LispValue -> string = fun v -> Printer.prettyPrint v

// Дешёвый F#-предфильтр перед вызовом Lisp: false — образец заведомо не сопоставится с выражением (по головам, числу
// аргументов под +/* и наличию пары для каждого жёсткого аргумента); true — «возможно». Консервативен: ошибаться
// «возможно» можно, «нет» — никогда. Образцы с - и / (ac-norm меняет их на + * ^) и вложенными той же AC-операцией пропускаются
let rec couldMatch (p: LispValue) (e: LispValue) : bool =
    match p with
    | LispSym s when isPatternVar s -> true
    | LispList (LispSym h :: pargs) when h = "-" || h = "/" -> true
    | LispList (LispSym ("+" | "*" as h) :: pargs) ->
        let isSeg a = (match a with LispSym s -> isPatternVar s && s.Contains "..." | _ -> false)
        let seg = pargs |> List.exists isSeg
        let fixedArgs = pargs |> List.filter (isSeg >> not)
        let nested = fixedArgs |> List.exists (fun a -> match a with LispList (LispSym h2 :: _) -> h2 = h | _ -> false)
        if nested then true
        else
            let items = (match e with LispList (LispSym h2 :: es) when h2 = h -> es | _ -> [ e ])
            let n = items.Length
            let k = fixedArgs.Length
            (if seg then n >= k else n = k)
            && fixedArgs |> List.forall (fun a ->
                   match a with
                   | LispSym s when isPatternVar s -> true
                   | _ -> items |> List.exists (couldMatch a))
    | LispList (LispSym h :: pargs) ->
        // не-AC голова: позиционно; константа без переменных могла быть упрощена в ac-compile — пропускаем её
        let rec hasVar (v: LispValue) =
            match v with
            | LispSym s -> isPatternVar s
            | LispList xs -> List.exists hasVar xs
            | _ -> false
        if not (hasVar p) then true
        else
            match e with
            | LispList (LispSym h2 :: eargs) -> h = h2 && pargs.Length = eargs.Length && List.forall2 couldMatch pargs eargs
            | _ -> false
    // атом образца (символ, число): должен совпасть с выражением как есть (ac-compile упрощает только составные константы)
    | LispSym _ | LispInteger _ | LispRational _ | LispBool _ | LispStr _ -> structEqual p e
    | _ -> true

// Попытка переписать узел: первое сработавшее правило оператора → (правило, замена, привязки)
let tryRewrite (op: string) (expr: LispValue) : (Rule * LispValue * Bindings) option =
    match byOp.TryGetValue op with
    | true, rules ->
        rules |> List.tryPick (fun rule ->
            let found =
                if rule.Ac then
                    if couldMatch rule.Pattern expr then acMatchHook rule expr else None
                else
                    match matchPattern rule.Pattern expr noBindings with
                    | None -> None
                    | Some b ->
                        let ok =
                            match rule.Condition with
                            | None -> true
                            // только ровно #t: unknown и прочие истинные значения правило не включают
                            | Some _ -> (match conditionHook rule b with LispBool true -> true | _ -> false)
                        if ok then Some b else None
            found |> Option.map (fun b -> (rule, substitute b rule.Replacement, b)))
    | _ -> None

// Голова списка образца, непосредственно содержащего сегментную переменную n ("" — не найдена)
let private segParent (pattern: LispValue) (n: string) : string =
    let rec go (p: LispValue) : string option =
        match p with
        | LispList (LispSym h :: args) ->
            if args |> List.exists (fun a -> match a with LispSym s -> s = n | _ -> false) then Some h
            else args |> List.tryPick go
        | LispList xs -> xs |> List.tryPick go
        | _ -> None
    defaultArg (go pattern) ""

// Пояснение шага для AC-правила: обычная переменная — «u = x»; сегментная — по смыслу узла образца:
// под * — «множитель c = z» (несколько — «множители c = z w»), под + — «остальные слагаемые: 3 + y»
// (при нескольких сегментных под + — с именем), иначе «остаток r = …»
let acComment (pattern: LispValue) (b: Bindings) : string =
    let plain, segs = b |> Map.toList |> List.partition (fun (n, _) -> not (n.Contains "..."))
    (plain |> List.map (fun (n, v) -> n.TrimStart('?') + " = " + formatValue v))
    @ (segs |> List.map (fun (n, v) ->
           let name = n.TrimStart('?').Replace("...", "")
           match segParent pattern n with
           | "*" ->
               let many = (match v with LispList (LispSym "*" :: _ :: _ :: _) -> true | _ -> false)
               (if many then "множители " else "множитель ") + name + " = " + formatValue v
           | "+" ->
               let sumSegs = segs |> List.filter (fun (m, _) -> segParent pattern m = "+")
               if sumSegs.Length = 1 then "остальные слагаемые: " + formatValue v
               else "остальные слагаемые " + name + ": " + formatValue v
           | _ -> "остаток " + name + " = " + formatValue v))
    |> String.concat ", "

let traceFired (rule: Rule) (before: LispValue) (after: LispValue) : unit =
    let show v = try Printer.prettyPrint v with _ -> "#<?>"
    Debug.out().WriteLine("правило " + rule.Name + ": " + show before + " → " + show after)
