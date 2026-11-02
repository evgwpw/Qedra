// Паттерн-матчинг для S-выражений
// ?x — переменная паттерна, связывается с любым подвыражением
// Используется для rewrite rules и упрощения
module PatternMatching

open Types
open Numeric

// Привязки: имя переменной паттерна → значение
type Bindings = Map<string, LispValue>

// Является ли символ переменной паттерна (?name)
let isPatternVar (s: string) : bool =
    // порядковое сравнение: StartsWith(string) учитывает культуру и в горячем пути упрощателя заметно дороже (Шаг AC.3)
    s.Length > 1 && s.[0] = '?'

// Пустые привязки
let noBindings : Bindings = Map.empty

// Сопоставление паттерна с выражением
// Возвращает Some(bindings) если удалось, None если нет
// Если переменная уже связана — проверяем структурное равенство
let rec matchPattern (pattern: LispValue) (expr: LispValue) (bindings: Bindings) : Bindings option =
    match pattern, expr with
    // Переменная паттерна ?x — связывается с любым значением
    | LispSym name, _ when isPatternVar name ->
        match Map.tryFind name bindings with
        | Some existing when structEqual existing expr -> Some bindings  // уже связана, та же
        | Some _ -> None  // уже связана, другая — несовпадение
        | None -> Some (Map.add name expr bindings)  // новая привязка
    // Списки одинаковой длины — рекурсивное сопоставление
    | LispList pArgs, LispList eArgs when pArgs.Length = eArgs.Length ->
        matchList pArgs eArgs bindings
    // Прочее — структурное равенство
    | _ when structEqual pattern expr -> Some bindings
    | _ -> None

and matchList (patterns: LispValue list) (exprs: LispValue list) (bindings: Bindings) : Bindings option =
    match patterns, exprs with
    | [], [] -> Some bindings
    | p :: ps, e :: es ->
        match matchPattern p e bindings with
        | Some b -> matchList ps es b
        | None -> None
    | _ -> None

// Подстановка: заменяет переменные паттерна в шаблоне их значениями
let rec substitute (bindings: Bindings) (template: LispValue) : LispValue =
    match template with
    | LispSym name when isPatternVar name ->
        match Map.tryFind name bindings with
        | Some v -> v
        | None -> template  // несвязанная — оставляем как есть
    | LispList items -> LispList (List.map (substitute bindings) items)
    | _ -> template

// Применить одно правило: если паттерн совпадает, вернуть replacement с подстановкой
let applyRule (pattern: LispValue) (replacement: LispValue) (expr: LispValue) : LispValue option =
    match matchPattern pattern expr noBindings with
    | Some bindings -> Some (substitute bindings replacement)
    | None -> None

// Попробовать список правил, вернуть первый успешный
let applyRules (rules: (LispValue * LispValue) list) (expr: LispValue) : LispValue option =
    rules |> List.tryPick (fun (pattern, replacement) -> applyRule pattern replacement expr)

// Рекурсивно применить правила ко всем подвыражениям, пока не стабилизируется
let rewriteUntilFixpoint (rules: (LispValue * LispValue) list) (expr: LispValue) : LispValue =
    let rec rewriteOnce (e: LispValue) : LispValue * bool =
        // Сначала пытаемся применить правило к самому выражению
        match applyRules rules e with
        | Some result -> (result, true)  // правило сработало
        | None ->
            // Иначе рекурсивно применяем к аргументам
            match e with
            | LispList items ->
                let newItems, changed = items |> List.map rewriteOnce |> List.unzip
                let anyChanged = List.exists id changed
                if anyChanged then
                    (LispList newItems, true)
                else
                    (e, false)
            | _ -> (e, false)

    let rec loop (e: LispValue) : LispValue =
        let result, changed = rewriteOnce e
        if changed then loop result else result
    loop expr

// --- Базовый набор правил упрощения ---

let simplifyRules : (LispValue * LispValue) list = [
    // (+ ?x ?x) → (* 2 ?x) — объединение одинаковых
    (LispList [LispSym "+"; LispSym "?x"; LispSym "?x"],
     LispList [LispSym "*"; LispInteger 2I; LispSym "?x"])

    // (+ (* ?a ?x) ?x) → (* (+ ?a 1) ?x) — коэффициент + одиночный терм
    (LispList [LispSym "+";
              LispList [LispSym "*"; LispSym "?a"; LispSym "?x"];
              LispSym "?x"],
     LispList [LispSym "*";
              LispList [LispSym "+"; LispSym "?a"; LispInteger 1I];
              LispSym "?x"])

    // (+ ?x (* ?a ?x)) → (* (+ ?a 1) ?x) — то же в другом порядке
    (LispList [LispSym "+";
              LispSym "?x";
              LispList [LispSym "*"; LispSym "?a"; LispSym "?x"]],
     LispList [LispSym "*";
              LispList [LispSym "+"; LispSym "?a"; LispInteger 1I];
              LispSym "?x"])

    // (- ?x ?x) → 0 — вычитание одинаковых (дублирует simplifySub, но для полноты)
    (LispList [LispSym "-"; LispSym "?x"; LispSym "?x"],
     LispInteger 0I)
]

// --- Правила раскрытия скобок (expand) ---

let expandRules : (LispValue * LispValue) list = [
    // (* ?a (+ ?b ?c)) → (+ (* ?a ?b) (* ?a ?c))
    (LispList [LispSym "*"; LispSym "?a";
              LispList [LispSym "+"; LispSym "?b"; LispSym "?c"]],
     LispList [LispSym "+";
              LispList [LispSym "*"; LispSym "?a"; LispSym "?b"];
              LispList [LispSym "*"; LispSym "?a"; LispSym "?c"]])

    // (* (+ ?b ?c) ?a) → (+ (* ?b ?a) (* ?c ?a))
    (LispList [LispSym "*";
              LispList [LispSym "+"; LispSym "?b"; LispSym "?c"];
              LispSym "?a"],
     LispList [LispSym "+";
              LispList [LispSym "*"; LispSym "?b"; LispSym "?a"];
              LispList [LispSym "*"; LispSym "?c"; LispSym "?a"]])
]

// --- Тригонометрические тождества (Шаг 8c) ---
// Правила применяются в simplify ПОСЛЕ алгоритмического упрощения (Шаг 13: основная работа с
// суммами — в Simplify.pythag; здесь — простые бинарные формы и tan/cot/sec/csc → sin/cos).
// Обратных правил нет (sin/cos → tan), поэтому применение завершается.

let private sq (fn: string) : LispValue =
    // (fn ?x)² — для пифагоровых правил
    LispList [LispSym "^"; LispList [LispSym fn; LispSym "?x"]; LispInteger 2I]

let trigRules : (LispValue * LispValue) list = [
    // Пифагор: sin²x + cos²x → 1 (оба порядка слагаемых)
    (LispList [LispSym "+"; sq "sin"; sq "cos"], LispInteger 1I)
    (LispList [LispSym "+"; sq "cos"; sq "sin"], LispInteger 1I)

    // 1 − cos²x → sin²x
    (LispList [LispSym "-"; LispInteger 1I; sq "cos"], sq "sin")
    // 1 − sin²x → cos²x
    (LispList [LispSym "-"; LispInteger 1I; sq "sin"], sq "cos")

    // Канонические формы Шага 13: 1 - cos²x = (+ 1 (* -1 (^ (cos x) 2))) → sin²x и т.п.
    // (n-арные суммы и коэффициенты при sin²/cos² обрабатывает Simplify.simplifySum — pythag)
    (LispList [LispSym "+"; LispInteger 1I; LispList [LispSym "*"; LispInteger -1I; sq "cos"]], sq "sin")
    (LispList [LispSym "+"; LispInteger 1I; LispList [LispSym "*"; LispInteger -1I; sq "sin"]], sq "cos")

    // tan → sin/cos, cot → cos/sin, sec → 1/cos, csc → 1/sin
    (LispList [LispSym "tan"; LispSym "?x"],
     LispList [LispSym "/"; LispList [LispSym "sin"; LispSym "?x"]; LispList [LispSym "cos"; LispSym "?x"]])
    (LispList [LispSym "cot"; LispSym "?x"],
     LispList [LispSym "/"; LispList [LispSym "cos"; LispSym "?x"]; LispList [LispSym "sin"; LispSym "?x"]])
    (LispList [LispSym "sec"; LispSym "?x"],
     LispList [LispSym "/"; LispInteger 1I; LispList [LispSym "cos"; LispSym "?x"]])
    (LispList [LispSym "csc"; LispSym "?x"],
     LispList [LispSym "/"; LispInteger 1I; LispList [LispSym "sin"; LispSym "?x"]])
]
