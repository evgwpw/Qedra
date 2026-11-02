// Инфикс-ридер математической записи (Шаг 8b, расширен в Шаге 21) — обратен MathPrinter.fs
// «2x^2 + 3x - 5» → Lisp-дерево. Round-trip: mathParse(mathPrint e) = e
// на канонических формах (n-ary цепочки -, /; унарный минус = (- 0 x)).
//
// Два входа:
//   mathParse        : string -> LispValue        одно выражение (без операторов :=), как раньше
//   mathParseProgram : string -> LispValue list   программа входного языка (Шаг 21): операторы через «;»/перевод строки
//
// Грамматика выражения (низ→высок):
//   or → and → not → отношения (= /= ≠ < > <= >= ≤ ≥ in ∈ ∉; не ассоциативны)
//   → ∪ и \ (теоретико-множественные) → ∩ → +/- → */÷ (с неявным умножением)
//   → унарный -/+ → ^ (правоассоц) → постфикс (v[i], m[i, j], n!) → primary
//   primary: число, дробь int/int, строка "..", имя, f(args), (expr), [a, b] (вектор), {a, b} (множество), ∅
// Оператор программы: expr | имя := expr | имя := | f(п1, п2) := expr | имя :∈ домен (или :in)
//
// AST (обычные Lisp-формы с явными тегами):
//   (:= a e)            присваивание;        (:= a) — снять присваивание
//   (:= (f x y) body)   определение функции
//   (:declare x D)      декларация x :∈ D;   (:declare x) — снять декларации (x :∈);   (:in x D) — отношение x ∈ D;  x ∉ D → (not (:in x D))
//   (m-vector a b ..)   вектор/матрица (вложенные);  (m-set a b ..) — множество;  (m-index v i j ..) — v[i, j] (индексы с 1)
//   (= a b) (/= a b) (< a b) (> a b) (<= a b) (>= a b)   отношения;  (and ..) (or ..) (not a)
//   (union a b) (intersection a b) (set-difference a b)   ∪ ∩ \ ;  (factorial n) — n!
//   имена: π→pi, ∞→inf, ⅈ→%i, ℕℤℚℝℂ → naturals integers rationals reals complexes; true/false → #t/#f; e остаётся символом e
module MathReader

open System
open System.Globalization
open Types
open Numeric

// --- Токены ---
type private Tok =
    | TInt of bigint        // целочисленный литерал: 42
    | TFloat of double       // дробный/экспоненциальный литерал: 2.5, 1e10, 1E+10
    | TStr of string         // строка в двойных кавычках
    | TName of string        // имя (греческие буквы транслитерированы: π → pi)
    | TOp of string          // оператор/скобка; ∈≠≤≥∉ нормализованы к in, /=, <=, >=, notin
    | TSep                   // разделитель операторов: «;» или перевод строки (только в режиме программы)
    | TEof

// Токен с позицией (строка и позиция в строке, с 1) — для сообщений об ошибках
type private Token = { T: Tok; Line: int; Col: int }

// Транслитерация греческих букв и обозначений доменов (фиксируем как решение:
// π в проекте — это символ pi). Прочие юникод-буквы — как есть.
let private greekMap : Map<char, string> =
    Map.ofList [
        'α', "alpha"; 'β', "beta"; 'γ', "gamma"; 'δ', "delta"; 'ε', "epsilon"
        'θ', "theta"; 'λ', "lambda"; 'μ', "mu"; 'ν', "nu"; 'ξ', "xi"
        'ρ', "rho"; 'σ', "sigma"; 'τ', "tau"; 'φ', "phi"; 'χ', "chi"
        'ψ', "psi"; 'ω', "omega"; 'π', "pi"
        // Шаг 21l.0: заглавные Γ/Ψ (нормализуются в gamma/psi при разборе вызова)
        'Γ', "Gamma"; 'Ψ', "Psi"
        // Шаг 21: домены (переменные domain.lisp)
        'ℕ', "naturals"; 'ℤ', "integers"; 'ℚ', "rationals"; 'ℝ', "reals"; 'ℂ', "complexes"
    ]

let private transliterate (name: string) : string =
    name |> String.collect (fun c ->
        match Map.tryFind c greekMap with
        | Some s -> s
        | None -> string c)

let private isNameChar (c: char) : bool = Char.IsLetter c || Char.IsDigit c || c = '_'

// Токен, после которого перевод строки — продолжение выражения (висячий оператор)
let private continuesLine (t: Tok) : bool =
    match t with
    | TOp o -> not (o = ")" || o = "]" || o = "}" || o = "!")
    | _ -> false

// Токенизация: числа (int/float/экспонента), имена (юникод-буквы), строки, операторы.
// program = true: перевод строки и «;» — разделители операторов (внутри скобок перевод строки — пробел),
// комментарии // до конца строки (в обоих режимах)
let private tokenize (who: string) (program: bool) (src: string) : Token[] =
    let toks = ResizeArray<Token>()
    let n = src.Length
    let mutable i = 0
    let mutable line = 1
    let mutable lineStart = 0
    let mutable depth = 0
    let add (t: Tok) (ln: int) (col: int) = toks.Add { T = t; Line = ln; Col = col }
    let err (ln: int) (col: int) (msg: string) : unit = failwithf "%s: строка %d, позиция %d: %s" who ln col msg
    while i < n do
        let c = src.[i]
        let col = i - lineStart + 1
        if c = '\n' then
            if program && depth = 0 && toks.Count > 0 && toks.[toks.Count - 1].T <> TSep
               && not (continuesLine toks.[toks.Count - 1].T) then
                add TSep line col
            i <- i + 1
            line <- line + 1
            lineStart <- i
        elif Char.IsWhiteSpace c then i <- i + 1
        elif c = '/' && i + 1 < n && src.[i + 1] = '/' then
            // комментарий до конца строки (перевод строки остаётся разделителем)
            while i < n && src.[i] <> '\n' do i <- i + 1
        elif Char.IsDigit c then
            // --- Число: digits [ . digits ] [ (e|E) [+|-] digits ] ---
            let start = i
            let mutable j = i
            while j < n && Char.IsDigit src.[j] do j <- j + 1
            // дробная часть: . digits — тогда это float
            let mutable isFloat = false
            if j < n && src.[j] = '.' && j + 1 < n && Char.IsDigit src.[j + 1] then
                j <- j + 1
                isFloat <- true
                while j < n && Char.IsDigit src.[j] do j <- j + 1
            // Экспонента: e/E и ОБЯЗАТЕЛЬНО цифры после (иначе «2e» — это 2 * символ e)
            if (j < n && (src.[j] = 'e' || src.[j] = 'E')) then
                let mutable k = j + 1
                if k < n && (src.[k] = '+' || src.[k] = '-') then k <- k + 1
                if k < n && Char.IsDigit src.[k] then
                    while k < n && Char.IsDigit src.[k] do k <- k + 1
                    j <- k
                    isFloat <- true
            let text = src.[start .. j - 1]
            if isFloat then add (TFloat (Double.Parse(text, NumberStyles.Float, CultureInfo.InvariantCulture))) line col
            else add (TInt (bigint.Parse text)) line col
            i <- j
        elif c = '"' then
            // --- Строка: "..." с экранированием \" \\ \n ---
            let sb = System.Text.StringBuilder()
            let mutable j = i + 1
            let mutable closed = false
            while not closed && j < n do
                let d = src.[j]
                if d = '"' then
                    closed <- true
                    j <- j + 1
                elif d = '\\' && j + 1 < n then
                    (match src.[j + 1] with
                     | 'n' -> sb.Append '\n' |> ignore
                     | other -> sb.Append other |> ignore)
                    j <- j + 2
                elif d = '\n' then
                    err line col "строка не закрыта до конца строки"
                else
                    sb.Append d |> ignore
                    j <- j + 1
            if not closed then err line col "строка не закрыта"
            add (TStr (sb.ToString())) line col
            i <- j
        elif c = 'ⅈ' then
            // мнимая единица ⅈ (U+2148) = %i
            add (TName "%i") line col
            i <- i + 1
        elif c = '∞' then
            add (TName "inf") line col
            i <- i + 1
        elif Char.IsLetter c || c = '_' || (c = '%' && i + 1 < n && Char.IsLetter src.[i + 1]) then
            // --- Имя: буква/подчёркивание (или «%» перед буквой — %i, Шаг 18), далее буквы/цифры/подчёркивания;
            //     «?» в конце имени перед «(» — часть имени (in?, subset?) ---
            let start = i
            let mutable j = i + (if c = '%' then 1 else 0)
            while j < n && isNameChar src.[j] do j <- j + 1
            if j + 1 < n && src.[j] = '?' && src.[j + 1] = '(' then j <- j + 1
            let word = src.[start .. j - 1]
            (match word with
             | "and" | "or" | "not" | "in" -> add (TOp word) line col
             | _ -> add (TName (transliterate word)) line col)
            i <- j
        elif c = ':' then
            // := присваивание;  :∈ и :in — декларация
            if i + 1 < n && src.[i + 1] = '=' then (add (TOp ":=") line col; i <- i + 2)
            elif i + 1 < n && src.[i + 1] = '∈' then (add (TOp ":in") line col; i <- i + 2)
            elif i + 2 < n && src.[i + 1] = 'i' && src.[i + 2] = 'n' && not (i + 3 < n && isNameChar src.[i + 3]) then
                add (TOp ":in") line col
                i <- i + 3
            else err line col "после «:» ожидалось «=» или «∈»/«in»"
        elif c = '<' && i + 1 < n && src.[i + 1] = '=' then (add (TOp "<=") line col; i <- i + 2)
        elif c = '>' && i + 1 < n && src.[i + 1] = '=' then (add (TOp ">=") line col; i <- i + 2)
        elif c = '/' && i + 1 < n && src.[i + 1] = '=' then (add (TOp "/=") line col; i <- i + 2)
        elif c = '!' && i + 1 < n && src.[i + 1] = '=' then (add (TOp "/=") line col; i <- i + 2)
        elif c = '<' && i + 1 < n && src.[i + 1] = '>' then (add (TOp "/=") line col; i <- i + 2)
        elif c = '≠' then (add (TOp "/=") line col; i <- i + 1)
        elif c = '≤' then (add (TOp "<=") line col; i <- i + 1)
        elif c = '≥' then (add (TOp ">=") line col; i <- i + 1)
        elif c = '∈' then (add (TOp "in") line col; i <- i + 1)
        elif c = '∉' then (add (TOp "notin") line col; i <- i + 1)
        elif c = ';' then
            if program then
                (if toks.Count > 0 && toks.[toks.Count - 1].T <> TSep then add TSep line col)
                i <- i + 1
            else err line col "недопустимый символ «;»"
        elif c = '(' || c = '[' || c = '{' then
            depth <- depth + 1
            add (TOp (string c)) line col
            i <- i + 1
        elif c = ')' || c = ']' || c = '}' then
            depth <- max 0 (depth - 1)
            add (TOp (string c)) line col
            i <- i + 1
        elif "+-*/^=,!<>\\∪∩∅'".IndexOf c >= 0 then
            add (TOp (string c)) line col
            i <- i + 1
        else
            err line col (sprintf "недопустимый символ «%c»" c)
    add TEof line (n - lineStart + 1)
    toks.ToArray()

// --- Состояние парсера: массив токенов + позиция ---
type private Parser =
    { Toks: Token[]
      mutable Pos: int
      Who: string
      // Шаг 21d: имя файла для позиций форм AST (вызовы и операторы) в побочной таблице; null — позиции не пишем
      File: string
      // y′: узлы-символы переменной (x) в сгенерированных производных; dsolve(…, y(t)) подменяет их на t
      Primes: System.Collections.Generic.HashSet<LispValue> }

let private cur (p: Parser) : Token = p.Toks.[p.Pos]
let private peek (p: Parser) : Tok = (cur p).T
let private peekAt (p: Parser) (k: int) : Tok =
    if p.Pos + k < p.Toks.Length then p.Toks.[p.Pos + k].T else TEof
let private advance (p: Parser) : Tok =
    let t = cur p
    if p.Pos < p.Toks.Length - 1 then p.Pos <- p.Pos + 1
    t.T

let private describe (t: Tok) : string =
    match t with
    | TInt n -> string n
    | TFloat f -> string f
    | TStr s -> "\"" + s + "\""
    | TName s -> s
    | TOp o -> o
    | TSep -> "конец оператора"
    | TEof -> "конец ввода"

// Запомнить позицию токена t для формы AST (по ссылке на объект формы; см. Types.srcPositions)
let private markAt (p: Parser) (t: Token) (form: LispValue) : LispValue =
    match form with
    | LispList (_ :: _) when not (isNull p.File) && isNull (posOf form) ->
        setPos form (SrcPos.Make(p.File, t.Line, t.Col))
    | _ -> ()
    form

// Формы без своей позиции (операторы +, *, векторы...) наследуют позицию ближайшей объемлющей отмеченной формы
let rec private spreadPos (pos: SrcPos) (v: LispValue) : unit =
    match v with
    | LispList items ->
        let own = posOf v
        let here = if isNull own then (setPos v pos; pos) else own
        for it in items do spreadPos here it
    | _ -> ()

// Ошибка разбора с позицией текущего токена
let private fail (p: Parser) (msg: string) : 'a =
    let t = cur p
    failwithf "%s: строка %d, позиция %d: %s" p.Who t.Line t.Col msg

// Унарный минус — каноническая форма проекта: (- 0 x), как (- 0 (cos x)).
// ВНИМАНИЕ: применяется и к числам: «-5» → (- 0 5) (так хранит simplify)
let private negate (e: LispValue) : LispValue =
    LispList [LispSym "-"; LispInteger 0I; e]

// y′ в dsolve: сгенерированные символы x → переменная tv; (at D (= tv tv)) → D (явное y′(t))
let rec private primesTo (p: Parser) (tv: string) (v: LispValue) : LispValue =
    if p.Primes.Contains v then LispSym tv
    else
        match v with
        | LispList [LispSym "at"; d; LispList [LispSym "="; xs; LispSym a]] when p.Primes.Contains xs && a = tv ->
            primesTo p tv d
        | LispList items ->
            let r = LispList (List.map (primesTo p tv) items)
            let pos = posOf v
            if not (isNull pos) then setPos r pos
            r
        | _ -> v

// Начало primary — признак НЕЯВНОГО умножения (2x, 3(x+1), (x)(y), 2sin(x))
let private startsPrimary (t: Tok) : bool =
    match t with
    | TInt _ | TFloat _ | TName _ -> true
    | TOp "(" -> true
    | _ -> false

let private expectOp (p: Parser) (op: string) : unit =
    match peek p with
    | TOp o when o = op -> ignore (advance p)
    | t -> fail p (sprintf "ожидалось «%s», получено «%s»" op (describe t))

// primary: число / рациональная дробь int/int / строка / имя / вызов f(x) / (expr) / [..] / {..} / ∅, затем постфикс.
// allowRat: рациональный литерал int/int (1/3) распознаётся ТОЛЬКО в начале
// mul-цепочки — там его всегда ставит MathPrinter («1/3», «1/3*x^3»).
// В середине цепочки после «/» целые — обычные операнды деления («8/2/2»,
// «x/2»), иначе «2/3/4» читалось бы как 2/((3/4)) — неверно
let rec private parsePrimary (p: Parser) (allowRat: bool) : LispValue =
    let atom =
        match peek p with
        | TInt a ->
            ignore (advance p)
            // целое / целое → рациональное ЧИСЛО (1/3), не форма (/ 1 3),
            // если за знаменателем НЕ следует очередной «/» (иначе цепочка делений)
            let isRat () =
                allowRat && peek p = TOp "/"
                // нулевой знаменатель — не литерал: остаётся формой (/ a 0), ошибка — при вычислении
                && (match peekAt p 1 with TInt d -> not d.IsZero && peekAt p 2 <> TOp "/" | _ -> false)
            if isRat () then
                ignore (advance p)                       // «/»
                match advance p with                     // знаменатель
                | TInt b -> makeRational a b
                | _ -> fail p "ожидался знаменатель"
            else LispInteger a
        | TFloat f ->
            ignore (advance p)
            LispFloat f
        | TStr s ->
            ignore (advance p)
            LispStr s
        | TName name ->
            let nameTok = cur p
            ignore (advance p)
            if peek p = TOp "'" then
                // ODE.0: y′, y″, y‴ — производные неизвестной функции y(x); y′(0) — в точке, через at.
                let mutable k = 0
                while peek p = TOp "'" do
                    ignore (advance p)
                    k <- k + 1
                let mkx () =
                    let xs = LispSym "x"
                    p.Primes.Add xs |> ignore
                    xs
                let mutable deriv = LispList [LispSym "diff"; LispList [LispSym name; mkx ()]; mkx ()]
                for _ in 2 .. k do
                    deriv <- LispList [LispSym "diff"; deriv; mkx ()]
                match peek p with
                | TOp "(" ->
                    ignore (advance p)
                    let items = parseItems p ")"
                    match items with
                    | [arg] -> markAt p nameTok (LispList [LispSym "at"; deriv; LispList [LispSym "="; mkx (); arg]])
                    | _ -> fail p "у производной в точке ожидается один аргумент"
                | _ -> markAt p nameTok deriv
            else
                match peek p with
                // Вызов функции: имя + скобки; аргументы через запятую (Шаг 18): sin(x + 1) → (sin (+ x 1)),
                // solve(x^2 = 4, x) → (solve (= (^ x 2) 4) x); аргумент может быть равенством; f() — без аргументов
                | TOp "(" ->
                    ignore (advance p)
                    let items = parseItems p ")"
                    // Шаг 21h: rootsum(E, t, Q) — язык; Lisp-форма (root-sum t Q E)
                    // Шаг 21l.0: C(n, k) — биномиальный коэффициент; Γ/ψ — имена gamma/psi (греческая буква
                    // транслитерируется в gamma/psi, но заглавная Γ даёт имя Gamma — нормализуем)
                    (match name, items with
                     | "rootsum", [e; (LispSym _ as tv); q] -> markAt p nameTok (LispList [LispSym "root-sum"; tv; q; e])
                     | "C", [n; k] -> markAt p nameTok (LispList [LispSym "binomial"; n; k])
                     | "Gamma", xs -> markAt p nameTok (LispList (LispSym "gamma" :: xs))
                     | "Psi", xs -> markAt p nameTok (LispList (LispSym "psi" :: xs))
                     // SFn.2a: BesselJ(ν, x), AiryAi(x), LegendreP(n, x) — головы Lisp
                     | "BesselJ", xs -> markAt p nameTok (LispList (LispSym "bessel-j" :: xs))
                     | "BesselY", xs -> markAt p nameTok (LispList (LispSym "bessel-y" :: xs))
                     | "BesselI", xs -> markAt p nameTok (LispList (LispSym "bessel-i" :: xs))
                     | "BesselK", xs -> markAt p nameTok (LispList (LispSym "bessel-k" :: xs))
                     | "AiryAi", xs -> markAt p nameTok (LispList (LispSym "airy-ai" :: xs))
                     | "AiryBi", xs -> markAt p nameTok (LispList (LispSym "airy-bi" :: xs))
                     | "AiryAiPrime", xs -> markAt p nameTok (LispList (LispSym "airy-ai-prime" :: xs))
                     | "AiryBiPrime", xs -> markAt p nameTok (LispList (LispSym "airy-bi-prime" :: xs))
                     | "LegendreP", xs -> markAt p nameTok (LispList (LispSym "legendre-p" :: xs))
                     | "LegendreQ", xs -> markAt p nameTok (LispList (LispSym "legendre-q" :: xs))
                     | "dsolve", (_ :: LispList [LispSym _; LispSym tv] :: _) when tv <> "x" ->
                         // y′ по переменной из y(t) во втором аргументе dsolve; y′(t) — производная без «в точке»
                         markAt p nameTok (LispList (LispSym name :: List.map (primesTo p tv) items))
                     | _ -> markAt p nameTok (LispList (LispSym name :: items)))
                | _ ->
                    match name with
                    | "true" -> LispBool true
                    | "false" -> LispBool false
                    | _ -> LispSym name
        | TOp "(" ->
            ignore (advance p)
            let e = parseExpr p
            // Шаг 21d: «(a, b)» и «(a, b]» — интервалы (запятая в круглых скобках иначе была бы ошибкой)
            if peek p = TOp "," then
                ignore (advance p)
                let b = parseExpr p
                match peek p with
                | TOp ")" -> ignore (advance p); LispList [LispSym ":interval"; e; b; LispSym "open"; LispSym "open"]
                | TOp "]" -> ignore (advance p); LispList [LispSym ":interval"; e; b; LispSym "open"; LispSym "closed"]
                | t -> fail p (sprintf "ожидалось «)» или «]» (конец интервала), получено «%s»" (describe t))
            else
                expectOp p ")"
                e
        | TOp "[" ->
            ignore (advance p)
            // Шаг 21d: «[a, b)» — интервал, закрытый слева и открытый справа; «[a, b]» — вектор (в позиции домена
            // вычислитель читает его как закрытый интервал)
            let items = parseItemsUntil p [ "]"; ")" ]
            match items with
            | [ a; b ], ")" -> LispList [LispSym ":interval"; a; b; LispSym "closed"; LispSym "open"]
            | _, ")" -> fail p "интервал [a, b) задаётся двумя границами"
            | xs, _ -> LispList (LispSym "m-vector" :: xs)
        | TOp "{" ->
            ignore (advance p)
            LispList (LispSym "m-set" :: parseItems p "}")
        | TOp "∅" ->
            ignore (advance p)
            LispList [LispSym "m-set"]
        | t -> fail p (sprintf "неожиданный токен «%s»" (describe t))
    parsePostfix p atom

// Список выражений через запятую до закрывающей скобки (скобка поглощается); пустой список допустим
and private parseItems (p: Parser) (closing: string) : LispValue list =
    if peek p = TOp closing then
        ignore (advance p)
        []
    else
        let items = ResizeArray<LispValue>()
        items.Add (parseItem p)
        while peek p = TOp "," do
            ignore (advance p)
            items.Add (parseItem p)
        expectOp p closing
        List.ofSeq items

// Шаг 21d: то же, но закрывающей может быть любая из скобок closings; возвращает элементы и закрывшую скобку
and private parseItemsUntil (p: Parser) (closings: string list) : LispValue list * string =
    let isClosing () = match peek p with TOp o when List.contains o closings -> true | _ -> false
    let closeWith () =
        match advance p with
        | TOp o -> o
        | _ -> ""
    if isClosing () then [], closeWith ()
    else
        let items = ResizeArray<LispValue>()
        items.Add (parseItem p)
        while peek p = TOp "," do
            ignore (advance p)
            items.Add (parseItem p)
        if isClosing () then List.ofSeq items, closeWith ()
        else
            expectOp p closings.Head        // сообщение как раньше: «ожидалось «]», получено …»
            [], ""

// Элемент списка аргументов: выражение или присваивание (Шаг 21a): a := e, v[i] := e (правоассоциативно: a := b := 1).
// Нужно для prog(a := 1, ...) и параметров по умолчанию f(n, s := 0) := ...
and private parseItem (p: Parser) : LispValue =
    let lhs = parseExpr p
    match peek p with
    | TOp ":=" ->
        (match lhs with
         | LispSym _ | LispList (LispSym "m-index" :: LispSym _ :: _ :: _) -> ()
         | _ -> fail p "слева от «:=» ожидалось имя или v[i]")
        ignore (advance p)
        LispList [LispSym ":="; lhs; parseItem p]
    | _ -> lhs

// Постфикс: v[i], m[i, j] (индексы с 1) и n! (факториал); можно подряд: v[1][2], n!!
and private parsePostfix (p: Parser) (e: LispValue) : LispValue =
    match peek p with
    | TOp "[" ->
        let bracket = cur p
        ignore (advance p)
        let idx = parseItems p "]"
        if idx.IsEmpty then fail p "пустой индекс"
        parsePostfix p (markAt p bracket (LispList (LispSym "m-index" :: e :: idx)))
    | TOp "!" ->
        ignore (advance p)
        parsePostfix p (LispList [LispSym "factorial"; e])
    | _ -> e

// Степень: правоассоциативна (x^y^2 = x^(y^2)); показатель может начинаться
// с унарного минуса: 2^-3. База — primary (унарный минус слабее: -x^2 = -(x^2))
and private parsePow (p: Parser) (allowRat: bool) : LispValue =
    let bse = parsePrimary p allowRat
    match peek p with
    | TOp "^" ->
        ignore (advance p)
        LispList [LispSym "^"; bse; parseUnary p false]
    | _ -> bse

// Унарный +/-: правоассоциативен (- -x, -(x + 1)); по силе между * и ^:
// -x^2 = -(x^2), -x*y = (-x)*y. Операнд наследует allowRat («-1/3»)
and private parseUnary (p: Parser) (allowRat: bool) : LispValue =
    match peek p with
    | TOp "-" ->
        ignore (advance p)
        negate (parseUnary p allowRat)
    | TOp "+" ->
        ignore (advance p)
        parseUnary p allowRat
    | _ -> parsePow p allowRat

// Умножение/деление + НЕЯВНОЕ умножение (два primary подряд = умножение).
// Левоассоциативно: 1/2x = (1/2)*x — сознательное решение (простота,
// MathPrinter для рациональных множителей всегда пишет явную «*»).
// Канонизация: только «*» → n-ary (* a b c); только «/» → n-ary (/ a b c);
// смешанные — вложенные левоассоциативные формы.
// Рациональный литерал — только первый множитель (allowRat, см. parsePrimary)
and private parseMul (p: Parser) : LispValue =
    let first = parseUnary p true
    // накопленные (операция, множитель); «*» — явная или неявная, «/» — деление
    let factors = ResizeArray()
    let rec loop () =
        match peek p with
        | TOp "*" ->
            ignore (advance p)
            factors.Add ("*", parseUnary p false)
            loop ()
        | TOp "/" ->
            ignore (advance p)
            factors.Add ("/", parseUnary p false)
            loop ()
        | t when startsPrimary t ->
            // неявное умножение: 2x, 3(x + 1), (x + 1)(y + 2), 2sin(x)
            factors.Add ("*", parseUnary p false)
            loop ()
        | _ -> ()
    loop ()
    if factors.Count = 0 then first
    else
        let ops = factors |> Seq.map (fun (o, _) -> o) |> Seq.distinct |> List.ofSeq
        let args = first :: (factors |> Seq.map snd |> List.ofSeq)
        match ops with
        | [ "*"] -> LispList (LispSym "*" :: args)
        | [ "/" ] -> LispList (LispSym "/" :: args)
        | _ ->
            // смешанная цепочка: левоассоциативная вложенность
            (first, factors |> Seq.toArray)
            ||> Array.fold (fun acc (o, v) ->
                LispList [LispSym (if o = "*" then "*" else "/"); acc; v])

// Сложение/вычитание, левоассоциативно.
// Канонизация: только «+» → n-ary (+ a b c); только «-» → n-ary (- a b c)
// (именно так печатает MathPrinter и хранит simplify); смешанные — вложенные
and private parseSum (p: Parser) : LispValue =
    let first = parseMul p
    let terms = ResizeArray()
    let rec loop () =
        match peek p with
        | TOp "+" ->
            ignore (advance p)
            terms.Add ("+", parseMul p)
            loop ()
        | TOp "-" ->
            ignore (advance p)
            terms.Add ("-", parseMul p)
            loop ()
        | _ -> ()
    loop ()
    if terms.Count = 0 then first
    else
        let ops = terms |> Seq.map fst |> Seq.distinct |> List.ofSeq
        let args = first :: (terms |> Seq.map snd |> List.ofSeq)
        match ops with
        | [ "+" ] -> LispList (LispSym "+" :: args)
        | [ "-" ] -> LispList (LispSym "-" :: args)
        | _ ->
            (first, terms |> Seq.toArray)
            ||> Array.fold (fun acc (o, v) ->
                LispList [LispSym o; acc; v])

// Пересечение ∩ (левоассоциативно): A ∩ B ∩ C = (intersection (intersection A B) C)
and private parseSetI (p: Parser) : LispValue =
    let mutable acc = parseSum p
    while peek p = TOp "∩" do
        ignore (advance p)
        acc <- LispList [LispSym "intersection"; acc; parseSum p]
    acc

// Объединение ∪ и разность \ (один уровень, левоассоциативно)
and private parseSetU (p: Parser) : LispValue =
    let mutable acc = parseSetI p
    let mutable go = true
    while go do
        match peek p with
        | TOp "∪" ->
            ignore (advance p)
            acc <- LispList [LispSym "union"; acc; parseSetI p]
        | TOp "\\" ->
            ignore (advance p)
            acc <- LispList [LispSym "set-difference"; acc; parseSetI p]
        | _ -> go <- false
    acc

// Отношение (не ассоциативно): a = b, a /= b, a < b, a > b, a <= b, a >= b, x ∈ D, x ∉ D
and private parseRel (p: Parser) : LispValue =
    let lhs = parseSetU p
    let bin (name: string) =
        ignore (advance p)
        LispList [LispSym name; lhs; parseSetU p]
    match peek p with
    | TOp "=" -> bin "="
    | TOp "/=" -> bin "/="
    | TOp "<" -> bin "<"
    | TOp ">" -> bin ">"
    | TOp "<=" -> bin "<="
    | TOp ">=" -> bin ">="
    | TOp "in" -> bin ":in"
    | TOp "notin" -> LispList [LispSym "not"; bin ":in"]
    | _ -> lhs

// not (префиксный, слабее отношений): not a = b → (not (= a b))
and private parseNot (p: Parser) : LispValue =
    match peek p with
    | TOp "not" ->
        ignore (advance p)
        LispList [LispSym "not"; parseNot p]
    | _ -> parseRel p

and private parseAnd (p: Parser) : LispValue =
    let first = parseNot p
    if peek p = TOp "and" then
        let items = ResizeArray [first]
        while peek p = TOp "and" do
            ignore (advance p)
            items.Add (parseNot p)
        LispList (LispSym "and" :: List.ofSeq items)
    else first

// Выражение целиком (низший приоритет — or)
and private parseExpr (p: Parser) : LispValue =
    let first = parseAnd p
    if peek p = TOp "or" then
        let items = ResizeArray [first]
        while peek p = TOp "or" do
            ignore (advance p)
            items.Add (parseAnd p)
        LispList (LispSym "or" :: List.ofSeq items)
    else first

// Заголовок определения функции: имя ( имена через запятую ) := — признак определения, а не вызова
let private isFunDef (p: Parser) : bool =
    match peek p, peekAt p 1 with
    | TName _, TOp "(" ->
        // сканируем с токена k: пусто или параметры через запятую (имя или имя := значение_по_умолчанию),
        // затем «)» и «:=». Шаг 21a: значение по умолчанию — произвольное выражение (скобки учитываются по глубине)
        let rec scan (k: int) (depth: int) (itemStart: bool) (afterComma: bool) : bool =
            match peekAt p k with
            | TEof | TSep -> false
            | TOp ("(" | "[" | "{") -> scan (k + 1) (depth + 1) false false
            | TOp (")" | "]" | "}") ->
                if depth = 0 then (not afterComma) && peekAt p k = TOp ")" && peekAt p (k + 1) = TOp ":="
                else scan (k + 1) (depth - 1) false false
            | TOp "," when depth = 0 -> scan (k + 1) 0 true true
            | t when depth = 0 && itemStart ->
                (match t, peekAt p (k + 1) with
                 | TName _, (TOp "," | TOp ")" | TOp ":=") -> scan (k + 1) 0 false false
                 | _ -> false)
            | _ -> scan (k + 1) depth false false
        scan 2 0 true false
    | _ -> false

// Оператор программы: присваивание / определение функции / декларация / выражение
let private parseStatement (p: Parser) : LispValue =
    let endOfStatement () = (match peek p with TSep | TEof -> true | _ -> false)
    match peek p, peekAt p 1 with
    | TName name, TOp ":=" ->
        ignore (advance p); ignore (advance p)
        // «a :=» без правой части — снять присваивание
        if endOfStatement () then LispList [LispSym ":="; LispSym name]
        else LispList [LispSym ":="; LispSym name; parseItem p]
    | TName name, TOp ":in" ->
        ignore (advance p); ignore (advance p)
        // «x :∈» без домена — снять декларации (как «x :=» снимает присваивание)
        if endOfStatement () then LispList [LispSym ":declare"; LispSym name]
        else LispList [LispSym ":declare"; LispSym name; parseExpr p]
    | _ when isFunDef p ->
        let name = (match advance p with TName n -> n | _ -> "")
        ignore (advance p)                                        // «(»
        let ps = parseItems p ")"
        expectOp p ":="
        LispList [LispSym ":="; LispList (LispSym name :: ps); parseExpr p]
    | _ ->
        let e = parseExpr p
        match peek p with
        // Шаг 21a: присваивание элементу v[i] := e, m[i, j] := e
        | TOp ":=" when (match e with LispList (LispSym "m-index" :: LispSym _ :: _ :: _) -> true | _ -> false) ->
            ignore (advance p)
            LispList [LispSym ":="; e; parseItem p]
        | TOp ":=" -> fail p "слева от «:=» ожидалось имя, f(параметры) или v[i]"
        | TOp ":in" -> fail p "слева от «:∈» ожидалось имя"
        | _ -> e

// Программа входного языка (Шаг 21): список операторов (AST — см. заголовок файла).
// Операторы разделяются «;» или переводом строки (внутри незакрытых скобок перевод строки — продолжение);
// комментарии // до конца строки. Ошибки — исключение с номером строки и позиции
// Шаг 21d: file — имя .mth-файла (или «<json>») для позиций: операторы и вызовы f(...) запоминают строку/столбец
// в побочной таблице, mathlang.lisp переносит их на сгенерированные формы Lisp (кадры стека ошибки показывают строку .mth)
let mathParseProgramFrom (file: string) (src: string) : LispValue list =
    let p = { Toks = tokenize "math" true src; Pos = 0; Who = "math"; File = file; Primes = System.Collections.Generic.HashSet<LispValue>(HashIdentity.Reference) }
    let stmts = ResizeArray<LispValue>()
    let mutable go = true
    while go do
        match peek p with
        | TEof -> go <- false
        | TSep -> ignore (advance p)
        | _ ->
            let t0 = cur p
            let st = markAt p t0 (parseStatement p)
            if not (isNull p.File) then
                let sp = posOf st
                if not (isNull sp) then spreadPos sp st
            stmts.Add st
            match peek p with
            | TSep | TEof -> ()
            | t -> fail p (sprintf "ожидался конец оператора («;» или перевод строки), получено «%s»" (describe t))
    List.ofSeq stmts

let mathParseProgram (src: string) : LispValue list = mathParseProgramFrom null src

// Главная функция: инфиксная строка → Lisp-дерево.
// Бросает исключение (failwith) при синтаксической ошибке — не молчит
let mathParse (src: string) : LispValue =
    let toks = tokenize "mathParse" false src
    match toks with
    | [| { T = TEof } |] -> failwith "mathParse: пустой ввод"
    | _ ->
        let p = { Toks = toks; Pos = 0; Who = "mathParse"; File = null; Primes = System.Collections.Generic.HashSet<LispValue>(HashIdentity.Reference) }
        let e = parseExpr p
        match peek p with
        | TEof -> e
        | t -> fail p (sprintf "лишние символы после выражения («%s»)" (describe t))
