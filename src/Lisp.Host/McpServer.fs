// Шаг 22.3: MCP-сервер (Model Context Protocol, транспорт stdio) — режим запуска «lisp --mcp».
// Тонкая обёртка над AgentApi.handleRequest: инструмент MCP → JSON-запрос --json (op, code, var, ...) → ToolResponse.
// Протокол (initialize, ping, tools/list, tools/call, версии протокола, отмена) — официальный C# SDK
// ModelContextProtocol.Core 1.4.1: сервер создаётся программно (McpServer.Create + StdioServerTransport),
// без Microsoft.Extensions.Hosting/DI; инструменты — таблица ToolSpec ниже (один инструмент — одна строка),
// схемы входа строятся по таблице, обработчики tools/list и tools/call — McpServerHandlers.
//
// Сессия одна на процесс (переменные, функции, декларации живут между вызовами; инструмент reset — новая сессия).
// Вызовы выполняются по одному в потоке интерпретатора (поток main с большим стеком, Program.fs): обработчик SDK
// кладёт работу в очередь и ждёт. stdout занят протоколом: SDK пишет в Console.OpenStandardOutput(), а Console.Out
// (print/display/трассы Lisp) перехвачен — вывод вызова попадает в поле output ответа, вывод вне вызовов — в stderr.
//
// Подшаг 22.4: каждый вызов — под сторожем runGuarded (timeout_s, отмена клиентом, предел памяти → флаг Cancel,
// ответ status timeout; не прервалось за GraceS — ответ и завершение процесса), размер ответа ограничен (limitResponse),
// песочница (Lisp.Core\Sandbox.fs) включена по умолчанию: --allow-dir <путь>, --unsafe.
module McpHost

open System
open System.Collections.Concurrent
open System.Collections.Generic
open System.IO
open System.Text
open System.Text.Json
open System.Text.Json.Nodes
open System.Threading
open System.Threading.Tasks
open ModelContextProtocol
open ModelContextProtocol.Protocol
open ModelContextProtocol.Server
open ToolResponse

// --- Таблица инструментов ---

type ParamKind =
    | PString
    | PInt
    | PBool
    | PEnum of string list

// Параметр инструмента: имя в MCP, поле запроса AgentApi (--json), тип, обязательность, значение по умолчанию
type ParamSpec =
    { Name: string
      Field: string
      Kind: ParamKind
      Required: bool
      Default: string option
      Description: string }

// Инструмент: имя MCP, операция AgentApi (op), описание для LLM (по-английски), параметры
type ToolSpec =
    { Name: string
      Op: string
      Description: string
      Params: ParamSpec list }

let private prm (name: string) (field: string) (kind: ParamKind) (required: bool) (descr: string) : ParamSpec =
    { Name = name; Field = field; Kind = kind; Required = required; Default = None; Description = descr }

// Общие параметры
let private expr =
    prm "expr" "code" PString true
        "Expression in the math language, e.g. \"x^2*sin(x) + exp(-x)\" (with syntax=\"lisp\": an S-expression, e.g. \"(* (^ x 2) (sin x))\")."
let private var (descr: string) = prm "var" "var" PString true descr
let private syntax =
    { prm "syntax" "syntax" (PEnum [ "math"; "lisp" ]) false
          "Input syntax of expression arguments: \"math\" (default; infix: x^2, sqrt(x), pi, ∞, a = b) or \"lisp\" (S-expressions)."
        with Default = Some "math" }
let private steps =
    prm "steps" "steps" (PEnum [ "none"; "brief"; "full"; "trace" ]) false
        ("Include the step-by-step solution in the 'steps' field (a tree; titles and comments are in Russian unless lang=\"en\"): none (default), "
         + "brief (main top-level steps only), full (the whole tree: depth ≤ 8, ≤ 200 steps; truncation is reported), "
         + "trace (full plus every simplifier rewrite, for debugging). Each step: rule (stable English id), title, comment, "
         + "before/after (+ _pretty), level (main|detail), children.")
// Шаг S.5: язык заголовков и пояснений шагов (rule остаётся английским идентификатором)
let private langParam =
    { prm "lang" "lang" (PEnum [ "ru"; "en" ]) false
          ("Language of step titles and comments (used with steps): \"ru\" (default) or \"en\". The rule ids and the formulas are language-independent. "
           + "A step without an English translation keeps its Russian text and is reported in 'warnings'.")
        with Default = Some "ru" }

// Подшаг 22.6: сертификат — проверка ответа независимым путём (по умолчанию выключен)
let private certificateParam =
    prm "certificate" "certificate" PBool false
        ("Include a verification of the answer in the 'certificate' field (default false): derivative check for integrate, substitution "
         + "check for solve, equivalence check for simplify/expand/factor/together/apart, ideal membership for groebner, counterexample "
         + "for equivalent=false. certificate.verified is true, false (also adds a warning), \"numeric\", \"partial\", \"skipped\" or \"timeout\". "
         + "The check counts against timeout_s.")

// Подшаг 22.4: параметры хоста (Field = null — в запрос AgentApi не передаются; их читает Server.Call)
let private timeoutParam =
    prm "timeout_s" null PInt false
        "Time limit in seconds (default 60, max 600). On expiry the computation is interrupted, status is \"timeout\"; the session stays usable."
let private maxCharsParam =
    prm "max_chars" null PInt false
        "Truncate result/pretty to this many characters (default 20000, max 200000); truncation is reported in 'warnings'."
let private hostParams = [ timeoutParam; maxCharsParam ]

let private exprTool (name: string) (descr: string) (ps: ParamSpec list) : ToolSpec =
    { Name = name; Op = name; Description = descr; Params = expr :: ps @ [ syntax; steps; langParam; certificateParam ] @ hostParams }

let private responseNote =
    " Returns a JSON object: status (answer | unknown | no-solution | nonelementary | error | timeout), result (S-expression), "
    + "pretty (math-language form), note, conditions (when the answer is valid, e.g. a ≠ 0), assumptions, certificate (only with certificate=true), "
    + "steps, warnings, output, error."

// Инструменты подшага 22.3. Новый инструмент — одна строка (операция должна быть в AgentApi.handleRequest)
let tools : ToolSpec list =
    [ { Name = "math"; Op = "math"
        Description =
            "Run a program in the CAS math language in the persistent session: statements separated by ';' or newlines, "
            + "assignments 'a := 2', functions 'f(x) := x^2', domain declarations 'x :∈ ℝ', and all CAS functions "
            + "(simplify, expand, factor, diff, integrate, solve, limit, series, ...). result/pretty contain one line per statement; "
            + "print() output goes to 'output'." + responseNote
        Params = [ prm "code" "code" PString true "Program text, e.g. \"f(x) := x^3 - x; factor(f(x)); solve(f(x) = 0, x)\"."; steps; langParam ] @ hostParams }
      { Name = "evaluate"; Op = "eval"
        Description =
            "Evaluate Lisp (Scheme-like) code in the persistent session; one or more forms, the value of each is returned "
            + "(one line per form). On error, 'stack' holds the Lisp backtrace." + responseNote
        Params = [ prm "code" "code" PString true "Lisp code, e.g. \"(integrate '(* x (exp x)) 'x)\"."; steps; langParam ] @ hostParams }
      exprTool "simplify" ("Simplify an expression to canonical form." + responseNote) []
      exprTool "diff" ("Differentiate an expression; the result is simplified." + responseNote)
          [ var "Differentiation variable, e.g. \"x\"."
            prm "order" "order" PInt false "Derivative order (default 1)." ]
      exprTool "integrate"
          ("Integrate an expression: indefinite, or definite when both 'from' and 'to' are given. If no antiderivative is found, "
           + "status is \"unknown\" and result is the unevaluated integral; conditions list parameter assumptions used." + responseNote)
          [ var "Integration variable, e.g. \"x\"."
            prm "from" "from" PString false "Lower limit for a definite integral (math language; -∞ allowed)."
            prm "to" "to" PString false "Upper limit for a definite integral (math language; ∞ allowed)." ]
      exprTool "sum"
          ("Symbolic summation (step 21l.7): Faulhaber for polynomials, Gosper/Abramov for hypergeometric and rational terms, "
           + "Zeilberger + rsolve for binomial sums (sum(C(n,k),k,0,n) = 2^n). The answer is a closed form, or a recurrence "
           + "with initial values when no hypergeometric closed form exists (Apéry numbers); the certificate verifies the answer "
           + "by direct summation. Lower bound 'from' defaults to 0; upper bound 'to' is required (usually n)." + responseNote)
          [ var "Summation variable, e.g. \"k\"."
            prm "from" "from" PString false "Lower bound (math language; default 0)."
            prm "to" "to" PString true "Upper bound (math language; usually n)." ]
      // Шаг LA.4: линейная алгебра — жорданова форма, exp(A·t), A^n, f(A), диагонализация, спектр
      { Name = "linear-algebra"; Op = "linear-algebra"
        Description =
            "Exact linear algebra on a matrix (step LA.4): Jordan normal form, matrix exponential exp(A·t), symbolic matrix "
            + "power A^n, a function of a matrix f(A), diagonalization, eigenvalues/eigenvectors. The matrix is given as "
            + "\"[[2,1],[0,2]]\" in the math language. fn selects the operation: jordan_form (returns [P, J] with A = P·J·P⁻¹), "
            + "jordan_blocks, mat_exp (var defaults to the built-in t; verified by d/dt E = A·E and E(0) = I), mat_power "
            + "(var defaults to n; nilpotent Jordan blocks at λ=0 are written as zeros with the condition n ≥ s in "
            + "'conditions'), mat_fn (func, e.g. \"exp\" or a lambda), diagonalize ([P, D]), is_diagonalizable, eigenvalues, "
            + "eigenvectors." + responseNote
        Params =
            [ prm "expr" "code" PString true "Matrix in the math language, e.g. \"[[2,1],[0,2]]\"."
              prm "fn" "fn" (PEnum [ "jordan_form"; "jordan_blocks"; "mat_exp"; "mat_power"; "mat_fn"; "diagonalize";
                                     "is_diagonalizable"; "eigenvalues"; "eigenvectors" ]) true
                  "Operation on the matrix."
              prm "var" "var" PString false "Variable for mat_exp (t) or mat_power (n); defaults to the built-in."
              prm "func" "func" PString false "Function for mat_fn, e.g. \"exp\" or \"lambda(x) x^2\"."
              steps; langParam ] @ hostParams }

      // Шаг LP.3: линейное и целочисленное программирование — точный симплекс + ветви и границы
      { Name = "linear-programming"; Op = "linear-programming"
        Description =
            "Linear and integer linear programming (step LP.3) with exact rational arithmetic: the two-phase simplex "
            + "method (Bland's rule) for LP, branch and bound for ILP. Maximize or minimize a linear objective cᵀx over "
            + "linear constraints. The answer always carries a certificate verified by lp-check (independent: only "
            + "multiplications and comparisons): optimal — x, value and the dual prices y with cᵀx = value = bᵀy; "
            + "infeasible — a Farkas lemma certificate; unbounded — a feasible point and a ray; integer — re-solving the "
            + "branch-and-bound tree. 'integer' is a vector of variable classes \"int\"/\"bin\"/\"free\"; when absent the "
            + "problem is a plain LP. answers: (optimal x value y), (infeasible y), (unbounded x d), "
            + "(unknown x value nil) when the node limit is exceeded." + responseNote
        Params =
            [ prm "objective" "code" PString true "Objective coefficients c as a vector, e.g. \"[3, 5]\"."
              prm "dir" "dir" (PEnum [ "max"; "min" ]) true "Optimization direction."
              prm "constraints" "A" PString true "Constraint matrix A as a matrix, e.g. \"[[1,0],[0,2],[1,1]]\"."
              prm "rhs" "b" PString true "Right-hand sides b as a vector, e.g. \"[4, 12, 8]\"."
              prm "relations" "relations" PString false "Constraint relations as a vector of \"<=\"/\">=\"/\"=\", e.g. \"[\"<=\", \">=\", \"=\"]\"; default all \"<=\"."
              prm "integer" "integer" PString false "Variable classes for ILP as a vector of \"int\"/\"bin\"/\"free\", e.g. \"[\"bin\", \"bin\", \"int\"]\"; when absent — plain LP."
              steps; langParam ] @ hostParams }

      { Name = "solve"; Op = "solve"
        Description =
            "Solve an equation or a system. Returns the SET of solutions (a system solution is a vector of equations x = ...); "
            + "status \"no-solution\" means proven unsolvable; 'conditions' lists the generic-parameter conditions (e.g. a ≠ 0) "
            + "under which the answer holds." + responseNote
        Params =
            [ prm "equations" "code" PString true
                  "Equation \"x^2 - 5x + 6 = 0\" (an expression means '= 0'), or a vector of equations \"[x + y = 3, x - y = 1]\"."
              prm "vars" "var" PString true "Unknown \"x\", or a vector of unknowns \"[x, y]\" for a system."
              syntax; steps; langParam; certificateParam ] @ hostParams }
      // Подшаг 22.5
      exprTool "expand" ("Expand products and integer powers of sums into a sum of monomials (collects like terms)." + responseNote) []
      exprTool "factor"
          ("Factor a polynomial over the integers into irreducible factors (also a rational function: numerator and denominator). "
           + "Irreducible or non-polynomial input is returned unchanged with status \"answer\"." + responseNote) []
      exprTool "together"
          ("Combine a sum of fractions into one fraction numerator/denominator in lowest terms: 1/x + 1/y gives (x + y)/(x*y)." + responseNote) []
      exprTool "apart"
          ("Partial fraction decomposition of a rational function with respect to 'var': 1/(x^2-1) gives 1/(2(x-1)) - 1/(2(x+1)). "
           + "Not a rational function in 'var' (e.g. contains sin(x)): status \"error\" or unchanged input." + responseNote)
          [ var "Variable of the decomposition, e.g. \"x\"." ]
      exprTool "limit"
          ("Limit of an expression as var approaches point (a number, or ∞ / -∞). Without 'side' it is the two-sided limit. "
           + "If the limit is not found (it may exist, or may not, e.g. sin(1/x) at 0), status is \"unknown\" and result is the "
           + "unevaluated limit(...); do not guess the value. Result may be ∞, -∞ or undefined." + responseNote)
          [ var "Limit variable, e.g. \"x\"."
            prm "point" "point" PString true "Limit point (math language): \"0\", \"1\", \"∞\", \"-∞\", \"a\"."
            prm "side" "side" (PEnum [ "plus"; "minus" ]) false "One-sided limit: \"plus\" (from the right, x→a+) or \"minus\" (from the left). Default: two-sided." ]
      exprTool "series"
          ("Taylor/Laurent series of an expression around a point, up to the given order (the O(...) remainder is included in the result). "
           + "Series that the CAS cannot compute (essential singularities, unsupported functions): status \"unknown\"." + responseNote)
          [ var "Expansion variable, e.g. \"x\"."
            { prm "point" "point" PString false "Expansion point (math language), default \"0\"." with Default = Some "0" }
            prm "order" "order" PInt false "The series is exact up to O(var^order); default 6." ]
      { Name = "groebner"; Op = "groebner"
        Description =
            "Reduced Groebner basis of the ideal generated by polynomials, as a vector of monic polynomials. 'order' is the monomial order: "
            + "lex (default; useful for elimination and solving), grlex, grevlex (usually fastest). Large systems (e.g. cyclic-6) can be slow: "
            + "use timeout_s; status \"timeout\" means no answer, not an empty basis." + responseNote
        Params =
            [ prm "polys" "code" PString true "Polynomials, as a vector \"[x^2 + y, x*y - 1]\" or an array of strings; an equation a = b means a - b."
              prm "vars" "var" PString true "Variables, as a vector \"[x, y]\" or an array of strings; the order of variables matters for lex."
              prm "order" "order" (PEnum [ "lex"; "grlex"; "grevlex" ]) false "Monomial order, default lex."
              syntax; steps; langParam; certificateParam ] @ hostParams }
      { Name = "declare"; Op = "declare"
        Description =
            "Declare a property of a symbol for the whole session: its domain or interval. It then affects simplify (sqrt(x^2) becomes x for "
            + "x in positive), solve, integrate and the signs of expressions. Declarations of one symbol accumulate (they intersect): call again to "
            + "add a constraint. Returns \"x ∈ D\"; 'assumptions' lists all active declarations. Undeclared symbols are complex numbers."
            + responseNote
        Params =
            [ prm "symbol" "code" PString true "Symbol name, e.g. \"x\"."
              prm "domain" "domain" PString true
                  ("One of: ℝ (reals), ℤ (integers), ℚ (rationals), ℕ (naturals incl. 0), ℂ (complex); positive, nonnegative, negative, nonpositive; "
                   + "an interval: (0, ∞), [0, 1], (0, 1], interval(-1, 1). ASCII names also work: reals, integers, rationals, naturals, complexes.")
              steps; langParam ] @ hostParams }
      { Name = "undeclare"; Op = "undeclare"
        Description = "Remove all declarations of a symbol (it becomes an arbitrary complex number again)." + responseNote
        Params = [ prm "symbol" "code" PString true "Symbol name, e.g. \"x\"."; steps; langParam ] @ hostParams }
      { Name = "declarations"; Op = "declarations"
        Description = "List the active declarations of the session, one \"x ∈ D\" per line (also given in 'assumptions' of every response)." + responseNote
        Params = hostParams }
      { Name = "equivalent"; Op = "equivalent"
        Description =
            "Check whether two expressions are equal. result is \"true\", \"false\" or \"unknown\" (status \"answer\"). "
            + "true: proved symbolically (the difference simplifies to 0); holds where both expressions are defined. "
            + "false: a counterexample is given in 'note' (a point where the values differ; sample points respect declarations, "
            + "undeclared symbols are sampled as real numbers). unknown: not proved, and the numeric checks at random points agreed "
            + "(this is NOT a proof); verify by other means or say that you could not decide." + responseNote
        Params =
            [ prm "a" "code" PString true "First expression, e.g. \"sin(x)^2 + cos(x)^2\"."
              prm "b" "other" PString true "Second expression, e.g. \"1\"."
              prm "vars" "var" PString false "Variables to sample, e.g. \"[x, y]\" (optional: all free symbols are used)."
              syntax; steps; langParam; certificateParam ] @ hostParams }
      { Name = "guide"; Op = "guide"
        Description =
            "Return the on-demand LLM guide (markdown). Without 'topic': the short core (input syntax, how to read the response: status / "
            + "conditions / certificates, which tool when) and the list of topic cards (the same text is the MCP resource lisp://guide). "
            + "With 'topic' (e.g. \"integration\", \"ode\", \"linear-algebra\", \"sums\"): a card with 5-15 functions with exact signatures, "
            + "runnable examples and pitfalls. A name from other systems (Mathematica, Maple) (\"DSolve\", \"FactorInteger\", \"Eigenvalues\", ...) or a tool "
            + "name is accepted and returns the right card; topic \"synonyms\" is the whole table. An unknown topic returns an error with "
            + "suggestions. Read the core once before the first calculation."
        Params =
            [ prm "topic" "topic" PString false "Topic card name (e.g. \"integration\") or a name from another system (e.g. \"DSolve\"); omit for the core guide and the list of topics." ] }
      { Name = "code"; Op = "code"
        Description =
            "Query the Lisp source of the CAS library (lib/) instead of reading whole files; for developers and agents extending the library. "
            + "kind: def (location, signature, doc comment and source of NAME), sig (one-line signature + module + first doc line; builtins too), "
            + "refs (where NAME is used), callers / callees (direct, depth for transitive), module (exports and module dependencies), "
            + "outline (definitions of a file with line numbers), search (top-10 definitions by name/doc words, Russian or English), "
            + "deps (external names a file uses, by module), unused (definitions never referenced). Names may be qualified: module::name. "
            + "Result: plain text (default, compact) or JSON text with json=true. An unknown name returns an error with similar names."
        Params =
            [ prm "kind" null (PEnum CodeIndex.kinds) true "Kind of query."
              prm "arg" null PString false "NAME for def/sig/refs/callers/callees, module name for module, file path (lib/algnum.lisp or algnum.lisp) for outline/deps, words for search; not used by unused."
              prm "depth" null PInt false "callers/callees: depth of the transitive closure (default 1)."
              prm "json" null PBool false "Return JSON text instead of compact text (default false)."
              prm "no_body" null PBool false "def: omit the source text (default false)."
              maxCharsParam ] }
      { Name = "reset"; Op = "reset"
        Description = "Reset the session: forget all variables, functions and domain declarations. Returns status \"answer\"."
        Params = [] } ]

// Шаг GD.2: ресурс lisp://guide — то же, что инструмент guide без темы (ядро docs\guide\core.md + список тем)
let guideText : string =
    match Guide.text None with
    | Result.Ok t -> t
    | Result.Error e -> e

// JSON-схема входа инструмента (inputSchema)
let inputSchema (t: ToolSpec) : JsonElement =
    let props = JsonObject()
    for p in t.Params do
        let o = JsonObject()
        match p.Kind with
        | PString -> o["type"] <- JsonValue.Create "string"
        | PInt -> o["type"] <- JsonValue.Create "integer"
        | PBool -> o["type"] <- JsonValue.Create "boolean"
        | PEnum vs ->
            o["type"] <- JsonValue.Create "string"
            o["enum"] <- JsonArray([| for v in vs -> JsonValue.Create v :> JsonNode |])
        match p.Default with
        | Some d -> o["default"] <- JsonValue.Create d
        | None -> ()
        o["description"] <- JsonValue.Create p.Description
        props[p.Name] <- o
    let schema = JsonObject()
    schema["type"] <- JsonValue.Create "object"
    schema["properties"] <- props
    schema["required"] <- JsonArray([| for p in t.Params do if p.Required then yield JsonValue.Create p.Name :> JsonNode |])
    schema["additionalProperties"] <- JsonValue.Create false
    JsonSerializer.SerializeToElement(schema)

// --- Вызов инструмента: аргументы MCP → запрос AgentApi ---

exception private BadArguments of string

// Запрос --json для AgentApi.handleRequest. Строковый параметр принимает и массив строк (LLM часто передаёт
// уравнения/неизвестные массивом): он склеивается в вектор языка «[a, b]» (syntax math) или список «(a b)» (lisp)
let buildRequest (t: ToolSpec) (args: IDictionary<string, JsonElement>) : string =
    let args = if isNull args then (Dictionary<string, JsonElement>() :> IDictionary<_, _>) else args
    for KeyValue (k, _) in args do
        if not (t.Params |> List.exists (fun p -> p.Name = k)) then
            let known = t.Params |> List.map (fun p -> p.Name) |> String.concat ", "
            raise (BadArguments $"Unknown argument '{k}' for tool '{t.Name}' (expected: {known})")
    let lisp =
        match args.TryGetValue "syntax" with
        | true, v when v.ValueKind = JsonValueKind.String -> v.GetString() = "lisp"
        | _ -> false
    use ms = new MemoryStream()
    do
        use w = new Utf8JsonWriter(ms)
        w.WriteStartObject()
        w.WriteString("op", t.Op)
        for p in t.Params |> List.filter (fun p -> not (isNull p.Field)) do
            match args.TryGetValue p.Name with
            | true, v when v.ValueKind = JsonValueKind.Null || v.ValueKind = JsonValueKind.Undefined ->
                p.Default |> Option.iter (fun d -> w.WriteString(p.Field, d))
            | true, v ->
                match p.Kind, v.ValueKind with
                | PInt, JsonValueKind.Number -> w.WriteNumber(p.Field, v.GetInt32())
                | PInt, JsonValueKind.String ->
                    match Int32.TryParse(v.GetString()) with
                    | true, n -> w.WriteNumber(p.Field, n)
                    | _ -> raise (BadArguments $"Argument '{p.Name}' must be an integer")
                | PInt, _ -> raise (BadArguments $"Argument '{p.Name}' must be an integer")
                | PBool, (JsonValueKind.True | JsonValueKind.False) -> w.WriteBoolean(p.Field, v.GetBoolean())
                | PBool, JsonValueKind.String when v.GetString() = "true" || v.GetString() = "false" ->
                    w.WriteBoolean(p.Field, v.GetString() = "true")
                | PBool, _ -> raise (BadArguments $"Argument '{p.Name}' must be true or false")
                | (PString | PEnum _), JsonValueKind.String -> w.WriteString(p.Field, v.GetString())
                | PString, JsonValueKind.Array ->
                    let items =
                        [ for e in v.EnumerateArray() ->
                            if e.ValueKind = JsonValueKind.String then e.GetString()
                            else raise (BadArguments $"Argument '{p.Name}' must be a string or an array of strings") ]
                    w.WriteString(p.Field, (if lisp then "(" + String.concat " " items + ")" else "[" + String.concat ", " items + "]"))
                | PString, (JsonValueKind.Number | JsonValueKind.True | JsonValueKind.False) -> w.WriteString(p.Field, v.GetRawText())
                | _ -> raise (BadArguments $"Argument '{p.Name}' must be a string")
            | _ -> p.Default |> Option.iter (fun d -> w.WriteString(p.Field, d))
        w.WriteEndObject()
    Encoding.UTF8.GetString(ms.ToArray())

// --- Подшаг 22.4: лимиты, сторож вызова ---

// Лимиты сервера (docs\mcp.md «Таймаут, лимиты, песочница»)
type Limits =
    { DefaultTimeoutS: int     // timeout_s по умолчанию
      MaxTimeoutS: int         // потолок timeout_s
      GraceS: float            // после поднятия флага отмены: столько ждать, затем — ответ timeout и перезапуск процесса
      MaxChars: int            // result/pretty/error по умолчанию (max_chars)
      MaxCharsCap: int         // потолок max_chars
      MaxOutput: int           // output (print/display)
      MaxSteps: int            // число шагов в steps
      MaxStepChars: int        // длина before/after одного шага
      MaxMemoryMB: int }       // управляемая куча (GC.GetTotalMemory) во время вызова; 0 — без проверки

let defaultLimits : Limits =
    { DefaultTimeoutS = 60; MaxTimeoutS = 600; GraceS = 5.0; MaxChars = 20000; MaxCharsCap = 200000; MaxOutput = 10000
      MaxSteps = 200; MaxStepChars = 2000; MaxMemoryMB = 4096 }

// Выполнить work в текущем потоке под сторожем (таймер раз в 50 мс, поток пула): по таймауту, отмене клиентом (ct) или
// превышению памяти поднимает флаг Cancel (один раз, с причиной) — интерпретатор прерывается на ближайшей проверке.
// Если work не завершилась за limits.GraceS после этого (застряла в F#-примитиве без проверок), вызывается
// onStuck причина (из потока таймера, один раз); work при этом продолжается. По выходе флаг опускается
let runGuarded (limits: Limits) (timeoutS: float) (ct: CancellationToken) (onStuck: string -> unit) (work: unit -> 'a) : 'a =
    Cancel.clear ()
    let sw = Diagnostics.Stopwatch.StartNew()
    let gate = obj ()
    let finished = ref false
    let firedAt = ref -1L
    let stuck = ref false
    let tick (_: obj) =
        lock gate (fun () ->
            if not finished.Value then
                let now = sw.ElapsedMilliseconds
                if firedAt.Value < 0L then
                    let why =
                        if ct.IsCancellationRequested then Some "запрос отменён клиентом"
                        elif float now >= timeoutS * 1000.0 then Some (sprintf "таймаут %g с" timeoutS)
                        elif limits.MaxMemoryMB > 0 && GC.GetTotalMemory(false) > int64 limits.MaxMemoryMB * 1048576L then
                            Some (sprintf "превышен предел памяти %d МБ" limits.MaxMemoryMB)
                        else None
                    match why with
                    | Some w ->
                        firedAt.Value <- now
                        Cancel.request w
                    | None -> ()
                elif not stuck.Value && float (now - firedAt.Value) >= limits.GraceS * 1000.0 then
                    stuck.Value <- true
                    onStuck Cancel.reason)
    use timer = new Timer(TimerCallback tick, null, 50, 50)
    try work ()
    finally
        lock gate (fun () -> finished.Value <- true)
        Cancel.clear ()

// Console.Out вызова: хранит не более cap символов, остальное только считает (бесконечный display не раздувает память)
type BoundedWriter(cap: int) =
    inherit StringWriter()
    let mutable dropped = 0L
    member _.Dropped = dropped
    member this.Reset() =
        this.GetStringBuilder().Clear() |> ignore
        dropped <- 0L
    override this.Write(c: char) =
        if this.GetStringBuilder().Length < cap then base.Write(c) else dropped <- dropped + 1L
    override this.Write(s: string) =
        if not (isNull s) then
            let room = cap - this.GetStringBuilder().Length
            if s.Length <= room then base.Write(s)
            else
                if room > 0 then base.Write(s.Substring(0, room))
                dropped <- dropped + int64 (s.Length - max room 0)
    override this.Write(buffer: char[], index: int, count: int) = this.Write(String(buffer, index, count))
    override this.Write(buffer: ReadOnlySpan<char>) = this.Write(String(buffer))
    override this.WriteLine(s: string) = this.Write(s + this.NewLine)
    override this.WriteLine(buffer: ReadOnlySpan<char>) = this.Write(String(buffer) + this.NewLine)

// Обрезать строку до limit символов (не разрывая суррогатную пару)
let private cutString (s: string) (limit: int) : string =
    let n = if limit > 0 && Char.IsHighSurrogate s.[limit - 1] then limit - 1 else limit
    s.Substring(0, n) + " …"

// Ограничить размер ответа: result/pretty/error — maxChars, output — MaxOutput (outputTotal — полная длина с отброшенным),
// steps — MaxSteps шагов и MaxStepChars на запись; обрезка — с пометкой в warnings
let limitResponse (limits: Limits) (maxChars: int) (outputTotal: int64) (r: ToolResponse) : ToolResponse =
    let warns = ResizeArray<string>()
    let cut (field: string) (limit: int) (total: int64) (v: string option) =
        match v with
        | Some s when int64 s.Length > int64 limit || total > int64 s.Length ->
            let shown = min s.Length limit
            warns.Add(sprintf "%s обрезан: показаны первые %d из %d символов" field shown (max total (int64 s.Length)))
            Some (if s.Length > limit then cutString s limit else s + " …")
        | other -> other
    // шаги — дерево (шаг S.1): уровень и лимит 200 узлов / глубина 8 уже применены в AgentApi (StepLog.select);
    // здесь — страховка по числу узлов (MaxSteps, обход в глубину) и длина выражений
    let steps =
        match r.Steps with
        | Some st ->
            let longStep = ref false
            let c (s: string) = if s.Length > limits.MaxStepChars then (longStep.Value <- true; cutString s limits.MaxStepChars) else s
            let budget = ref limits.MaxSteps
            let total = ref 0
            let rec count (es: StepEntry list) = es |> List.sumBy (fun e -> 1 + count e.Children)
            let rec prune (es: StepEntry list) : StepEntry list =
                [ for e in es do
                    total.Value <- total.Value + 1
                    if budget.Value > 0 then
                        budget.Value <- budget.Value - 1
                        yield { e with Before = c e.Before; BeforePretty = c e.BeforePretty; BeforeLatex = c e.BeforeLatex
                                       After = c e.After
                                       AfterPretty = c e.AfterPretty; AfterLatex = c e.AfterLatex; Children = prune e.Children }
                    else total.Value <- total.Value + count e.Children ]
            let kept = prune st
            if total.Value > limits.MaxSteps then
                warns.Add(sprintf "steps обрезаны: показаны первые %d из %d шагов" limits.MaxSteps total.Value)
            if longStep.Value then warns.Add(sprintf "длинные выражения в steps обрезаны до %d символов" limits.MaxStepChars)
            Some kept
        | None -> None
    let r2 =
        { r with
            Result = cut "result" maxChars 0L r.Result
            Pretty = cut "pretty" maxChars 0L r.Pretty
            Latex = cut "latex" maxChars 0L r.Latex
            Error = cut "error" maxChars 0L r.Error
            Output = cut "output" limits.MaxOutput outputTotal r.Output
            Steps = steps }
    if warns.Count = 0 then r2 else { r2 with Warnings = r.Warnings @ List.ofSeq warns }

// Целый параметр хоста (timeout_s, max_chars): нет — None; не целое — BadArguments
let private intArg (args: IDictionary<string, JsonElement>) (name: string) : int option =
    if isNull args then None
    else
        match args.TryGetValue name with
        | true, v when v.ValueKind = JsonValueKind.Number ->
            match v.TryGetInt32() with
            | true, n -> Some n
            | _ ->
                match v.TryGetDouble() with
                | true, d when d >= 1.0 -> Some (int (min d 1e9))
                | _ -> raise (BadArguments $"Argument '{name}' must be a positive integer")
        | true, v when v.ValueKind = JsonValueKind.String ->
            match Int32.TryParse(v.GetString()) with
            | true, n -> Some n
            | _ -> raise (BadArguments $"Argument '{name}' must be a positive integer")
        | true, v when v.ValueKind = JsonValueKind.Null -> None
        | true, _ -> raise (BadArguments $"Argument '{name}' must be a positive integer")
        | _ -> None

// Состояние сервера: сессия и перехваченный Console.Out. Используется только из потока интерпретатора
type Server(limits: Limits) =
    let mutable session : Types.Env = AgentApi.makeSession ()
    // print/display за вызов: с запасом над MaxOutput (обрезка с пометкой — limitResponse)
    let captured = new BoundedWriter(limits.MaxOutput + 1)
    new() = Server(defaultLimits)
    member _.Session = session
    member _.Captured = captured
    member _.Limits = limits

    // Перехватить Console.Out (вызывается один раз при старте режима --mcp)
    member _.CaptureConsole() = Console.SetOut(captured)

    // Текст, напечатанный в Console.Out с прошлого вызова (и очистка); вторая компонента — сколько символов отброшено
    member _.TakeOutputCounted() : string * int64 =
        let s = captured.GetStringBuilder().ToString()
        let d = captured.Dropped
        captured.Reset()
        s, d

    member this.TakeOutput() : string = fst (this.TakeOutputCounted())

    // Сброс сессии: новая Env (декларации доменов, переменные и функции языка — состояние окружения) + math-reset
    member _.Reset() =
        session <- AgentApi.makeSession ()
        Evaluator.eval (Types.LispList [ Types.LispSym "math-reset" ]) session |> ignore

    // Вызов инструмента по имени → ToolResponse (ошибки аргументов — status error)
    member this.Call(name: string, args: IDictionary<string, JsonElement>) : ToolResponse =
        this.Call(name, args, CancellationToken.None, (fun why -> eprintfn "lisp --mcp: вычисление не прерывается (%s)" why))

    // Подшаг 22.4: вызов под сторожем — timeout_s (по умолчанию limits.DefaultTimeoutS), отмена клиентом ct;
    // onStuck — вычисление не прервалось за GraceS после таймаута (см. runGuarded); ответ ограничен по размеру
    member this.Call(name: string, args: IDictionary<string, JsonElement>, ct: CancellationToken, onStuck: string -> unit) : ToolResponse =
        match tools |> List.tryFind (fun t -> t.Name = name) with
        | None -> raise (McpProtocolException($"Unknown tool: {name}", McpErrorCode.InvalidParams))
        | Some t ->
            this.TakeOutput() |> ignore
            let sw = Diagnostics.Stopwatch.StartNew()
            let mutable maxChars = limits.MaxChars
            let r =
                try
                    let request = buildRequest t args
                    let timeoutS =
                        match intArg args "timeout_s" with
                        | Some n when n >= 1 -> min n limits.MaxTimeoutS
                        | Some _ -> raise (BadArguments "Argument 'timeout_s' must be a positive integer")
                        | None -> limits.DefaultTimeoutS
                    maxChars <-
                        match intArg args "max_chars" with
                        | Some n when n >= 1 -> min n limits.MaxCharsCap
                        | Some _ -> raise (BadArguments "Argument 'max_chars' must be a positive integer")
                        | None -> limits.MaxChars
                    if t.Op = "reset" then
                        this.Reset()
                        { empty Answer with Result = Some "#t"; Pretty = Some "true"; Note = Some "сессия сброшена"
                                            TimingMs = sw.ElapsedMilliseconds }
                    elif t.Op = "code" then
                        let strOf (n: string) =
                            match (if isNull args then (false, Unchecked.defaultof<JsonElement>) else args.TryGetValue n) with
                            | true, v when v.ValueKind = JsonValueKind.String -> v.GetString()
                            | true, v when v.ValueKind = JsonValueKind.Number -> v.GetRawText()
                            | true, v when v.ValueKind = JsonValueKind.Null || v.ValueKind = JsonValueKind.Undefined -> ""
                            | true, _ -> raise (BadArguments $"Argument '{n}' must be a string")
                            | _ -> ""
                        let boolOf (n: string) =
                            match (if isNull args then (false, Unchecked.defaultof<JsonElement>) else args.TryGetValue n) with
                            | true, v when v.ValueKind = JsonValueKind.True -> true
                            | true, v when v.ValueKind = JsonValueKind.String && v.GetString() = "true" -> true
                            | _ -> false
                        let kind = strOf "kind"
                        if kind = "" then raise (BadArguments "Argument 'kind' is required")
                        let depth = defaultArg (intArg args "depth") 1
                        let text, ok = QueryCli.runCode session kind (strOf "arg") (boolOf "json") (boolOf "no_body") depth None []
                        if ok then { empty Answer with Result = Some text; TimingMs = sw.ElapsedMilliseconds }
                        else { empty Error with Error = Some text; Stack = Some []; TimingMs = sw.ElapsedMilliseconds }
                    elif t.Op = "guide" then
                        let topic =
                            match (if isNull args then (false, Unchecked.defaultof<JsonElement>) else args.TryGetValue "topic") with
                            | true, v when v.ValueKind = JsonValueKind.String -> Some (v.GetString())
                            | true, v when v.ValueKind = JsonValueKind.Null || v.ValueKind = JsonValueKind.Undefined -> None
                            | true, _ -> raise (BadArguments "Argument 'topic' must be a string")
                            | _ -> None
                        match Guide.text topic with
                        | Result.Ok text ->
                            { empty Answer with Result = Some text; Note = Some "LLM guide (markdown); the core is also the MCP resource lisp://guide"
                                                TimingMs = sw.ElapsedMilliseconds }
                        | Result.Error msg -> { empty Error with Error = Some msg; Stack = Some []; TimingMs = sw.ElapsedMilliseconds }
                    else
                        runGuarded limits (float timeoutS) ct onStuck (fun () -> AgentApi.handleRequest session request)
                with BadArguments msg -> { empty Error with Error = Some msg; Stack = Some []; TimingMs = sw.ElapsedMilliseconds }
            // print/display Lisp (Console.Out) — в output, после вывода print языка (m-capture)
            let console, dropped = this.TakeOutputCounted()
            let r = if console = "" then r else { r with Output = Some ((defaultArg r.Output "") + console) }
            let outLen = (defaultArg r.Output "").Length
            let r = limitResponse limits maxChars (int64 outLen + dropped) r
            // после прерывания по памяти — вернуть память системе до следующего вызова
            if r.Status = Status.Timeout then GC.Collect()
            r

// --- Поток интерпретатора: очередь работ ---

type private Job = { Run: unit -> unit }

// Результат tools/call: ToolResponse как JSON — текстом (content[0].text) и структурой (structuredContent).
// isError не используется: ошибка вычисления — обычный ответ со status error (LLM читает структуру)
let toCallResult (r: ToolResponse) : CallToolResult =
    let json = toJson r
    let res = CallToolResult()
    res.Content <- List<ContentBlock>([ TextContentBlock(Text = json) :> ContentBlock ])
    res.StructuredContent <- JsonSerializer.SerializeToElement(JsonDocument.Parse(json).RootElement) |> Nullable
    res

let private instructions =
    "Computer algebra system (exact symbolic math). Expression arguments use the CAS math language by default: "
    + "infix x^2, implicit multiplication 2x, sqrt, exp, log, sin, pi (π), ∞, equations a = b, vectors [a, b], sets {a, b}. "
    + "The session is persistent: definitions made with the 'math' tool (a := 2, f(x) := ...) are visible to later calls; "
    + "use 'reset' to start over. Always check 'status' (answer / unknown / no-solution / error) and 'conditions' in the result; "
    + "'unknown' means the CAS could not decide (e.g. an unevaluated integral), not that the answer does not exist. "
    + "Each call has a time limit (timeout_s, default 60 s): status \"timeout\" means the computation was interrupted, "
    + "the session is still usable. Long result/output strings are truncated (see 'warnings', max_chars). "
    + "Call 'guide' once for the short core (also the resource lisp://guide); 'guide' with topic=NAME returns a topic card "
    + "(a name from other systems (Mathematica, Maple) such as DSolve or FactorInteger is accepted)."

let private sandboxNote =
    " Sandbox: files can be loaded (load, load-math) only from the CAS library and directories given with --allow-dir; "
    + "writing files and starting processes are not available."

// Параметры командной строки режима --mcp
type McpOptions =
    { Unsafe: bool                 // --unsafe: без песочницы
      AllowDirs: string list       // --allow-dir <путь> (можно несколько)
      MaxMemoryMB: int option }    // --max-memory-mb <N> (0 — без проверки)

// Разбор аргументов после --mcp: Ok параметры | Error сообщение
let parseOptions (argv: string list) : Result<McpOptions, string> =
    let rec go (o: McpOptions) (xs: string list) =
        match xs with
        | [] -> Result.Ok o
        | "--unsafe" :: rest -> go { o with Unsafe = true } rest
        | "--allow-dir" :: d :: rest ->
            if Directory.Exists d then go { o with AllowDirs = o.AllowDirs @ [ Path.GetFullPath d ] } rest
            else Result.Error $"--allow-dir: каталог не найден: {d}"
        | "--max-memory-mb" :: n :: rest ->
            match Int32.TryParse n with
            | true, v when v >= 0 -> go { o with MaxMemoryMB = Some v } rest
            | _ -> Result.Error $"--max-memory-mb: ожидается неотрицательное целое, получено {n}"
        | x :: _ -> Result.Error $"неизвестный параметр --mcp: {x} (допустимы --allow-dir <путь>, --unsafe, --max-memory-mb <N>)"
    go { Unsafe = false; AllowDirs = []; MaxMemoryMB = None } argv

// Режим --mcp: вызывать из потока с большим стеком (Program.main). argv — аргументы после --mcp. Возвращает код выхода
let run (argv: string list) : int =
  match parseOptions argv with
  | Result.Error msg ->
    eprintfn "lisp --mcp: %s" msg
    2
  | Result.Ok opts ->
    // Подшаг 22.4: песочница по умолчанию (--unsafe снимает) — Sandbox.fs
    Sandbox.configure (not opts.Unsafe) opts.AllowDirs
    if opts.Unsafe then eprintfn "lisp --mcp: песочница выключена (--unsafe)"
    else eprintfn "lisp --mcp: %s" (Sandbox.describe ())
    let limits = { defaultLimits with MaxMemoryMB = defaultArg opts.MaxMemoryMB defaultLimits.MaxMemoryMB }
    let realOut = Console.Out
    let server = Server(limits)
    server.CaptureConsole()
    // Вывод при загрузке библиотек — в stderr
    match server.TakeOutput() with
    | "" -> ()
    | s -> eprintf "%s" s
    let queue = new BlockingCollection<Job>()
    let options = McpServerOptions()
    options.ServerInfo <- Implementation(Name = "qedra", Version = (match System.Reflection.Assembly.GetEntryAssembly() with null -> "0" | a -> a.GetName().Version.ToString()))
    options.ServerInstructions <- instructions + (if opts.Unsafe then "" else sandboxNote)
    options.Capabilities <- ServerCapabilities(Tools = ToolsCapability(), Resources = ResourcesCapability())
    // Подшаг 22.5: ресурс lisp://guide — тот же текст, что у инструмента guide
    let guideUri = "lisp://guide"
    options.Handlers.ListResourcesHandler <-
        McpRequestHandler<ListResourcesRequestParams, ListResourcesResult>(fun _ _ ->
            let res = Resource(Uri = guideUri, Name = "guide", Title = "LLM guide", MimeType = "text/markdown",
                               Description = "Core guide: input languages, response format (status, conditions, certificates), which tool when, list of topic cards")
            ValueTask<ListResourcesResult>(ListResourcesResult(Resources = List<Resource>([ res ]))))
    options.Handlers.ReadResourceHandler <-
        McpRequestHandler<ReadResourceRequestParams, ReadResourceResult>(fun ctx _ ->
            if ctx.Params.Uri <> guideUri then
                raise (McpProtocolException($"Unknown resource: {ctx.Params.Uri}", McpErrorCode.InvalidParams))
            let c = TextResourceContents(Uri = guideUri, MimeType = "text/markdown", Text = guideText)
            ValueTask<ReadResourceResult>(ReadResourceResult(Contents = List<ResourceContents>([ c :> ResourceContents ]))))
    let toolList = tools |> List.map (fun t -> Tool(Name = t.Name, Description = t.Description, InputSchema = inputSchema t))
    options.Handlers.ListToolsHandler <-
        McpRequestHandler<ListToolsRequestParams, ListToolsResult>(fun _ _ ->
            ValueTask<ListToolsResult>(ListToolsResult(Tools = List<Tool>(toolList))))
    // Подшаг 22.4: вычисление не прервалось за GraceS после таймаута (застряло в F#-примитиве без проверок флага):
    // ответить timeout сразу (из потока сторожа) и завершить процесс — клиент перезапустит сервер, сессия теряется
    let onStuck (tcs: TaskCompletionSource<CallToolResult>) (why: string) =
        let r =
            { empty Status.Timeout with
                Note = Some ($"вычисление прервано: {why}; оно не остановилось за {limits.GraceS} с (долгий примитив на F#) — "
                             + "процесс сервера завершается, клиент должен перезапустить его; состояние сессии потеряно")
                Error = Some ("Прервано: " + why); Stack = Some []; TimedOut = true
                Warnings = [ "процесс сервера завершается: состояние сессии (переменные, функции, декларации) потеряно" ] }
        tcs.TrySetResult(toCallResult r) |> ignore
        eprintfn "lisp --mcp: вычисление не прерывается (%s) — завершение процесса" why
        Task.Run(fun () ->
            Thread.Sleep 1000          // дать SDK отправить ответ
            Environment.Exit 3) |> ignore
    options.Handlers.CallToolHandler <-
        McpRequestHandler<CallToolRequestParams, CallToolResult>(fun ctx ct ->
            let tcs = TaskCompletionSource<CallToolResult>(TaskCreationOptions.RunContinuationsAsynchronously)
            let name = ctx.Params.Name
            let args = ctx.Params.Arguments
            queue.Add
                { Run = fun () ->
                    if ct.IsCancellationRequested then tcs.TrySetCanceled(ct) |> ignore
                    else
                        // отмена клиентом (notifications/cancelled → ct) во время вычисления — тот же флаг, что таймаут
                        try tcs.TrySetResult(toCallResult (server.Call(name, args, ct, onStuck tcs))) |> ignore
                        with ex -> tcs.TrySetException(ex) |> ignore }
            ValueTask<CallToolResult>(tcs.Task))
    let transport = new StdioServerTransport("qedra")
    let mcp = McpServer.Create(transport, options)
    // Прогрев JIT (первый интеграл — секунды) — первой работой в очереди, сервер уже отвечает на initialize
    let warmArgs = Dictionary<string, JsonElement>()
    warmArgs["expr"] <- JsonSerializer.SerializeToElement "x*sin(x)"
    warmArgs["var"] <- JsonSerializer.SerializeToElement "x"
    queue.Add { Run = fun () -> try server.Call("integrate", warmArgs) |> ignore with _ -> () }
    let serverTask =
        Task.Run<unit>(fun () ->
            task {
                try
                    try do! mcp.RunAsync(CancellationToken.None)
                    with ex -> eprintfn "lisp --mcp: %s" ex.Message
                finally
                    queue.CompleteAdding()
                do! mcp.DisposeAsync()
                do! transport.DisposeAsync()
            })
    for job in queue.GetConsumingEnumerable() do
        job.Run ()
    serverTask.Wait()
    Console.SetOut(realOut)
    0
