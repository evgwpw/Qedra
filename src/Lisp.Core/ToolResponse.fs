// Шаг 22.1: единый формат ответа инструмента (ToolResponse) — для режима --json и (с подшага 22.3) MCP-сервера.
// Описание для пользователя — docs\math-language.md «Из других программ».
// Здесь только тип и сериализация (без интерпретатора); заполнение и правило статуса — AgentApi.classify.
//
// Порядок полей JSON стабилен (клиенты и тесты могут на него опираться):
//   status, result, pretty, note, conditions, assumptions, certificate, steps, warnings, output, timing,
//   затем прежние поля --json для совместимости: ok, error, stack.
// conditions — массив объектов {condition (запись языка), sexpr, reason}.
// certificate — null или объект {kind, verified, method, detail} (подшаг 22.6, только по запросу certificate: true).
// steps — дерево шагов {rule, title, comment, before, before_pretty, after, after_pretty, level, children[, omitted]}
// (шаг S.1; отбор по уровню brief | full | trace и лимиты — в AgentApi).
// Пустое значение — null (пустой список тоже null), кроме: steps — [] если шаги запрошены, но не записаны
// (null — не запрашивались); прежних полей: output у op "math" — строка (возможно ""), stack при ошибке — массив.
module ToolResponse

open System.IO
open System.Text.Encodings.Web
open System.Text.Json

// Исход запроса (соответствие Outcome: Answer → answer, Unknown → unknown, NoSolution → no-solution / nonelementary)
type Status =
    | Answer          // ответ найден
    | Unknown         // «не знаю»: невычисленная форма или ошибка «не умею»; другой путь может справиться
    | NoSolution      // доказано, что решений нет (пустое множество solve)
    | Nonelementary   // доказано, что интеграл неэлементарен (появится с алгоритмом Риша, 21j/21k)
    | Error           // ошибка (в том числе ошибка протокола)
    | Timeout         // превышено время (подшаг 22.4)

let statusName (s: Status) : string =
    match s with
    | Answer -> "answer"
    | Unknown -> "unknown"
    | NoSolution -> "no-solution"
    | Nonelementary -> "nonelementary"
    | Error -> "error"
    | Timeout -> "timeout"

// Шаг решения (журнал StepLog, шаг S.1 — дерево): rule (стабильный английский идентификатор приёма), title и comment
// (по-русски), до и после — S-выражение и запись языка, level (main | detail), children — вложенные шаги,
// omitted — сколько вложенных шагов скрыто обрезкой (в JSON — только если > 0)
type StepEntry =
    { Rule: string
      Title: string
      Comment: string
      Before: string
      BeforePretty: string
      BeforeLatex: string
      After: string
      AfterPretty: string
      AfterLatex: string
      Level: string
      Children: StepEntry list
      Omitted: int }

// Условие применимости ответа (канал record-condition): запись языка («a ≠ 0»), S-выражение ((/= a 0)), причина
type ConditionEntry =
    { Pretty: string
      Sexpr: string
      Reason: string }

// Подшаг 22.6: сертификат — проверка ответа независимым путём. Подробности (detail) — небольшое дерево значений
type CertDetail =
    | DStr of string
    | DList of CertDetail list
    | DObj of (string * CertDetail) list

// kind: derivative | substitution | equivalence | counterexample | ideal_membership | none;
// verified: "true" | "false" (в JSON — булевы), "numeric" (только численно), "partial" (часть не проверена),
// "skipped" (проверить нечем, причина в detail), "timeout" (не хватило времени);
// method — чем проверено («simplify», «numeric at 5 points», ...)
type CertificateEntry =
    { Kind: string
      Verified: string
      Method: string
      Detail: CertDetail }

type ToolResponse =
    { Status: Status
      Result: string option              // S-выражение (по строке на оператор/форму)
      Pretty: string option              // запись на математическом языке
      Latex: string option               // LaTeX-запись (шаг TEX.1; KaTeX)
      Note: string option                // короткая причина для unknown / no-solution / nonelementary (по-русски)
      Conditions: ConditionEntry list    // явные условия ответа (канал record-condition, подшаг 22.2; всегда включён)
      Assumptions: string list           // действующие декларации доменов сессии («x ∈ ℝ»)
      Certificate: CertificateEntry option   // проверка ответа (подшаг 22.6); только по запросу certificate: true, иначе null
      Steps: StepEntry list option       // None — шаги не запрашивались (steps: none) и журнал сессии выключен
      Warnings: string list
      Output: string option              // вывод print (op "math"); для прочих операций null
      TimingMs: int64
      TimedOut: bool
      // совместимость с прежним --json
      Error: string option               // сообщение исключения (ok = false)
      Stack: string list option }        // кадры стека Lisp при ошибке

// Пустой ответ с данным статусом (заготовка для заполнения)
let empty (status: Status) : ToolResponse =
    { Status = status; Result = None; Pretty = None; Latex = None; Note = None; Conditions = []; Assumptions = []
      Certificate = None; Steps = None; Warnings = []; Output = None; TimingMs = 0L; TimedOut = false
      Error = None; Stack = None }

// ok — прежний смысл: запрос выполнен без исключения (ошибка «не умею» даёт status unknown, но ok = false)
let isOk (r: ToolResponse) : bool = r.Error.IsNone && r.Status <> Error && r.Status <> Timeout

// Кириллица и математические символы — без \uXXXX (ответ читают LLM и люди); JSON-эквивалентно прежнему
let private writerOptions = JsonWriterOptions(Encoder = JavaScriptEncoder.UnsafeRelaxedJsonEscaping)

let toJson (r: ToolResponse) : string =
    use ms = new MemoryStream()
    use w = new Utf8JsonWriter(ms, writerOptions)
    do
        let str (name: string) (v: string option) =
            match v with
            | Some s -> w.WriteString(name, s)
            | None -> w.WriteNull(name)
        let strs (name: string) (vs: string list) =
            if List.isEmpty vs then w.WriteNull(name)
            else
                w.WriteStartArray(name)
                for s in vs do w.WriteStringValue(s)
                w.WriteEndArray()
        w.WriteStartObject()
        w.WriteString("status", statusName r.Status)
        str "result" r.Result
        str "pretty" r.Pretty
        str "latex" r.Latex
        str "note" r.Note
        if List.isEmpty r.Conditions then w.WriteNull("conditions")
        else
            w.WriteStartArray("conditions")
            for c in r.Conditions do
                w.WriteStartObject()
                w.WriteString("condition", c.Pretty)
                w.WriteString("sexpr", c.Sexpr)
                w.WriteString("reason", c.Reason)
                w.WriteEndObject()
            w.WriteEndArray()
        strs "assumptions" r.Assumptions
        match r.Certificate with
        | Some c ->
            let rec detail (d: CertDetail) =
                match d with
                | DStr s -> w.WriteStringValue(s)
                | DList xs ->
                    w.WriteStartArray()
                    for x in xs do detail x
                    w.WriteEndArray()
                | DObj kvs ->
                    w.WriteStartObject()
                    for k, v in kvs do
                        w.WritePropertyName(k)
                        detail v
                    w.WriteEndObject()
            w.WriteStartObject("certificate")
            w.WriteString("kind", c.Kind)
            match c.Verified with
            | "true" -> w.WriteBoolean("verified", true)
            | "false" -> w.WriteBoolean("verified", false)
            | v -> w.WriteString("verified", v)
            w.WriteString("method", c.Method)
            w.WritePropertyName("detail")
            detail c.Detail
            w.WriteEndObject()
        | None -> w.WriteNull("certificate")
        match r.Steps with
        | Some steps ->
            let rec step (s: StepEntry) =
                w.WriteStartObject()
                w.WriteString("rule", s.Rule)
                w.WriteString("title", s.Title)
                w.WriteString("comment", s.Comment)
                w.WriteString("before", s.Before)
                w.WriteString("before_pretty", s.BeforePretty)
                w.WriteString("before_latex", s.BeforeLatex)
                w.WriteString("after", s.After)
                w.WriteString("after_pretty", s.AfterPretty)
                w.WriteString("after_latex", s.AfterLatex)
                w.WriteString("level", s.Level)
                w.WriteStartArray("children")
                for c in s.Children do step c
                w.WriteEndArray()
                if s.Omitted > 0 then w.WriteNumber("omitted", s.Omitted)
                w.WriteEndObject()
            w.WriteStartArray("steps")
            for s in steps do step s
            w.WriteEndArray()
        | None -> w.WriteNull("steps")
        strs "warnings" r.Warnings
        str "output" r.Output
        w.WriteStartObject("timing")
        w.WriteNumber("ms", r.TimingMs)
        w.WriteBoolean("timeout", r.TimedOut)
        w.WriteEndObject()
        w.WriteBoolean("ok", isOk r)
        str "error" r.Error
        match r.Stack with
        | Some st ->
            w.WriteStartArray("stack")
            for s in st do w.WriteStringValue(s)
            w.WriteEndArray()
        | None -> w.WriteNull("stack")
        w.WriteEndObject()
    w.Flush()
    System.Text.Encoding.UTF8.GetString(ms.ToArray())
