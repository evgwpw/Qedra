// Шаг 21, коммит 3: JSON-API op "math" и пример examples\demo.mth
module MathLangApiTests

open System.IO
open System.Text.Json
open Xunit

// Запрос к сессии → разобранный ответ
let private call (session: Types.Env) (json: string) : JsonElement =
    JsonDocument.Parse(AgentApi.handleJsonRequest session json).RootElement

// Код программы → JSON-запрос op math (строка экранируется сериализатором)
let private req (code: string) : string =
    JsonSerializer.Serialize({| op = "math"; code = code |})

let private str (r: JsonElement) (name: string) : string = r.GetProperty(name).GetString()

[<Fact>]
let ``API math: определение и вызов функции`` () =
    let r = call (AgentApi.makeSession ()) (req "f(x) := x^2 + sin(x)\na := 5\nf(a)")
    Assert.True(r.GetProperty("ok").GetBoolean())
    Assert.Equal("f(x) := x^2 + sin(x)\n5\n25 + sin(5)", str r "pretty")

[<Fact>]
let ``API math: result — S-выражение последнего значения`` () =
    let r = call (AgentApi.makeSession ()) (req "x^2 + 1")
    Assert.Equal("(+ 1 (^ x 2))", str r "result")
    Assert.Equal("1 + x^2", str r "pretty")

[<Fact>]
let ``API math: сессия сохраняет переменные и функции между запросами`` () =
    let s = AgentApi.makeSession ()
    call s (req "g(t) := t*2; b := 21") |> ignore
    let r = call s (req "g(b)")
    Assert.Equal("42", str r "pretty")
    // другая сессия их не видит
    let r2 = call (AgentApi.makeSession ()) (req "g(b)")
    Assert.Equal("g(b)", str r2 "pretty")

[<Fact>]
let ``API math: векторы, множества, булевы в синтаксисе языка`` () =
    let s = AgentApi.makeSession ()
    Assert.Equal("[2, 4, 6]", str (call s (req "2*[1, 2, 3]")) "pretty")
    Assert.Equal("{1, 2, 3}", str (call s (req "{1, 2} ∪ {3}")) "pretty")
    Assert.Equal("true", str (call s (req "2 ∈ {1, 2}")) "pretty")
    Assert.Equal("unknown", str (call s (req "apiq ∈ {1, 2}")) "pretty")

[<Fact>]
let ``API math: integrate, limit, solve`` () =
    let s = AgentApi.makeSession ()
    Assert.Equal("1/3*x^3", str (call s (req "integrate(x^2, x)")) "pretty")
    Assert.Equal("1", str (call s (req "limit(sin(x)/x, x, 0)")) "pretty")
    Assert.Equal("{2, 3}", str (call s (req "solve(x^2 - 5x + 6 = 0, x)")) "pretty")

[<Fact>]
let ``API math: ошибка разбора — позиция и без стека`` () =
    let r = call (AgentApi.makeSession ()) (req "a := 1\nb := )")
    Assert.False(r.GetProperty("ok").GetBoolean())
    Assert.Contains("строка 2, позиция 6", str r "error")
    Assert.Equal(0, r.GetProperty("stack").GetArrayLength())

[<Fact>]
let ``API math: ошибка вычисления — сообщение без стека Lisp`` () =
    let r = call (AgentApi.makeSession ()) (req "v := [1, 2, 3]; v[4]")
    Assert.False(r.GetProperty("ok").GetBoolean())
    Assert.Contains("вне границ", str r "error")
    Assert.Equal(0, r.GetProperty("stack").GetArrayLength())

[<Fact>]
let ``API math: без кода — ошибка протокола; op parse не изменился`` () =
    let s = AgentApi.makeSession ()
    let r = call s "{\"op\":\"math\"}"
    Assert.False(r.GetProperty("ok").GetBoolean())
    let p = call s "{\"op\":\"parse\",\"code\":\"2x+3\"}"
    Assert.Equal("(+ (* 2 x) 3)", str p "result")

[<Fact>]
let ``API eval и math-eval в Lisp-сессии согласованы`` () =
    let s = AgentApi.makeSession ()
    let r = call s (JsonSerializer.Serialize({| op = "eval"; code = "(math-show (math-eval \"a := 3; a^2 + 1\"))" |}))
    Assert.Equal("\"10\"", str r "result")

[<Fact>]
let ``demo.mth выполняется без ошибок`` () =
    let path = Path.Combine(System.AppContext.BaseDirectory, "examples", "demo.mth")
    Assert.True(File.Exists path, path)
    let s = AgentApi.makeSession ()
    let r = call s (req (File.ReadAllText path))
    Assert.True(r.GetProperty("ok").GetBoolean(), (if r.GetProperty("ok").GetBoolean() then "" else str r "error"))
    let lines = (str r "pretty").Split('\n')
    Assert.Contains("1/3*x^3 - cos(x)", lines)
    Assert.Contains("3628800", lines)
    Assert.Contains("[[-2, 1], [3/2, -1/2]]", lines)
    Assert.Contains("{[x = 2, y = 1]}", lines)

// Шаг 21a: examples\programs.mth — 9 программ (циклы, return, локальные переменные, итераторы)
[<Fact>]
let ``programs.mth выполняется без ошибок и даёт ожидаемые значения`` () =
    let path = Path.Combine(System.AppContext.BaseDirectory, "examples", "programs.mth")
    Assert.True(File.Exists path, path)
    let r = call (AgentApi.makeSession ()) (req (File.ReadAllText path))
    Assert.True(r.GetProperty("ok").GetBoolean(), (if r.GetProperty("ok").GetBoolean() then "" else str r "error"))
    let lines = (str r "pretty").Split('\n')
    Assert.Contains("21", lines)                                                       // НОД(1071, 462)
    Assert.Contains("886731088897/627013566048", lines)                                // 5 шагов Ньютона (рациональные)
    Assert.True(lines |> Array.exists (fun l -> l.StartsWith "1.41421356237"), "Ньютон sqrt(2), float")
    Assert.Contains("[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]", lines) // решето
    Assert.Contains("832040", lines)                                                   // F(30)
    Assert.Contains("[[0, 1], [1, 1], [1, 2], [2, 3], [3, 5], [5, 8], [8, 13], [13, 21], [21, 34]]", lines)
    Assert.True(lines |> Array.exists (fun l -> l.StartsWith "2.71692393223"), "метод Эйлера")
    Assert.Contains("[[0, -2], [1, -1], [2, 2], [3, 7], [4, 14]]", lines)
    Assert.Contains("[-2, -7/4, -1, 1/4, 2]", lines)
    Assert.Contains("1 + x + 1/2*x^2 + 1/6*x^3 + 1/24*x^4 + 1/120*x^5", lines)
    Assert.Contains("0", lines)                                                        // partial(5) совпадает с taylor
    Assert.Contains("111", lines)                                                      // Коллатц(27)
    Assert.Contains("[1, 2, 3, 5, 7, 9]", lines)                                       // пузырёк

[<Fact>]
let ``API math: программирование — loop, return, ошибки без стека`` () =
    let s = AgentApi.makeSession ()
    let p = str (call s (req "s := 0; k := 1; loop(if(k > 100, exit), s := s + k, k := k + 1); s")) "pretty"
    Assert.Equal("5050", Array.last (p.Split('\n')))
    let r = call s (req "x := 7; solve(x^2 - 5x + 6 = 0, x)")
    Assert.False(r.GetProperty("ok").GetBoolean())
    Assert.Equal("x имеет значение 7 — переменная решения не должна быть присвоена; снимите присваивание: x :=", str r "error")
    Assert.Equal(0, r.GetProperty("stack").GetArrayLength())
    let r2 = call s (req "a := b; b := a")
    Assert.Equal("циклическое определение b", str r2 "error")
    Assert.Equal("[1, 4, 9]", str (call s (req "vector(k^2, k, 3)")) "pretty")

[<Fact>]
let ``load-math выполняет файл языка`` () =
    let path = Path.Combine(System.AppContext.BaseDirectory, "examples", "demo.mth")
    let s = AgentApi.makeSession ()
    // последний оператор demo.mth — значение символа a после clear(a)
    let r = call s (req ("load(\"" + path.Replace("\\", "\\\\") + "\")"))
    Assert.True(r.GetProperty("ok").GetBoolean(), (if r.GetProperty("ok").GetBoolean() then "" else str r "error"))
    Assert.Equal("a", str r "pretty")
    // функции из файла остались в сессии
    Assert.Equal("120", str (call s (req "fact(5)")) "pretty")

[<Fact>]
let ``load-math: ошибка разбора указывает файл`` () =
    let tmp = Path.Combine(Path.GetTempPath(), "mathlang_bad_" + System.Guid.NewGuid().ToString("N") + ".mth")
    File.WriteAllText(tmp, "a := 1\nb := )\n")
    try
        let r = call (AgentApi.makeSession ()) (req ("load(\"" + tmp.Replace("\\", "\\\\") + "\")"))
        Assert.False(r.GetProperty("ok").GetBoolean())
        Assert.Contains(Path.GetFileName tmp, str r "error")
        Assert.Contains("строка 2", str r "error")
    finally
        File.Delete tmp

// Шаг 21b: print в режиме JSON не пишет в stdout (ломал поток ответов), а возвращается в поле output
[<Fact>]
let ``API math: print накапливается в поле output`` () =
    let s = AgentApi.makeSession ()
    let r = call s (req "print(1, x + 1)\nprint(\"привет\", 2)\n5")
    Assert.True(r.GetProperty("ok").GetBoolean())
    Assert.Equal("1 1 + x\nпривет 2", str r "output")
    // значение print — последний аргумент; результаты операторов не затронуты
    Assert.Equal("1 + x\n2\n5", str r "pretty")
    // следующий запрос — свой output; без print — пустая строка
    Assert.Equal("", str (call s (req "2 + 2")) "output")
    let loop = call s (req "k := 1; loop(if(k > 3, exit), print(k), k := k + 1)")
    Assert.Equal("1\n2\n3", str loop "output")

[<Fact>]
let ``API math: print в функции, пустой print, вывод до ошибки`` () =
    let s = AgentApi.makeSession ()
    Assert.Equal("a 7", str (call s (req "f(n) := print(\"a\", n); f(7)")) "output")
    Assert.Equal("", str (call s (req "print()")) "output")
    let r = call s (req "print(1); print(2); 1/0")
    Assert.False(r.GetProperty("ok").GetBoolean())
    Assert.Equal("1\n2", str r "output")
    // после ошибки перехват снят: следующий запрос чист
    Assert.Equal("", str (call s (req "3")) "output")
    // ошибка разбора — до выполнения, печатать нечего
    let bad = call s (req "print(1); b := )")
    Assert.False(bad.GetProperty("ok").GetBoolean())
    Assert.Equal("", str bad "output")
