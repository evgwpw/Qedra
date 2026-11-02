// Шаг 20: JSON-API ops series и limit; reader — в ReaderTests.fs, Lisp-тесты рядов/пределов — tests\lisp\series.lisp, limit.lisp
module SeriesLimitApiTests

open Xunit

let private call (json: string) = AgentApi.handleJsonRequest (AgentApi.makeSession ()) json

[<Fact>]
let ``API series: ряд Лорана 1/sin x`` () =
    let r = call "{\"op\":\"series\",\"code\":\"(/ 1 (sin x))\",\"var\":\"x\",\"order\":3}"
    Assert.Contains("\"ok\":true", r)
    Assert.Contains("x^-1", r)
    Assert.Contains("O(x^3)", r)

[<Fact>]
let ``API series: точка по умолчанию 0, порядок по умолчанию 6`` () =
    let r = call "{\"op\":\"series\",\"code\":\"(exp x)\",\"var\":\"x\"}"
    Assert.Contains("O(x^6)", r)

[<Fact>]
let ``API limit: sin x / x`` () =
    let r = call "{\"op\":\"limit\",\"code\":\"(/ (sin x) x)\",\"var\":\"x\",\"point\":\"0\"}"
    Assert.Contains("\"result\":\"1\"", r)

[<Fact>]
let ``API limit: односторонний и на бесконечности`` () =
    let r1 = call "{\"op\":\"limit\",\"code\":\"(/ 1 x)\",\"var\":\"x\",\"point\":\"0\",\"side\":\"minus\"}"
    Assert.Contains("\"result\":\"-inf\"", r1)
    let r2 = call "{\"op\":\"limit\",\"code\":\"(/ (log x) x)\",\"var\":\"x\",\"point\":\"inf\"}"
    Assert.Contains("\"result\":\"0\"", r2)

[<Fact>]
let ``API limit: нет point — ошибка, невычисленная форма — не ошибка`` () =
    let r1 = call "{\"op\":\"limit\",\"code\":\"(sin x)\",\"var\":\"x\"}"
    Assert.Contains("\"ok\":false", r1)
    let r2 = call "{\"op\":\"limit\",\"code\":\"(sin x)\",\"var\":\"x\",\"point\":\"inf\"}"
    Assert.Contains("\"ok\":true", r2)
    Assert.Contains("limit", r2)
