// Шаг 22.3: интеграционный тест — процесс «Lisp --mcp»: initialize → tools/list → tools/call,
// ответы JSON-RPC и поля ToolResponse, stdout содержит только сообщения протокола
module McpProcessProtocolTests

open System
open Xunit
open McpProcess

[<Fact>]
let ``MCP: процесс --mcp — initialize, tools/list, tools/call; stdout — только JSON-RPC`` () =
    use srv = new McpProcess()
    let init =
        srv.Request(1, "initialize", """{"protocolVersion":"2025-06-18","capabilities":{},"clientInfo":{"name":"test","version":"1"}}""")
    let info = init.GetProperty("result")
    Assert.Equal("qedra", info.GetProperty("serverInfo").GetProperty("name").GetString())
    Assert.True(has (info.GetProperty "capabilities") "tools")
    srv.Send """{"jsonrpc":"2.0","method":"notifications/initialized"}"""
    let list = srv.Request(2, "tools/list", "{}").GetProperty("result").GetProperty("tools")
    let names = list.EnumerateArray() |> Seq.map (fun t -> str t "name") |> Set.ofSeq
    for n in [ "math"; "evaluate"; "simplify"; "diff"; "integrate"; "sum"; "solve"; "reset"
               "expand"; "factor"; "together"; "apart"; "limit"; "series"; "groebner"; "declare"; "undeclare"; "declarations"
               "equivalent"; "guide"; "code"; "linear-algebra"; "linear-programming" ] do
        Assert.Contains(n, names)
    Assert.Equal(23, names.Count)
    // ресурс lisp://guide (подшаг 22.5)
    Assert.True(has (info.GetProperty "capabilities") "resources")
    let res = srv.Request(20, "resources/list", "{}").GetProperty("result").GetProperty("resources")
    Assert.Equal("lisp://guide", str res.[0] "uri")
    let read = srv.Request(21, "resources/read", """{"uri":"lisp://guide"}""").GetProperty("result").GetProperty("contents").[0]
    Assert.Contains("CAS guide for LLMs", str read "text")
    Assert.Equal("text/markdown", str read "mimeType")
    Assert.True(has (srv.Request(22, "resources/read", """{"uri":"lisp://nope"}""")) "error")
    let eq = toolCall srv 23 "equivalent" """{"a":"x^2","b":"x^2+1"}"""
    Assert.Equal("false", str eq "result")
    Assert.Equal("answer", str eq "status")
    Assert.Contains("CAS guide for LLMs", str (toolCall srv 24 "guide" "{}") "result")
    for t in list.EnumerateArray() do
        Assert.Equal("object", t.GetProperty("inputSchema").GetProperty("type").GetString())
        Assert.False(String.IsNullOrWhiteSpace(str t "description"))
    // solve с параметром: ответ и условие a ≠ 0
    let sol = toolCall srv 3 "solve" """{"equations":"a*x = 1","vars":"x"}"""
    Assert.Equal("answer", str sol "status")
    Assert.Equal("{1/a}", str sol "pretty")
    Assert.Equal("a ≠ 0", sol.GetProperty("conditions").[0].GetProperty("condition").GetString())
    // интеграл, доказанно неэлементарный (21k.5, Риш): nonelementary + невычисленная форма
    let unk = toolCall srv 4 "integrate" """{"expr":"exp(x^2)","var":"x"}"""
    Assert.Equal("nonelementary", str unk "status")
    Assert.Equal("integrate(exp(x^2), x)", str unk "pretty")
    Assert.False(String.IsNullOrEmpty(str unk "note"))
    // вывод display/print не попадает в stdout — он в поле output
    let ev = toolCall srv 5 "evaluate" """{"code":"(display \"MCP-NOISE\") (newline) (+ 1 2)"}"""
    Assert.Equal("answer", str ev "status")
    Assert.Contains("MCP-NOISE", str ev "output")
    let m = toolCall srv 6 "math" """{"code":"print(\"MCP-PRINT\"); h(x) := x^2; h(3)"}"""
    Assert.Equal("MCP-PRINT", str m "output")
    Assert.EndsWith("9", str m "pretty")
    // сессия общая между инструментами; reset её сбрасывает
    Assert.Equal("2x", str (toolCall srv 7 "diff" """{"expr":"h(x)","var":"x"}""") "pretty")
    Assert.Equal("answer", str (toolCall srv 8 "reset" "{}") "status")
    Assert.Equal("h(3)", str (toolCall srv 9 "math" """{"code":"h(3)"}""") "pretty")
    // ошибка вычисления — обычный ответ status error
    let err = toolCall srv 10 "simplify" """{"expr":"1/0"}"""
    Assert.Equal("error", str err "status")
    // неизвестный инструмент — ошибка JSON-RPC
    let unknownTool = srv.Request(11, "tools/call", """{"name":"nope","arguments":{}}""")
    Assert.True(has unknownTool "error")
    Assert.Equal("2.0", str (srv.Request(12, "ping", "{}")) "jsonrpc")
    // stdout: каждая строка — сообщение JSON-RPC 2.0 (печать display/print, попади она в stdout, дала бы строку не-JSON)
    Assert.NotEmpty(srv.Lines)
    for line in srv.Lines do
        Assert.Equal("2.0", str (parse line) "jsonrpc")
    Assert.Equal(0, srv.Close())
