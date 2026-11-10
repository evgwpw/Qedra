// Подшаг 22.4 в процессе «Lisp --mcp»: песочница по умолчанию, timeout, отмена клиентом, --allow-dir, --unsafe
module McpProcessSandboxTests

open System
open System.Diagnostics
open System.IO
open Xunit
open McpProcess

[<Fact; Trait("Category", "Slow")>]
let ``22.4: процесс --mcp — песочница по умолчанию, timeout, отмена клиентом, --allow-dir`` () =
    let dir = Path.Combine(Path.GetTempPath(), "lisp-mcp-sbx-" + string (Guid.NewGuid()))
    Directory.CreateDirectory dir |> ignore
    let file = Path.Combine(dir, "p.lisp").Replace("\\", "/")
    File.WriteAllText(file, "(define p-v 5)")
    try
        use srv = new McpProcess()
        srv.Request(1, "initialize", """{"protocolVersion":"2025-06-18","capabilities":{},"clientInfo":{"name":"test","version":"1"}}""") |> ignore
        srv.Send """{"jsonrpc":"2.0","method":"notifications/initialized"}"""
        // песочница по умолчанию: load вне lib — error с причиной
        let denied = toolCall srv 2 "evaluate" (sprintf """{"code":"(load \"%s\")"}""" file)
        Assert.Equal("error", str denied "status")
        Assert.Contains("запрещено", str denied "error")
        // бесконечный цикл: timeout за ~timeout_s, затем сессия работает
        toolCall srv 3 "evaluate" """{"code":"(define (spin n) (spin (+ n 1)))"}""" |> ignore
        let sw = Stopwatch.StartNew()
        let t = toolCall srv 4 "evaluate" """{"code":"(spin 0)","timeout_s":1}"""
        Assert.Equal("timeout", str t "status")
        Assert.True(t.GetProperty("timing").GetProperty("timeout").GetBoolean())
        Assert.True(sw.ElapsedMilliseconds < 30000L, sprintf "timeout_s=1 сработал через %d мс" sw.ElapsedMilliseconds)
        Assert.Equal("3", str (toolCall srv 5 "evaluate" """{"code":"(+ 1 2)"}""") "result")
        // отмена клиентом: notifications/cancelled во время вычисления освобождает интерпретатор
        srv.Send """{"jsonrpc":"2.0","id":6,"method":"tools/call","params":{"name":"evaluate","arguments":{"code":"(spin 0)"}}}"""
        Threading.Thread.Sleep 500
        srv.Send """{"jsonrpc":"2.0","method":"notifications/cancelled","params":{"requestId":6,"reason":"test"}}"""
        let sw2 = Stopwatch.StartNew()
        Assert.Equal("7", str (toolCall srv 7 "evaluate" """{"code":"(+ 3 4)"}""") "result")
        Assert.True(sw2.ElapsedMilliseconds < 60000L, sprintf "после отмены ответ через %d мс" sw2.ElapsedMilliseconds)
        Assert.Equal(0, srv.Close())
        // --allow-dir: тот же load разрешён
        use srv2 = new McpProcess(sprintf " --allow-dir \"%s\"" dir)
        srv2.Request(1, "initialize", """{"protocolVersion":"2025-06-18","capabilities":{},"clientInfo":{"name":"test","version":"1"}}""") |> ignore
        srv2.Send """{"jsonrpc":"2.0","method":"notifications/initialized"}"""
        Assert.Equal("answer", str (toolCall srv2 2 "evaluate" (sprintf """{"code":"(load \"%s\") p-v"}""" file)) "status")
        Assert.Equal(0, srv2.Close())
        // --unsafe
        use srv3 = new McpProcess(" --unsafe")
        srv3.Request(1, "initialize", """{"protocolVersion":"2025-06-18","capabilities":{},"clientInfo":{"name":"test","version":"1"}}""") |> ignore
        srv3.Send """{"jsonrpc":"2.0","method":"notifications/initialized"}"""
        Assert.Equal("answer", str (toolCall srv3 2 "evaluate" (sprintf """{"code":"(load \"%s\")"}""" file)) "status")
        Assert.Equal(0, srv3.Close())
    finally
        Directory.Delete(dir, true)
