// Шаг JSON.GUARD: процессные тесты режима «Lisp --json» — поле запроса timeout_s (сторож runGuarded, как в --mcp)
module JsonGuardTests

open System
open System.Diagnostics
open System.IO
open System.Text
open System.Text.Json
open Xunit
open McpProcess

// Сессия «Lisp --json»: запрос — строка JSON в stdin, ответ — строка stdout (с пределом ожидания)
type JsonProcess() =
    let psi = ProcessStartInfo("dotnet", "\"" + Path.Combine(AppContext.BaseDirectory, "Lisp.dll") + "\" --json")
    do
        psi.RedirectStandardInput <- true
        psi.RedirectStandardOutput <- true
        psi.RedirectStandardError <- true
        psi.UseShellExecute <- false
        psi.StandardOutputEncoding <- UTF8Encoding(false)
        psi.StandardInputEncoding <- UTF8Encoding(false)
        psi.WorkingDirectory <- AppContext.BaseDirectory
    let p = Process.Start psi
    do p.ErrorDataReceived.Add(fun _ -> ())
    do p.BeginErrorReadLine()
    member _.Ask(json: string) : JsonElement =
        p.StandardInput.WriteLine json
        p.StandardInput.Flush()
        let task = p.StandardOutput.ReadLineAsync()
        if not (task.Wait replyTimeout) then
            (try p.Kill true with _ -> ())
            failwithf "нет ответа за %d с" (int replyTimeout.TotalSeconds)
        if isNull task.Result then failwith "процесс закрыл stdout"
        parse task.Result
    member _.Close() : int =
        p.StandardInput.Close()
        if not (p.WaitForExit 60000) then p.Kill true
        p.ExitCode
    interface IDisposable with
        member _.Dispose() = if not p.HasExited then p.Kill true

[<Fact; Trait("Category", "Slow")>]
let ``JSON.GUARD: timeout_s — бесконечный цикл прерывается, сессия жива, без поля — прежнее поведение`` () =
    use srv = new JsonProcess()
    // (в) без timeout_s — как раньше; заодно прогрев (холодный старт библиотеки не входит в замер)
    let warm = srv.Ask """{"op":"eval","code":"(define (spin n) (spin (+ n 1)))"}"""
    Assert.Equal("answer", str warm "status")
    let plain = srv.Ask """{"op":"eval","code":"(+ 1 2)"}"""
    Assert.Equal("answer", str plain "status")
    Assert.Equal("3", str plain "result")
    Assert.False(plain.GetProperty("timing").GetProperty("timeout").GetBoolean())
    // (а) timeout_s: 1 на бесконечном цикле → status timeout за ≈ 1–2 с (запас ×3 на нагрузку)
    let sw = Stopwatch.StartNew()
    let t = srv.Ask """{"op":"eval","code":"(spin 0)","timeout_s":1}"""
    let ms = sw.ElapsedMilliseconds
    Assert.Equal("timeout", str t "status")
    Assert.True(t.GetProperty("timing").GetProperty("timeout").GetBoolean())
    Assert.False(t.GetProperty("ok").GetBoolean())
    Assert.True(ms < 6000L, sprintf "timeout_s=1 сработал через %d мс" ms)
    // (б) следующий запрос в той же сессии — верный ответ, без повторного холодного старта
    let sw2 = Stopwatch.StartNew()
    let next = srv.Ask """{"op":"eval","code":"(+ 40 2)"}"""
    Assert.Equal("answer", str next "status")
    Assert.Equal("42", str next "result")
    Assert.True(sw2.ElapsedMilliseconds < 3000L, sprintf "следующий запрос %d мс" sw2.ElapsedMilliseconds)
    // определения сессии сохранились (spin ещё определена), быстрый запрос с лимитом укладывается в него
    let fast = srv.Ask """{"op":"eval","code":"(* 6 7)","timeout_s":30}"""
    Assert.Equal("answer", str fast "status")
    Assert.Equal("42", str fast "result")
    // неверный timeout_s — ошибка протокола, процесс жив
    for bad in [ "0"; "\"abc\""; "1.5" ] do
        let e = srv.Ask(sprintf """{"op":"eval","code":"1","timeout_s":%s}""" bad)
        Assert.Equal("error", str e "status")
        Assert.Contains("timeout_s", str e "error")
    Assert.Equal("3", str (srv.Ask """{"op":"eval","code":"(+ 1 2)"}""") "result")
    Assert.Equal(0, srv.Close())
