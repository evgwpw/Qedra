// Клиент JSON-RPC поверх stdio процесса «Lisp --mcp» (общий для тестов проекта).
// Ускорение тестов: эти тесты вынесены из Lisp.Tests в отдельный проект — у каждого теста свой процесс и свои данные,
// глобального состояния Lisp в тестовом процессе нет, поэтому коллекции xUnit идут ПАРАЛЛЕЛЬНО.
module McpProcess

open System
open System.Collections.Generic
open System.Diagnostics
open System.IO
open System.Text
open System.Text.Json
open Xunit

let parse (json: string) : JsonElement = JsonDocument.Parse(json).RootElement
let str (r: JsonElement) (name: string) : string = r.GetProperty(name).GetString()
let has (r: JsonElement) (name: string) : bool = fst (r.TryGetProperty name)

// Предел ожидания ответа: большой запас на холодный старт (prelude) при полной загрузке процессами решения
let replyTimeout = TimeSpan.FromSeconds 180.0

// Запрос — строка JSON, ответ — первая строка stdout с тем же id
type McpProcess(extraArgs: string) =
    let psi = ProcessStartInfo("dotnet", "\"" + Path.Combine(AppContext.BaseDirectory, "Lisp.dll") + "\" --mcp" + extraArgs)
    do
        psi.RedirectStandardInput <- true
        psi.RedirectStandardOutput <- true
        psi.RedirectStandardError <- true
        psi.UseShellExecute <- false
        psi.StandardOutputEncoding <- UTF8Encoding(false)
        psi.StandardInputEncoding <- UTF8Encoding(false)
        psi.WorkingDirectory <- AppContext.BaseDirectory
    let p = Process.Start psi
    let stderr = StringBuilder()
    do p.ErrorDataReceived.Add(fun e -> if not (isNull e.Data) then lock stderr (fun () -> stderr.AppendLine e.Data |> ignore))
    do p.BeginErrorReadLine()
    let lines = List<string>()
    new() = new McpProcess("")
    member _.Lines = lines
    member _.Stderr = lock stderr (fun () -> stderr.ToString())
    member _.Send(json: string) =
        p.StandardInput.WriteLine json
        p.StandardInput.Flush()
    member this.Request(id: int, meth: string, prms: string) : JsonElement =
        this.Send(sprintf """{"jsonrpc":"2.0","id":%d,"method":"%s","params":%s}""" id meth prms)
        let deadline = DateTime.UtcNow + replyTimeout
        let mutable result = None
        while result.IsNone do
            // чтение с настоящим таймаутом: ReadLine без него вис бы до убийства тестового хоста (под нагрузкой — минуты)
            let left = deadline - DateTime.UtcNow
            let task = p.StandardOutput.ReadLineAsync()
            if left <= TimeSpan.Zero || not (task.Wait left) then
                (try p.Kill true with _ -> ())
                failwithf "нет ответа на %s за %d с (stderr: %s)" meth (int replyTimeout.TotalSeconds) this.Stderr
            let line = task.Result
            if isNull line then failwithf "процесс закрыл stdout (stderr: %s)" this.Stderr
            lines.Add line
            let msg = parse line
            match msg.TryGetProperty "id" with
            | true, v when v.ValueKind = JsonValueKind.Number && v.GetInt32() = id -> result <- Some msg
            | _ -> ()
        result.Value
    member _.Close() : int =
        p.StandardInput.Close()
        if not (p.WaitForExit 60000) then p.Kill true
        p.ExitCode
    interface IDisposable with
        member _.Dispose() = if not p.HasExited then p.Kill true

let toolCall (srv: McpProcess) (id: int) (name: string) (arguments: string) : JsonElement =
    let r = srv.Request(id, "tools/call", sprintf """{"name":"%s","arguments":%s}""" name arguments)
    Assert.Equal("2.0", str r "jsonrpc")
    let res = r.GetProperty "result"
    Assert.False(has res "isError" && res.GetProperty("isError").GetBoolean())
    // текст и структура — один и тот же ToolResponse
    let text = res.GetProperty("content").[0]
    Assert.Equal("text", str text "type")
    let fromText = parse (str text "text")
    let structured = res.GetProperty "structuredContent"
    Assert.Equal(str fromText "status", str structured "status")
    Assert.Equal(fromText.GetProperty("result").ToString(), structured.GetProperty("result").ToString())
    structured
