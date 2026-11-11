// LEAN.L3: --lean-results в CLI — статус Lean попадает в сертификат ответа; чужой хеш даёт not-run.
module LeanCliTests

open System
open System.IO
open System.Text.Json
open Xunit
open CliProcess

let private hashOf (id: string) : string =
    // тот же генератор и id, что у сертификата MCP (id = "antiderivative")
    let code =
        "(lean-hash (lean-emit-antiderivative 'x '(* 1/2 (^ x 2)) 'x '() \"" + id + "\"))"
    let rc, out, err = runLisp [ "-e"; code ]
    Assert.True((rc = 0), out + err)
    out.Trim().Trim('"')

let private writeResults (path: string) (hash: string) : unit =
    let line =
        "{\"id\":\"cli\",\"status\":\"passed\",\"lean\":\"4.34.0-rc2\",\"mathlib\":\"v4.34.0-rc2\",\"seconds\":1.0,"
        + "\"log\":\"\",\"hash\":\"" + hash + "\",\"file\":\"lean/catalog/cli.lean\",\"lemma\":\"qedra_int_cli\"}"
    File.WriteAllText(path, line + "\n")

let private request : string =
    "{\"op\":\"integrate\",\"code\":\"x\",\"var\":\"x\",\"syntax\":\"lisp\",\"certificate\":\"lean\"}\n"

[<Fact>]
let ``LEAN.L3: --lean-results — passed по хешу попадает в certificate.detail.lean`` () =
    let h = hashOf "antiderivative"
    let path = Path.Combine(Path.GetTempPath(), "lean-results-" + Guid.NewGuid().ToString("N") + ".jsonl")
    try
        writeResults path h
        let rc, out, err = runLispStdin request [ "--lean-results"; path; "--json" ]
        Assert.True((rc = 0), out + err)
        use doc = JsonDocument.Parse out
        let c = doc.RootElement.GetProperty("certificate")
        Assert.Equal("lean", c.GetProperty("kind").GetString())
        let lean = c.GetProperty("detail").GetProperty("lean")
        Assert.Equal("passed", lean.GetProperty("status").GetString())
        Assert.Equal("lean/catalog/cli.lean", lean.GetProperty("file").GetString())
        Assert.Equal("qedra_int_cli", lean.GetProperty("lemma").GetString())
        Assert.Contains("theorem qedra_int_antiderivative", c.GetProperty("detail").GetProperty("lean_source").GetString())
    finally
        if File.Exists path then File.Delete path

[<Fact>]
let ``LEAN.L3: чужой хеш (подделка passed) — not-run`` () =
    let h = hashOf "another-id"
    let path = Path.Combine(Path.GetTempPath(), "lean-results-" + Guid.NewGuid().ToString("N") + ".jsonl")
    try
        // в записи passed лежит хеш ДРУГОГО текста: текущая генерация его не находит
        writeResults path h
        let rc, out, err = runLispStdin request [ "--lean-results"; path; "--json" ]
        Assert.True((rc = 0), out + err)
        use doc = JsonDocument.Parse out
        let lean = doc.RootElement.GetProperty("certificate").GetProperty("detail").GetProperty("lean")
        Assert.Equal("not-run", lean.GetProperty("status").GetString())
    finally
        if File.Exists path then File.Delete path
