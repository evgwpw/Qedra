// REL.1a: --sandbox и --version в процессе Lisp — пять режимов × (разрешено, запрещено),
// обходы (.., абсолютный путь, регистр), отсутствие изменения поведения без флага
module SandboxCliTests

open System
open System.IO
open Xunit
open CliProcess

// Каталог пробы: ok — разрешён через --allow-dir, bad — вне разрешённых
type private Probe =
    { Ok: string
      Bad: string
      OkLisp: string
      BadLisp: string }

let private slash (p: string) : string = p.Replace('\\', '/')

let private writeFile (dir: string) (name: string) (text: string) : string =
    let p = Path.Combine(dir, name)
    File.WriteAllText(p, text)
    p

let private withProbe (f: Probe -> unit) =
    let root = Path.Combine(Path.GetTempPath(), "rel1a-" + Guid.NewGuid().ToString("N").Substring(0, 8))
    let ok = Path.Combine(root, "ok")
    let bad = Path.Combine(root, "bad")
    Directory.CreateDirectory ok |> ignore
    Directory.CreateDirectory bad |> ignore
    let okLisp = writeFile ok "ok.lisp" "(define sb-ok 42)"
    let badLisp = writeFile bad "bad.lisp" "(define sb-bad 7)"
    writeFile ok "ok.mth" "okval := 42" |> ignore
    writeFile bad "bad.mth" "badval := 7" |> ignore
    try f { Ok = ok; Bad = bad; OkLisp = okLisp; BadLisp = badLisp }
    finally (try Directory.Delete(root, true) with _ -> ())

[<Fact>]
let ``REL.1a: --version — версия из сборки (Qedra 1.109.7.11), код 0`` () =
    let code, out, _ = runLisp [ "--version" ]
    Assert.Equal(0, code)
    Assert.Equal("Qedra 1.109.7.11", out)
    // та же версия лежит в сборке Lisp.dll (строка в коде не дублируется)
    let asm = Reflection.Assembly.LoadFrom(Path.Combine(AppContext.BaseDirectory, "Lisp.dll"))
    Assert.Equal("Qedra " + asm.GetName().Version.ToString(), out)

[<Fact>]
let ``REL.1a: --help описывает --sandbox, --allow-dir и --version`` () =
    let code, out, _ = runLisp [ "--help" ]
    Assert.Equal(0, code)
    Assert.Contains("--sandbox", out)
    Assert.Contains("--allow-dir", out)
    Assert.Contains("--version", out)

[<Fact>]
let ``REL.1a: файл — load из --allow-dir работает, вне — ошибка, без флага — как раньше`` () =
    withProbe (fun p ->
        let okMain = writeFile p.Ok "main-ok.lisp" (sprintf "(load \"%s\") (display sb-ok) (newline)" (slash p.OkLisp))
        let badMain = writeFile p.Ok "main-bad.lisp" (sprintf "(load \"%s\") (display sb-bad) (newline)" (slash p.BadLisp))
        let code1, out1, _ = runLisp [ "--sandbox"; "--allow-dir"; p.Ok; okMain ]
        Assert.Equal(0, code1)
        Assert.Contains("42", out1)
        let code2, out2, _ = runLisp [ "--sandbox"; "--allow-dir"; p.Ok; badMain ]
        Assert.Equal(1, code2)
        Assert.Contains("запрещено", out2)
        // без --sandbox — прежнее поведение: load вне каталогов работает
        let code3, out3, _ = runLisp [ badMain ]
        Assert.Equal(0, code3)
        Assert.Contains("7", out3))

[<Fact>]
let ``REL.1a: -e — load из --allow-dir работает, вне — ошибка, без флага — как раньше`` () =
    withProbe (fun p ->
        let ok = sprintf "(load \"%s\")" (slash p.OkLisp)
        let bad = sprintf "(load \"%s\")" (slash p.BadLisp)
        let code1, out1, _ = runLisp [ "--sandbox"; "--allow-dir"; p.Ok; "-e"; ok; "-e"; "sb-ok" ]
        Assert.Equal(0, code1)
        Assert.Equal("42", out1)
        let code2, out2, _ = runLisp [ "--sandbox"; "--allow-dir"; p.Ok; "-e"; bad ]
        Assert.Equal(1, code2)
        Assert.Contains("запрещено", out2)
        let code3, out3, _ = runLisp [ "-e"; bad; "-e"; "sb-bad" ]
        Assert.Equal(0, code3)
        Assert.Equal("7", out3))

[<Fact>]
let ``REL.1a: --math файл — load из --allow-dir работает, вне — ошибка`` () =
    withProbe (fun p ->
        let okMth = Path.Combine(p.Ok, "ok.mth")
        let badMth = Path.Combine(p.Bad, "bad.mth")
        let okMain = writeFile p.Ok "main-ok.mth" (sprintf "load(\"%s\")" (slash okMth))
        let badMain = writeFile p.Ok "main-bad.mth" (sprintf "load(\"%s\")" (slash badMth))
        let code1, out1, _ = runLisp [ "--sandbox"; "--allow-dir"; p.Ok; okMain ]
        Assert.Equal(0, code1)
        Assert.Equal("42", out1)
        let code2, out2, _ = runLisp [ "--sandbox"; "--allow-dir"; p.Ok; badMain ]
        Assert.Equal(1, code2)
        Assert.Contains("запрещено", out2))

[<Fact>]
let ``REL.1a: --math -e — load из --allow-dir работает, вне — ошибка`` () =
    withProbe (fun p ->
        let okMth = Path.Combine(p.Ok, "ok.mth")
        let badMth = Path.Combine(p.Bad, "bad.mth")
        let code1, out1, _ =
            runLisp [ "--math"; "--sandbox"; "--allow-dir"; p.Ok; "-e"; sprintf "load(\"%s\")" (slash okMth) ]
        Assert.Equal(0, code1)
        Assert.Equal("42", out1)
        let code2, out2, _ =
            runLisp [ "--math"; "--sandbox"; "--allow-dir"; p.Ok; "-e"; sprintf "load(\"%s\")" (slash badMth) ]
        Assert.Equal(1, code2)
        Assert.Contains("запрещено", out2))

[<Fact>]
let ``REL.1a: --json — load из --allow-dir работает (answer), вне — status error`` () =
    withProbe (fun p ->
        let jsonReq (code: string) =
            "{\"op\": \"eval\", \"code\": \"" + code.Replace("\\", "\\\\").Replace("\"", "\\\"") + "\"}"
        let okReq = jsonReq (sprintf "(load \"%s\")" (slash p.OkLisp)) + "\n" + jsonReq "sb-ok" + "\n"
        let code1, out1, _ = runLispStdin okReq [ "--json"; "--sandbox"; "--allow-dir"; p.Ok ]
        Assert.Equal(0, code1)
        Assert.Contains("\"result\":\"42\"", out1)
        let badReq = jsonReq (sprintf "(load \"%s\")" (slash p.BadLisp)) + "\n"
        let code2, out2, _ = runLispStdin badReq [ "--json"; "--sandbox"; "--allow-dir"; p.Ok ]
        Assert.Equal(0, code2)
        Assert.Contains("\"status\":\"error\"", out2)
        Assert.Contains("запрещено", out2))

[<Fact>]
let ``REL.1a: REPL — load из --allow-dir работает, вне — ошибка, процесс жив`` () =
    withProbe (fun p ->
        let okIn = sprintf "(load \"%s\")\nsb-ok\nexit\n" (slash p.OkLisp)
        let code1, out1, _ = runLispStdin okIn [ "--sandbox"; "--allow-dir"; p.Ok ]
        Assert.Equal(0, code1)
        Assert.Contains("=> 42", out1)
        let badIn = sprintf "(load \"%s\")\n(+ 1 2)\nexit\n" (slash p.BadLisp)
        let code2, out2, _ = runLispStdin badIn [ "--sandbox"; "--allow-dir"; p.Ok ]
        Assert.Equal(0, code2)
        Assert.Contains("запрещено", out2)
        Assert.Contains("=> 3", out2))     // после ошибки REPL продолжает работу

[<Fact>]
let ``REL.1a: обходы — .., абсолютный путь, регистр букв`` () =
    withProbe (fun p ->
        // .. нормализуется: выход из разрешённого каталога запрещён
        let dotdot = sprintf "(load \"%s/../bad/bad.lisp\")" (slash p.Ok)
        let code1, out1, _ = runLisp [ "--sandbox"; "--allow-dir"; p.Ok; "-e"; dotdot ]
        Assert.Equal(1, code1)
        Assert.Contains("запрещено", out1)
        // абсолютный путь запрещённого каталога
        let code2, out2, _ =
            runLisp [ "--sandbox"; "--allow-dir"; p.Ok; "-e"; sprintf "(load \"%s\")" (slash p.BadLisp) ]
        Assert.Equal(1, code2)
        Assert.Contains("запрещено", out2)
        // регистр букв не обходит: путь в верхнем регистре по-прежнему разрешён
        let upper = (slash p.OkLisp).ToUpperInvariant()
        let code3, out3, _ =
            runLisp [ "--sandbox"; "--allow-dir"; p.Ok; "-e"; sprintf "(load \"%s\")" upper; "-e"; "sb-ok" ]
        Assert.Equal(0, code3)
        Assert.Equal("42", out3))

[<Fact>]
let ``REL.1a: --allow-dir без аргумента и несуществующий каталог — код 2`` () =
    let code1, out1, _ = runLisp [ "--sandbox"; "--allow-dir" ]
    Assert.Equal(2, code1)
    Assert.Contains("--allow-dir", out1)
    let missing = Path.Combine(Path.GetTempPath(), "rel1a-missing-" + Guid.NewGuid().ToString("N").Substring(0, 8))
    let code2, out2, _ = runLisp [ "--sandbox"; "--allow-dir"; missing; "-e"; "1" ]
    Assert.Equal(2, code2)
    Assert.Contains("каталог не найден", out2)
