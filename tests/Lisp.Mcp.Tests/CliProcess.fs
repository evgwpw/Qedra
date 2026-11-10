// Шаг D1: процессные тесты CLI: -e (Lisp/math), --help, неизвестный ключ, файл + -e, коды возврата.
// Запуск процесса как в McpProcess.fs (dotnet Lisp.dll), но аргументы передаются списком — без искажения
module CliProcess

open System
open System.Diagnostics
open System.IO

// запуск Lisp.dll с аргументами; → (код возврата, stdout, stderr)
let runLispStdin (stdin: string) (args: string list) : int * string * string =
    let psi = ProcessStartInfo("dotnet")
    psi.ArgumentList.Add(Path.Combine(AppContext.BaseDirectory, "Lisp.dll"))
    for a in args do psi.ArgumentList.Add a
    psi.RedirectStandardInput <- true
    psi.RedirectStandardOutput <- true
    psi.RedirectStandardError <- true
    psi.UseShellExecute <- false
    psi.StandardOutputEncoding <- Text.UTF8Encoding(false)
    psi.StandardInputEncoding <- Text.UTF8Encoding(false)
    psi.WorkingDirectory <- AppContext.BaseDirectory
    let p = Process.Start psi
    p.StandardInput.Write stdin
    p.StandardInput.Close()
    // асинхронное чтение с пределом: зависший процесс убивается, а не вешает тестовый хост (ReadToEnd ждал бы вечно)
    let outT = p.StandardOutput.ReadToEndAsync()
    let errT = p.StandardError.ReadToEndAsync()
    if not (p.WaitForExit 240000) then p.Kill true
    let out = outT.Result
    let err = errT.Result
    (p.ExitCode, out.Trim(), err.Trim())

// запуск без подготовленного stdin (обычные режимы закрывают ввод сразу)
let runLisp (args: string list) : int * string * string = runLispStdin "" args

// Шаг D0: запуск Lisp.dll в заданном рабочем каталоге (копия приложения); → (код, stdout, stderr)
let private runLispIn (root: string) (args: string list) : int * string * string =
    let psi = ProcessStartInfo("dotnet")
    psi.ArgumentList.Add(Path.Combine(root, "Lisp.dll"))
    for a in args do psi.ArgumentList.Add a
    psi.RedirectStandardInput <- true
    psi.RedirectStandardOutput <- true
    psi.RedirectStandardError <- true
    psi.UseShellExecute <- false
    psi.StandardOutputEncoding <- Text.UTF8Encoding(false)
    psi.StandardInputEncoding <- Text.UTF8Encoding(false)
    psi.WorkingDirectory <- root
    let p = Process.Start psi
    p.StandardInput.Close()
    // асинхронное чтение с пределом: зависший процесс убивается, а не вешает тестовый хост (ReadToEnd ждал бы вечно)
    let outT = p.StandardOutput.ReadToEndAsync()
    let errT = p.StandardError.ReadToEndAsync()
    if not (p.WaitForExit 240000) then p.Kill true
    let out = outT.Result
    let err = errT.Result
    (p.ExitCode, out.Trim(), err.Trim())

// Шаг D0: запуск во временной копии приложения (каталог Lisp.dll + lib) — тесты сломанного prelude:
// правим lib\prelude.lisp в копии, запускаем там Lisp.dll; возвращает (код, stdout, stderr)
let runLispInCopy (mutate: string -> unit) (args: string list) : int * string * string =
    let root = Path.Combine(Path.GetTempPath(), "lisp-d0-" + Guid.NewGuid().ToString("N").Substring(0, 8))
    Directory.CreateDirectory root |> ignore
    // Lisp.dll и зависимости (FSharp.Core и др.) лежат рядом с тестовой сборкой (та же выходная копия)
    for f in Directory.GetFiles(AppContext.BaseDirectory, "*.dll") do
        File.Copy(f, Path.Combine(root, Path.GetFileName f))
    for f in Directory.GetFiles(AppContext.BaseDirectory, "*.json") do
        File.Copy(f, Path.Combine(root, Path.GetFileName f))
    let exe = Path.Combine(AppContext.BaseDirectory, "Lisp.exe")
    if File.Exists exe then File.Copy(exe, Path.Combine(root, "Lisp.exe"))
    // lib копируется из bin: тестовые проекты собирают Lisp.Host и складывают lib рядом (см. fsproj)
    let srcLib = Path.Combine(AppContext.BaseDirectory, "lib")
    if Directory.Exists srcLib then
        let rec copyDir (src: string) (dst: string) =
            Directory.CreateDirectory dst |> ignore
            for f in Directory.GetFiles src do File.Copy(f, Path.Combine(dst, Path.GetFileName f))
            for d in Directory.GetDirectories src do copyDir d (Path.Combine(dst, Path.GetFileName d))
        copyDir srcLib (Path.Combine(root, "lib"))
        mutate (Path.Combine(root, "lib", "prelude.lisp"))
    try runLispIn root args
    finally
        try Directory.Delete(root, true) with _ -> ()
