// Документация: примеры из examples\ выполняются отдельным процессом (Lisp.dll файл) и сравниваются с эталоном рядом
// (имя.expected, схема — examples\README.md). Время вида «12.3 мс» в выводе (explain) нормализуется.
// Обновить эталоны после осознанного изменения: UPDATE_EXAMPLES=1 dotnet test tests\Lisp.Mcp.Tests --filter ExamplesTests
module ExamplesTests

open System
open System.IO
open System.Text.RegularExpressions
open Xunit
open CliProcess

let private examplesDir = Path.Combine(AppContext.BaseDirectory, "examples")

let private normalize (s: string) : string =
    let s = s.Replace("\r\n", "\n").TrimEnd()
    Regex.Replace(s, @"\d+(\.\d+)? мс", "N мс")

let private allFiles () : string list =
    Directory.GetFiles(examplesDir)
    |> Array.filter (fun p -> p.EndsWith ".lisp" || p.EndsWith ".mth")
    |> Array.map Path.GetFileName
    |> Array.sort
    |> List.ofArray

// Все примеры быстрые (< ≈ 1 с каждый); появится медленный — вынести во вторую теорию с Trait("Category", "Slow")
let cases () : seq<obj[]> = allFiles () |> Seq.map (fun f -> [| box f |])

// Исходный каталог examples (для UPDATE_EXAMPLES): вверх от выходного каталога до Lisp.slnx
let private sourceExamples () : string option =
    let rec up (d: DirectoryInfo) =
        if isNull d then None
        elif File.Exists(Path.Combine(d.FullName, "Lisp.slnx")) then Some(Path.Combine(d.FullName, "examples"))
        else up d.Parent
    up (DirectoryInfo AppContext.BaseDirectory)

let private runExample (file: string) =
    let code, out, err = runLisp [ Path.Combine(examplesDir, file) ]
    Assert.True((code = 0), sprintf "%s: код возврата %d, stderr: %s" file code err)
    let expectedPath = Path.Combine(examplesDir, Path.GetFileNameWithoutExtension file + ".expected")
    if Environment.GetEnvironmentVariable "UPDATE_EXAMPLES" = "1" then
        match sourceExamples () with
        | Some dir ->
            File.WriteAllText(Path.Combine(dir, Path.GetFileNameWithoutExtension file + ".expected"),
                              out.Replace("\r\n", "\n") + "\n", Text.UTF8Encoding(false))
        | None -> failwith "не найден Lisp.slnx"
    else
        Assert.True(File.Exists expectedPath, "нет эталона " + expectedPath + " (UPDATE_EXAMPLES=1 создаёт)")
        Assert.Equal(normalize (File.ReadAllText expectedPath), normalize out)

[<Theory; MemberData(nameof cases)>]
let ``examples: вывод совпадает с эталоном`` (file: string) = runExample file
