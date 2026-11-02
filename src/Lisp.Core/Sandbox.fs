// Подшаг 22.4: песочница режима --mcp — ВСЕ ограничения в одном месте (этот файл).
// Это защита от ошибок LLM (load произвольного файла, порча файлов пользователя), а не от злоумышленника:
// интерпретатор и хост — один процесс, полной изоляции нет.
//
// Пока Enabled (включает McpHost при запуске --mcp, снимает --mcp --unsafe):
//   1. чтение файлов — (load "файл") и (load-math "файл.mth") (builtin read-text-file) — только из каталога lib\ рядом
//      с исполняемым файлом и каталогов --allow-dir <путь> (с подкаталогами; путь сравнивается после Path.GetFullPath,
//      без учёта регистра); иначе ошибка с причиной;
//   2. запись файлов — builtins записи в языке нет; новый такой builtin обязан вызвать checkWrite;
//   3. запуск процессов — builtins нет; новый такой builtin обязан вызвать checkProcess.
// REPL, файлы .lisp/.mth и --json работают без песочницы (Enabled = false).
module Sandbox

open System
open System.IO

let mutable Enabled : bool = false

// Каталог библиотеки (lib\ рядом с исполняемым файлом) — разрешён всегда
let libDir : string = Path.Combine(AppContext.BaseDirectory, "lib")

// Дополнительные разрешённые каталоги (--allow-dir), полные пути
let mutable private allowed : string list = []

// Нормализованный каталог с разделителем на конце
let private dirKey (d: string) : string =
    let full = Path.GetFullPath d
    if full.EndsWith(string Path.DirectorySeparatorChar) then full else full + string Path.DirectorySeparatorChar

// Включить песочницу с данными дополнительными каталогами (enabled = false — снять ограничения)
let configure (enabled: bool) (allowDirs: string list) : unit =
    allowed <- allowDirs |> List.map dirKey
    Enabled <- enabled

// Разрешённые для чтения каталоги (lib\ первым)
let allowedDirs () : string list = dirKey libDir :: allowed

// Перечень ограничений (для docs/mcp.md и ответов сервера, общий текст для --mcp и --sandbox)
let describe () : string =
    "песочница: чтение файлов (load, load-math) — только из "
    + String.concat ", " (allowedDirs ())
    + "; запись файлов и запуск процессов недоступны; снять ограничения — запуск без --sandbox (в режиме --mcp — --unsafe), добавить каталог — --allow-dir <путь>"

// Проверить чтение файла: вне разрешённых каталогов — ошибка с причиной
let checkRead (who: string) (path: string) : unit =
    if Enabled then
        let full =
            try Path.GetFullPath path
            with ex -> failwithf "%s: недопустимый путь «%s»: %s" who path ex.Message
        let ok = allowedDirs () |> List.exists (fun d -> full.StartsWith(d, StringComparison.OrdinalIgnoreCase))
        if not ok then
            failwithf "%s: чтение файла «%s» запрещено (%s)" who path (describe ())

let checkWrite (who: string) : unit =
    if Enabled then failwithf "%s: запись файлов запрещена (%s)" who (describe ())

let checkProcess (who: string) : unit =
    if Enabled then failwithf "%s: запуск процессов запрещён (%s)" who (describe ())
