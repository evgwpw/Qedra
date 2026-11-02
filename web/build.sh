#!/bin/sh
# WASM.2d/WASM.4a: publish the browser build into web/dist.
# AOT is the default; pass -i / --interpreter for the interpreter build.
set -e
here=$(cd "$(dirname "$0")" && pwd)
aot=1
if [ "$1" = "-i" ] || [ "$1" = "--interpreter" ]; then aot=0; shift; fi
if [ "$1" = "aot" ]; then aot=1; shift; fi
if [ "$aot" = "1" ]; then
  set -- "-p:RunAOTCompilation=true" "$@"
else
  # WebCIL (сборки в виде .wasm) в Worker завершается с exit(1) — проверено 2026-11-01
  set -- "-p:RunAOTCompilation=false" "-p:WasmEnableWebcil=false" "$@"
fi

rm -rf "$here/dist"
# WASM.4a: интерфейс на TypeScript + JSX собирается Vite (npm ci по package-lock.json)
(cd "$here" && npm ci --no-audit --no-fund && npm run typecheck && npm run build)
# WASM.3a/4a: каталог функций входного языка (генератор на TS); примеры проверяются через Lisp.exe
dotnet build "$here/../src/Lisp.Host/Lisp.Host.fsproj" -c Debug -nologo
(cd "$here" && npm run gen:functions -- app/functions.json)
dotnet publish "$here/../src/Lisp.Wasm/Lisp.Wasm.csproj" -c Release -o "$here/dist" "$@"
echo "Built $here/dist"
echo "Start it with ./start.sh"
