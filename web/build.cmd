@echo off
setlocal
rem WASM.2d/WASM.4a: publish the browser build into web\dist.
rem AOT is the default (fast runtime, big folder); pass -i / --interpreter for the interpreter build.
rem Usage: build.cmd [-i] [extra msbuild args]
rem NOTE: comments here are ASCII only -- cmd reads this file in the OEM codepage, and UTF-8
rem Cyrillic bytes used to break parsing of the flags below (AOT=0 was ignored).
set AOT=1
if /i "%~1"=="-i" set AOT=0
if /i "%~1"=="--interpreter" set AOT=0
if /i "%~1"=="aot" set AOT=1
if exist "%~dp0dist" rmdir /s /q "%~dp0dist"

rem WASM.4a: interface is TypeScript + JSX built by Vite (npm ci by package-lock.json, exact versions)
pushd "%~dp0"
call npm ci --no-audit --no-fund
if errorlevel 1 (popd & echo BUILD FAILED: npm ci & exit /b 1)
call npm run typecheck
if errorlevel 1 (popd & echo BUILD FAILED: typecheck & exit /b 1)
call npm run build
if errorlevel 1 (popd & echo BUILD FAILED: vite build & exit /b 1)
popd

rem WASM.3a/4a: function catalog from docs\math-language.md (TS generator); its examples are checked
rem by running Lisp.exe, so build the desktop host first
dotnet build "%~dp0..\src\Lisp.Host\Lisp.Host.fsproj" -c Debug -nologo
if errorlevel 1 (echo BUILD FAILED: Lisp.Host & exit /b 1)
pushd "%~dp0"
call npm run gen:functions -- app\functions.json
if errorlevel 1 (popd & echo BUILD FAILED: functions.json & exit /b 1)
rem WASM.5b: example problems (web/app/examples/*.json) are generated separately: npm run gen:examples
popd

rem WebCIL (assemblies served as .wasm) makes the Worker exit(1) in the interpreter build -- verified 2026-11-01
if "%AOT%"=="1" (
  dotnet publish "%~dp0..\src\Lisp.Wasm\Lisp.Wasm.csproj" -c Release -o "%~dp0dist" -p:RunAOTCompilation=true %2 %3 %4 %5
) else (
  dotnet publish "%~dp0..\src\Lisp.Wasm\Lisp.Wasm.csproj" -c Release -o "%~dp0dist" -p:RunAOTCompilation=false -p:WasmEnableWebcil=false %2 %3 %4 %5
)
if errorlevel 1 (
  echo BUILD FAILED
  exit /b 1
)
echo Built %~dp0dist with AOT=%AOT%
echo Start it with start.cmd
