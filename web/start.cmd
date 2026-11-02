@echo off
rem WASM.2d: start the published app on http://localhost:8080/app/index.html
rem Uses the built-in PowerShell (no extra software). Args: [port] [-nobrowser]
setlocal
set PORT=8080
if not "%~1"=="" set PORT=%~1
if not exist "%~dp0dist\wwwroot" (
  echo web\dist not found - run build.cmd first
  exit /b 1
)
powershell -NoProfile -ExecutionPolicy Bypass -File "%~dp0serve.ps1" -Port %PORT% %2
