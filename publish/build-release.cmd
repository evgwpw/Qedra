@echo off
setlocal enabledelayedexpansion
rem Build self-contained Qedra release archives (default: win-x64).
rem Usage: publish\build-release.cmd [rid ...]
rem Archive names: qedra-<version>-<rid>.zip for Windows, .tar.gz for Linux and macOS.
rem Comments are ASCII: cmd reads this file in the OEM codepage.

set "HERE=%~dp0"
set "ROOT=%HERE%.."
set "OUT=%HERE%out"
set "PROJ=%ROOT%\src\Lisp.Host\Lisp.Host.fsproj"

rem Version is written once, in Directory.Build.props; read it from the evaluated project
set "VERSION="
for /f "usebackq delims=" %%v in (`dotnet msbuild "%PROJ%" -getProperty:Version -nologo`) do set "VERSION=%%v"
if "%VERSION%"=="" (
  echo build-release: cannot read Version from Directory.Build.props
  exit /b 1
)

set "RIDS=%*"
if "%RIDS%"=="" set "RIDS=win-x64"

for %%f in (LICENSE README.en.md README.md THIRD-PARTY-NOTICES.md) do (
  if not exist "%ROOT%\%%f" (
    echo build-release: missing %%f in the repository root
    exit /b 1
  )
)

if not exist "%OUT%" mkdir "%OUT%"

for %%r in (%RIDS%) do (
  set "NAME=qedra-%VERSION%-%%r"
  set "STAGE=%OUT%\!NAME!"
  if exist "!STAGE!" rmdir /s /q "!STAGE!"
  echo == %%r
  rem Self-contained (no installed .NET needed), not single-file, no trimming.
  rem No PDB: debug symbols carry build-machine paths into the archive.
  dotnet publish "%PROJ%" -c Release -r %%r --self-contained true -o "!STAGE!" -nologo -p:DebugType=None -p:DebugSymbols=false
  if errorlevel 1 exit /b 1
  del /q "!STAGE!\*.pdb" 2>nul
  rem The .NET apphost loads Lisp.dll by the name recorded inside it, so a copy runs the same app.
  if /i "%%r"=="win-x64" (
    copy /y "!STAGE!\Lisp.exe" "!STAGE!\qedra.exe" >nul
  ) else (
    copy /y "!STAGE!\Lisp" "!STAGE!\qedra" >nul
  )
  if errorlevel 1 exit /b 1
  copy /y "%ROOT%\LICENSE" "!STAGE!\" >nul
  copy /y "%ROOT%\README.md" "!STAGE!\" >nul
  copy /y "%ROOT%\README.en.md" "!STAGE!\" >nul
  copy /y "%ROOT%\THIRD-PARTY-NOTICES.md" "!STAGE!\" >nul
  if errorlevel 1 exit /b 1
  if /i "%%r"=="win-x64" (
    if exist "!OUT!\!NAME!.zip" del /q "!OUT!\!NAME!.zip"
    tar -a -c -f "!OUT!\!NAME!.zip" -C "!OUT!" "!NAME!"
  ) else (
    if exist "!OUT!\!NAME!.tar.gz" del /q "!OUT!\!NAME!.tar.gz"
    tar -czf "!OUT!\!NAME!.tar.gz" -C "!OUT!" "!NAME!"
  )
  if errorlevel 1 exit /b 1
  echo   done
)

echo Archives in %OUT%
