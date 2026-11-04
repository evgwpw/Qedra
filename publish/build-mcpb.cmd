@echo off
setlocal enabledelayedexpansion
rem Build the MCPB bundle (one self-contained .mcpb for all platforms).
rem Input: publish\out\qedra-<version>-<rid> produced by build-release.cmd.

set "HERE=%~dp0"
set "ROOT=%HERE%.."
set "OUT=%HERE%out"
set "PROJ=%ROOT%\src\Lisp.Host\Lisp.Host.fsproj"

set "VERSION="
for /f "usebackq delims=" %%v in (`dotnet msbuild "%PROJ%" -getProperty:Version -nologo`) do set "VERSION=%%v"
if "%VERSION%"=="" (
  echo build-mcpb: cannot read Version from Directory.Build.props
  exit /b 1
)

for %%f in (LICENSE README.en.md README.md THIRD-PARTY-NOTICES.md) do (
  if not exist "%ROOT%\%%f" (
    echo build-mcpb: missing %%f in the repository root
    exit /b 1
  )
)

set "STAGE=%OUT%\mcpb-%VERSION%"
if exist "%STAGE%" rmdir /s /q "%STAGE%"
mkdir "%STAGE%\bin"

for %%r in (linux-x64 osx-x64 osx-arm64 win-x64) do (
  set "SRC=%OUT%\qedra-%VERSION%-%%r"
  if not exist "!SRC!" (
    echo build-mcpb: missing !SRC! ^(run publish\build-release.cmd %%r first^)
    exit /b 1
  )
  mkdir "%STAGE%\bin\%%r"
  xcopy /e /i /q /y "!SRC!" "%STAGE%\bin\%%r" >nul
  del /q "%STAGE%\bin\%%r\*.pdb" 2>nul
  if /i "%%r"=="win-x64" (
    ren "%STAGE%\bin\%%r\Lisp.exe" qedra.exe
  ) else (
    ren "%STAGE%\bin\%%r\Lisp" qedra
  )
  if errorlevel 1 exit /b 1
)

copy /y "%HERE%mcpb\launcher.sh" "%STAGE%\bin\qedra" >nul
powershell -NoProfile -Command "$p='%STAGE%\manifest.json'; $t=[IO.File]::ReadAllText('%HERE%mcpb\manifest.json'); [IO.File]::WriteAllText($p, $t.Replace('{{VERSION}}','%VERSION%'), (New-Object Text.UTF8Encoding($false)))"
if errorlevel 1 exit /b 1
copy /y "%ROOT%\LICENSE" "%STAGE%\" >nul
copy /y "%ROOT%\README.md" "%STAGE%\" >nul
copy /y "%ROOT%\README.en.md" "%STAGE%\" >nul
copy /y "%ROOT%\THIRD-PARTY-NOTICES.md" "%STAGE%\" >nul

set "BUNDLE=%OUT%\qedra-%VERSION%.mcpb"
if exist "%BUNDLE%" del /q "%BUNDLE%"
call npx --yes @anthropic-ai/mcpb validate "%STAGE%"
if errorlevel 1 exit /b 1
call npx --yes @anthropic-ai/mcpb pack "%STAGE%" "%BUNDLE%"
if errorlevel 1 exit /b 1
echo bundle: %BUNDLE%
certutil -hashfile "%BUNDLE%" SHA256
