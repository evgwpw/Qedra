@echo off
setlocal enabledelayedexpansion
rem Build the Qedra NuGet package (.NET tool); ordinary build and tests are unchanged.

set "HERE=%~dp0"
set "ROOT=%HERE%.."
set "OUT=%HERE%out"
set "PROJ=%ROOT%\src\Lisp.Host\Lisp.Host.fsproj"

set "VERSION="
for /f "usebackq delims=" %%v in (`dotnet msbuild "%PROJ%" -getProperty:Version -nologo`) do set "VERSION=%%v"
if "%VERSION%"=="" (
  echo build-nuget: cannot read Version from Directory.Build.props
  exit /b 1
)

if not exist "%OUT%" mkdir "%OUT%"
dotnet pack "%PROJ%" -c Release -p:PackQedra=true -o "%OUT%" -nologo
if errorlevel 1 exit /b 1

set "PKG=%OUT%\Qedra.%VERSION%.nupkg"
if not exist "%PKG%" (
  echo build-nuget: package was not created: %PKG%
  exit /b 1
)
echo package: %PKG%
for %%a in ("%PKG%") do echo size: %%~za bytes

rem содержимое: инструмент и Lisp-библиотека
tar -tf "%PKG%" | findstr /i "tools/ lib/ qedra Lisp" | findstr /n "^"
