#!/bin/sh
# Сборка NuGet-пакета Qedra (.NET tool). Сборку и тесты lisp2 не меняет: свойства — только при PackQedra=true.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)
out="$here/out"
proj="$root/src/Lisp.Host/Lisp.Host.fsproj"

version=$(dotnet msbuild "$proj" -getProperty:Version -nologo | tr -d '\r' | tail -n 1)
if [ -z "$version" ]; then
  echo "build-nuget: cannot read <Version> from Directory.Build.props" >&2
  exit 1
fi

mkdir -p "$out"
dotnet pack "$proj" -c Release -p:PackQedra=true -o "$out" -nologo

pkg="$out/Qedra.$version.nupkg"
if [ ! -f "$pkg" ]; then
  echo "build-nuget: package was not created: $pkg" >&2
  exit 1
fi
echo "package: $pkg"
ls -l "$pkg"
if command -v unzip >/dev/null 2>&1; then
  unzip -l "$pkg" | grep -E 'tools/.*/(qedra|Lisp)|tools/.*/lib/' | head -n 20 || true
fi
