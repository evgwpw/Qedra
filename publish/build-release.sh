#!/bin/sh
# Build self-contained Qedra release archives.
# Usage: publish/build-release.sh [rid ...]   (default: win-x64 linux-x64 osx-x64 osx-arm64)
# Archive names: qedra-<version>-<rid>.zip for Windows, .tar.gz for Linux and macOS.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)
out="$here/out"
proj="$root/src/Lisp.Host/Lisp.Host.fsproj"

# Version is written once, in Directory.Build.props; read it from the evaluated project
version=$(dotnet msbuild "$proj" -getProperty:Version -nologo | tr -d '\r' | tail -n 1)
if [ -z "$version" ]; then
  echo "build-release: cannot read <Version> from Directory.Build.props" >&2
  exit 1
fi

rids="$*"
if [ -z "$rids" ]; then rids="win-x64 linux-x64 osx-x64 osx-arm64"; fi

for f in LICENSE README.en.md README.md THIRD-PARTY-NOTICES.md; do
  if [ ! -f "$root/$f" ]; then
    echo "build-release: missing $f in the repository root" >&2
    exit 1
  fi
done

mkdir -p "$out"
for rid in $rids; do
  name="qedra-$version-$rid"
  stage="$out/$name"
  archive=""
  rm -rf "$stage"
  echo "== $rid"
  # Self-contained (no installed .NET needed), not single-file, no trimming.
  # No PDB: debug symbols carry build-machine paths into the archive.
  dotnet publish "$proj" -c Release -r "$rid" --self-contained true -o "$stage" -nologo \
    -p:DebugType=None -p:DebugSymbols=false
  rm -f "$stage"/*.pdb
  # The .NET apphost loads Lisp.dll by the name recorded inside it, so a copy runs the same app.
  if [ "$rid" = "win-x64" ]; then
    cp "$stage/Lisp.exe" "$stage/qedra.exe"
  else
    cp "$stage/Lisp" "$stage/qedra"
    chmod +x "$stage/qedra" "$stage/Lisp"
  fi
  cp "$root/LICENSE" "$root/README.en.md" "$root/README.md" "$root/THIRD-PARTY-NOTICES.md" "$stage/"
  case "$rid" in
    win-*)
      archive="$out/$name.zip"
      rm -f "$archive"
      (cd "$out" && zip -qr "$name.zip" "$name")
      ;;
    *)
      archive="$out/$name.tar.gz"
      rm -f "$archive"
      (cd "$out" && tar -czf "$name.tar.gz" "$name")
      ;;
  esac
  if [ ! -f "$archive" ]; then
    echo "build-release: archive was not created: $archive" >&2
    exit 1
  fi
  echo "  $archive"
done
echo "Archives in $out"
