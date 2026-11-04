#!/bin/sh
# Сборка MCPB-бандла Qedra: один самодостаточный .mcpb на все платформы.
# Вход — готовые каталоги publish/out/qedra-<version>-<rid> из build-release.sh.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)
out="$here/out"
proj="$root/src/Lisp.Host/Lisp.Host.fsproj"

version=$(dotnet msbuild "$proj" -getProperty:Version -nologo | tr -d '\r' | tail -n 1)
if [ -z "$version" ]; then
  echo "build-mcpb: cannot read <Version> from Directory.Build.props" >&2
  exit 1
fi

for f in LICENSE README.en.md README.md THIRD-PARTY-NOTICES.md; do
  if [ ! -f "$root/$f" ]; then
    echo "build-mcpb: missing $f in the repository root" >&2
    exit 1
  fi
done

stage="$out/mcpb-$version"
rm -rf "$stage"
mkdir -p "$stage/bin"

for rid in linux-x64 osx-x64 osx-arm64 win-x64; do
  src="$out/qedra-$version-$rid"
  if [ ! -d "$src" ]; then
    echo "build-mcpb: missing $src (run publish/build-release.sh $rid first)" >&2
    exit 1
  fi
  mkdir -p "$stage/bin/$rid"
  cp -R "$src/." "$stage/bin/$rid/"
  rm -f "$stage/bin/$rid"/*.pdb
  if [ "$rid" = "win-x64" ]; then
    mv "$stage/bin/$rid/Lisp.exe" "$stage/bin/$rid/qedra.exe"
  else
    mv "$stage/bin/$rid/Lisp" "$stage/bin/$rid/qedra"
    chmod +x "$stage/bin/$rid/qedra"
  fi
done

cp "$here/mcpb/launcher.sh" "$stage/bin/qedra"
chmod +x "$stage/bin/qedra"
sed "s/{{VERSION}}/$version/" "$here/mcpb/manifest.json" > "$stage/manifest.json"
cp "$root/LICENSE" "$root/README.en.md" "$root/README.md" "$root/THIRD-PARTY-NOTICES.md" "$stage/"

bundle="$out/qedra-$version.mcpb"
rm -f "$bundle"
npx --yes @anthropic-ai/mcpb validate "$stage"
npx --yes @anthropic-ai/mcpb pack "$stage" "$bundle"
echo "bundle: $bundle"
if command -v sha256sum >/dev/null 2>&1; then
  sha256sum "$bundle"
else
  shasum -a 256 "$bundle"
fi
