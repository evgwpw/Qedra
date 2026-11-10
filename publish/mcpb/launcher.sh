#!/bin/sh
# Выбор двоичного файла Qedra по платформе и архитектуре (macOS x64/arm64, Linux x64).
dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
case "$(uname -s)-$(uname -m)" in
  Darwin-arm64) exec "$dir/osx-arm64/qedra" "$@" ;;
  Darwin-*)     exec "$dir/osx-x64/qedra" "$@" ;;
  *)            exec "$dir/linux-x64/qedra" "$@" ;;
esac
