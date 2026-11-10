#!/bin/sh
# WASM.2d: start the published app on http://localhost:8080/app/index.html
# Serves web/dist/wwwroot with Python 3 (python3 or python); pass another port as $1.
set -e
here=$(cd "$(dirname "$0")" && pwd)
port=${1:-8080}
if [ ! -d "$here/dist/wwwroot" ]; then
  echo "web/dist not found - run ./build.sh first"
  exit 1
fi
url="http://localhost:$port/app/index.html"
echo "Open $url"
( sleep 1
  if command -v xdg-open >/dev/null 2>&1; then xdg-open "$url" >/dev/null 2>&1 || true
  elif command -v open >/dev/null 2>&1; then open "$url" >/dev/null 2>&1 || true
  fi ) &
if command -v python3 >/dev/null 2>&1; then
  exec python3 -m http.server "$port" --directory "$here/dist/wwwroot"
elif command -v python >/dev/null 2>&1; then
  exec python -m http.server "$port" --directory "$here/dist/wwwroot"
else
  echo "Python 3 not found. Serve web/dist/wwwroot with any static server and open $url"
  exit 1
fi
