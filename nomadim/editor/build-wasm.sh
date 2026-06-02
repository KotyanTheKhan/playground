#!/usr/bin/env bash
# Build the libnomadim WebAssembly module via Emscripten.
# Requires emcc on PATH (provided by the mise emsdk tool — run via
# `mise run nomadim-editor-build`). Output: nomadim/editor/public/nomadim.{js,wasm}
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
SRC="$ROOT/nomadim"
BUILD="$ROOT/nomadim/build-wasm"
OUT="$ROOT/nomadim/editor/public"

mkdir -p "$OUT"
emcmake cmake -S "$SRC" -B "$BUILD" -DCMAKE_BUILD_TYPE=Release -DNOMADIM_WASM=ON
cmake --build "$BUILD" -j --target nomadim_wasm
cp "$BUILD/nomadim.js" "$BUILD/nomadim.wasm" "$OUT/"
echo "✅ wrote $OUT/nomadim.js + nomadim.wasm"
