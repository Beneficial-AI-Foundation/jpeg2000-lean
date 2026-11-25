#!/usr/bin/env bash
# Build the instrumented OpenJPEG decoder used by the differential tests
# (task 4.6a; dump format and usage in docs/differential.md).
#
# Usage: scripts/build-opj-instrumented.sh [--force]
#   --force   rebuild even if an up-to-date binary is installed
#
# Steps: download the OpenJPEG v2.5.3 source tarball (pinned commit) into a
# fresh temp dir, verify its SHA-256 (refuses on mismatch), extract, apply
# scripts/opj-instrument.patch with `patch -p1`, configure with cmake (Release,
# static, codec on, threads off for a deterministic dump order), build only
# opj_decompress and install it as
#   .lake/opj-instrumented/bin/opj_decompress_dump
# A stamp file (commit + patch hash) makes reruns a no-op. OpenJPEG is a
# test-only tool, not a dependency of the Lean libraries.
# Exits 0 with a message if cmake, a C compiler, curl/wget, patch or a SHA-256
# tool is missing.
set -euo pipefail

OPJ_TAG="v2.5.3"
OPJ_COMMIT="210a8a5690d0da66f02d49420d7176a21ef409dc"
OPJ_URL="https://github.com/uclouvain/openjpeg/archive/${OPJ_COMMIT}.tar.gz"
OPJ_SHA256="a7e669f502ad14d93f374a850113a2857447bfbfd389c8e278888053b0e3abcc"

force=0
while [ $# -gt 0 ]; do
  case "$1" in
    --force) force=1; shift ;;
    -h|--help) sed -n '2,18p' "$0"; exit 0 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

skip() { echo "build-opj-instrumented: $1; skipping"; exit 0; }

sha256() {
  if command -v sha256sum >/dev/null 2>&1; then
    sha256sum "$1" | cut -d ' ' -f 1
  else
    shasum -a 256 "$1" | cut -d ' ' -f 1
  fi
}

command -v cmake >/dev/null 2>&1 || skip "cmake not found"
cc_found=""
for c in "${CC:-}" cc gcc clang; do
  if [ -n "$c" ] && command -v "$c" >/dev/null 2>&1; then cc_found="$c"; break; fi
done
[ -n "$cc_found" ] || skip "no C compiler (cc, gcc, clang) found"
command -v patch >/dev/null 2>&1 || skip "patch not found"
command -v sha256sum >/dev/null 2>&1 || command -v shasum >/dev/null 2>&1 \
  || skip "neither sha256sum nor shasum found"
if command -v curl >/dev/null 2>&1; then
  fetch() { curl -fsSL -o "$2" "$1"; }
elif command -v wget >/dev/null 2>&1; then
  fetch() { wget -q -O "$2" "$1"; }
else
  skip "neither curl nor wget found"
fi

root="$(cd "$(dirname "$0")/.." && pwd)"
patch_file="$root/scripts/opj-instrument.patch"
dest="$root/.lake/opj-instrumented"
bin="$dest/bin/opj_decompress_dump"
stamp="$dest/stamp"
want_stamp="$OPJ_TAG $OPJ_COMMIT $OPJ_SHA256 patch=$(sha256 "$patch_file")"

if [ "$force" = 0 ] && [ -x "$bin" ] && [ -f "$stamp" ] \
   && [ "$(cat "$stamp")" = "$want_stamp" ]; then
  echo "build-opj-instrumented: up to date"
  echo "$bin"
  exit 0
fi

work="$(mktemp -d "${TMPDIR:-/tmp}/opj-instr.XXXXXX")"
trap 'rm -rf "$work"' EXIT
mkdir "$work/dl" "$work/src" "$work/build"

echo "build-opj-instrumented: downloading OpenJPEG $OPJ_TAG ($OPJ_COMMIT)"
fetch "$OPJ_URL" "$work/dl/openjpeg.tar.gz"
got="$(sha256 "$work/dl/openjpeg.tar.gz")"
if [ "$got" != "$OPJ_SHA256" ]; then
  echo "build-opj-instrumented: SHA-256 mismatch for $OPJ_URL" >&2
  echo "  expected $OPJ_SHA256" >&2
  echo "  got      $got" >&2
  exit 1
fi

tar -xzf "$work/dl/openjpeg.tar.gz" -C "$work/src"
srcdir="$work/src/openjpeg-$OPJ_COMMIT"
[ -f "$srcdir/CMakeLists.txt" ] || { echo "unexpected tarball layout" >&2; exit 1; }
patch -p1 -N --quiet -d "$srcdir" < "$patch_file"

jobs="$(getconf _NPROCESSORS_ONLN 2>/dev/null || echo 2)"
cmake -S "$srcdir" -B "$work/build" \
  -DCMAKE_C_COMPILER="$cc_found" \
  -DCMAKE_BUILD_TYPE=Release \
  -DBUILD_SHARED_LIBS=OFF -DBUILD_STATIC_LIBS=ON \
  -DBUILD_CODEC=ON -DBUILD_TESTING=OFF -DBUILD_DOC=OFF \
  -DOPJ_USE_THREAD=OFF >"$work/cmake.log" 2>&1 \
  || { cat "$work/cmake.log" >&2; echo "cmake configure failed" >&2; exit 1; }
cmake --build "$work/build" --target opj_decompress --parallel "$jobs" \
  >"$work/build.log" 2>&1 \
  || { tail -n 40 "$work/build.log" >&2; echo "build failed" >&2; exit 1; }

built="$work/build/bin/opj_decompress"
[ -x "$built" ] || { echo "opj_decompress not found after build" >&2; exit 1; }
mkdir -p "$dest/bin"
cp "$built" "$bin.tmp"
chmod 755 "$bin.tmp"
mv "$bin.tmp" "$bin"
printf '%s\n' "$want_stamp" > "$stamp"
echo "build-opj-instrumented: installed"
echo "$bin"
