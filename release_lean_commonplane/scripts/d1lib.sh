#!/bin/bash
# d1lib.sh: native code for the D1 check of NPT.CP3 (the active blocks), for builds and audits.
#
#   d1lib.sh build ROOT OUT
#       Inputs : ROOT/NPT/CP3/D1Core.lean, ROOT/NPT/CP3/Data/Types.lean (sources; D1Core imports only Data.Types).
#       Outputs: ROOT/.build/lib/NPT/CP3/D1Core.{olean,ilean} (same lean run as the C file), OUT/D1Core.c,
#                OUT/Types.c, OUT/D1Core.o, OUT/Types.o, OUT/libcp3d1.so, OUT/build.log.
#   d1lib.sh run ROOT SO MODULE
#       Compiles ROOT/<MODULE as path>.lean with --load-dynlib=SO into ROOT/.build/lib (the native_decide theorems
#       NPT.CP3.D1Nat.N<kk>); log on stdout.
#
# Environment: LEAN_TC = toolchain directory (default: `lean --print-prefix`); LEAN_PATH must contain ROOT/.build/lib
# (the imports' oleans, Data.Types built first) and the toolchain's lib/lean.
# Every step's exit status is checked; the script exits 1 at the first failure and prints the failing step.
set -u
TC=${LEAN_TC:-$(lean --print-prefix)}
CMD=${1:-}
fail() { echo "FAILED: $*"; exit 1; }
case "$CMD" in
  build)
    [ $# -eq 3 ] || fail "usage: d1lib.sh build ROOT OUT"
    ROOT=$(realpath "$2") || fail "ROOT"; OUT=$3
    mkdir -p "$OUT" "$ROOT/.build/lib/NPT/CP3" || fail "mkdir"
    OUT=$(realpath "$OUT") || fail "OUT"
    [ -f "$ROOT/NPT/CP3/D1Core.lean" ] || fail "missing $ROOT/NPT/CP3/D1Core.lean"
    [ -f "$ROOT/NPT/CP3/Data/Types.lean" ] || fail "missing $ROOT/NPT/CP3/Data/Types.lean"
    LOG="$OUT/build.log"
    : > "$LOG" || fail "log"
    {
      echo "sha256 $(sha256sum "$ROOT/NPT/CP3/D1Core.lean")"
      echo "sha256 $(sha256sum "$ROOT/NPT/CP3/Data/Types.lean")"
      echo "lean $("$TC/bin/lean" --version)"
    } >> "$LOG"
    cd "$ROOT" || fail "cd ROOT"
    "$TC/bin/lean" -DElab.async=false --root="$ROOT" -o .build/lib/NPT/CP3/D1Core.olean \
      -i .build/lib/NPT/CP3/D1Core.ilean -c "$OUT/D1Core.c" NPT/CP3/D1Core.lean >> "$LOG" 2>&1 \
      || fail "lean D1Core (see $LOG)"
    "$TC/bin/lean" -DElab.async=false --root="$ROOT" -c "$OUT/Types.c" NPT/CP3/Data/Types.lean >> "$LOG" 2>&1 \
      || fail "lean Data.Types (see $LOG)"
    "$TC/bin/leanc" -c -fPIC -O3 -DLEAN_EXPORTING -o "$OUT/D1Core.o" "$OUT/D1Core.c" >> "$LOG" 2>&1 \
      || fail "leanc D1Core.o (see $LOG)"
    "$TC/bin/leanc" -c -fPIC -O3 -DLEAN_EXPORTING -o "$OUT/Types.o" "$OUT/Types.c" >> "$LOG" 2>&1 \
      || fail "leanc Types.o (see $LOG)"
    "$TC/bin/leanc" -shared -o "$OUT/libcp3d1.so" "$OUT/D1Core.o" "$OUT/Types.o" -L"$TC/lib/lean" \
      -lInit_shared -lleanshared >> "$LOG" 2>&1 || fail "link libcp3d1.so (see $LOG)"
    n=$(nm -D --defined-only "$OUT/libcp3d1.so" | wc -l)
    [ "$n" -gt 0 ] || fail "libcp3d1.so exports no symbols"
    echo "exported symbols: $n" >> "$LOG"
    echo "sha256 $(sha256sum "$OUT/libcp3d1.so")" >> "$LOG"
    echo "build ok: $OUT/libcp3d1.so ($n symbols)" ;;
  run)
    [ $# -eq 4 ] || fail "usage: d1lib.sh run ROOT SO MODULE"
    ROOT=$(realpath "$2") || fail "ROOT"; SO=$(realpath "$3") || fail "SO"; M=$4
    case "$M" in NPT.CP3.*) ;; *) fail "module $M is not NPT.CP3.*";; esac
    f="${M//.//}.lean"; o=".build/lib/${M//.//}"
    cd "$ROOT" || fail "cd ROOT"
    [ -f "$f" ] || fail "missing $ROOT/$f"
    mkdir -p "$(dirname "$o")" || fail "mkdir"
    "$TC/bin/lean" -DElab.async=false --load-dynlib="$SO" --root="$ROOT" -o "$o.olean" -i "$o.ilean" "$f" \
      || fail "lean $M"
    echo "run ok: $M" ;;
  *) fail "usage: d1lib.sh build ROOT OUT | run ROOT SO MODULE" ;;
esac
