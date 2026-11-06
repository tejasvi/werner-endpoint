#!/bin/bash
# d3lib.sh TREE CAPGB: native library for the D3 check of NPT.CP3 (objective and equality rows), built inside TREE.
# Inputs, all from TREE: the sources NPT/CP3/D3Fast.lean, NPT/CP3/D1Core.lean, NPT/CP3/Data/Types.lean, and the oleans of
# NPT.CP3.D1Core and NPT.CP3.Data.Types in LIBDIR ($LIBDIR if set, else the first existing of TREE/.lake/build/lib/lean,
# TREE/.lake/build/lib, TREE/.build/lib). Steps: lean -c (C only; no olean or ilean is written) for the three modules,
# leanc -c -fPIC -O3 objects, leanc -shared link with -lInit_shared -lleanshared.
# Outputs only under TREE/native (a real directory inside TREE; earlier outputs are renamed *.prev_<UTC stamp> first).
# Prints the toolchain, the source/olean mtimes and the sha256 of the inputs, the C files, the two toolchain libraries
# and the .so; ends with "LIB OK" (exit 0) or "LIB FAIL" (exit 1, or 2 before any step).
# Each step: prlimit --as=CAPGB, nice 10, oom_score_adj 1000, one thread. Toolchain $TC (default: `lean --print-prefix`).
# Then build NPT.CP3.Chk.D3N with --load-dynlib=TREE/native/libcp3d3.so.
set -u
[ $# -eq 2 ] || { echo "usage: d3lib.sh TREE CAPGB"; exit 2; }
TREE=$(realpath -e "$1") || { echo "LIB FAIL: no tree $1"; exit 2; }
CAP=$2
case "$CAP" in ''|*[!0-9]*) echo "LIB FAIL: CAPGB must be a whole number"; exit 2;; esac
TC=${TC:-$(lean --print-prefix)}
OUT=$TREE/native
SRCS="NPT/CP3/D3Fast.lean NPT/CP3/D1Core.lean NPT/CP3/Data/Types.lean"
for s in $SRCS; do [ -f "$TREE/$s" ] || { echo "LIB FAIL: missing source $TREE/$s"; exit 2; }; done
if [ -n "${LIBDIR:-}" ]; then LD=$LIBDIR
elif [ -d "$TREE/.lake/build/lib/lean" ]; then LD=$TREE/.lake/build/lib/lean
elif [ -d "$TREE/.lake/build/lib" ]; then LD=$TREE/.lake/build/lib
else LD=$TREE/.build/lib; fi
for o in NPT/CP3/D1Core.olean NPT/CP3/Data/Types.olean; do
  [ -f "$LD/$o" ] || { echo "LIB FAIL: missing $LD/$o (build NPT.CP3.D1Core and NPT.CP3.Data.Types first)"; exit 2; }
done
[ -L "$OUT" ] && { echo "LIB FAIL: $OUT is a symlink"; exit 2; }
mkdir -p "$OUT" || { echo "LIB FAIL: cannot create $OUT"; exit 2; }
[ "$(realpath -e "$OUT")" = "$TREE/native" ] || { echo "LIB FAIL: $OUT resolves outside $TREE"; exit 2; }
stamp=$(date -u +%Y%m%dT%H%M%SZ)
for f in Types.c D1Core.c D3Fast.c Types.o D1Core.o D3Fast.o libcp3d3.so; do
  [ -L "$OUT/$f" ] && { echo "LIB FAIL: $OUT/$f is a symlink"; exit 2; }
  if [ -e "$OUT/$f" ]; then mv -n "$OUT/$f" "$OUT/$f.prev_$stamp" && [ ! -e "$OUT/$f" ] || { echo "LIB FAIL: cannot move $OUT/$f aside"; exit 2; }; fi
done
export LEAN_PATH="$LD:$TC/lib/lean" LEAN_NUM_THREADS=1 OMP_NUM_THREADS=1
cd "$TREE" || exit 2
TIMER=""; [ -x /usr/bin/time ] && TIMER="/usr/bin/time -f   %e_s,_%M_KB"
G="prlimit --as=$((CAP*1024*1024*1024)) -- nice -n 10 $TIMER"
step() { echo "== $*" | cut -c1-220; bash -c 'echo 1000 > /proc/self/oom_score_adj; exec "$@"' _ $G "$@"; r=$?; echo "rc=$r"; [ "$r" -eq 0 ] || { echo "LIB FAIL"; exit 1; }; }
step "$TC/bin/lean" -DElab.async=false -R . -c "$OUT/Types.c" NPT/CP3/Data/Types.lean
step "$TC/bin/lean" -DElab.async=false -R . -c "$OUT/D1Core.c" NPT/CP3/D1Core.lean
step "$TC/bin/lean" -DElab.async=false -R . -c "$OUT/D3Fast.c" NPT/CP3/D3Fast.lean
for m in D3Fast Types D1Core; do step "$TC/bin/leanc" -c -fPIC -O3 -DLEAN_EXPORTING -o "$OUT/$m.o" "$OUT/$m.c"; done
step "$TC/bin/leanc" -shared -o "$OUT/libcp3d3.so" "$OUT/D3Fast.o" "$OUT/Types.o" "$OUT/D1Core.o" -L"$TC/lib/lean" -lInit_shared -lleanshared
echo "-- toolchain: $("$TC/bin/lean" --version)"
echo "-- olean dir $LD; mtimes (source, olean):"
stat -L -c '%y %n' NPT/CP3/D1Core.lean "$LD/NPT/CP3/D1Core.olean" NPT/CP3/Data/Types.lean "$LD/NPT/CP3/Data/Types.olean"
echo "-- sha256:"
sha256sum $SRCS "$OUT/D3Fast.c" "$OUT/D1Core.c" "$OUT/Types.c" "$TC/lib/lean/libInit_shared.so" "$TC/lib/lean/libleanshared.so" "$OUT/libcp3d3.so"
echo "LIB OK"
