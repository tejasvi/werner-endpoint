#!/usr/bin/env bash
# build_sequential.sh [MODULE ...]: memory-safe build of this package, one module at a time (see README_commonplane.md).
#
#   ./build_sequential.sh                    every module of build_order.txt, then the axioms of the main theorems
#   ./build_sequential.sh NPT.CP3.Final      only the given modules and their imports (needs python3)
#
# Fetches the prebuilt Mathlib (`lake exe cache get`, needs network access), then compiles one module at a time with
# `lean`, in topological import order (imports first), into .build/lib: the procedure of the final audit, without its
# parallelism. Native code: NPT.CP3.D1Core is compiled together with its C code and linked into native1/libcp3d1.so
# (scripts/d1lib.sh); after NPT.CP3.D3Fast, scripts/d3lib.sh links native/libcp3d3.so from the C code of NPT.CP3.D3Fast,
# NPT.CP3.D1Core and NPT.CP3.Data.Types; the 64 modules NPT.CP3.D1Nat.N<kk> and NPT.CP3.Chk.D3N, whose `native_decide`
# checks run that code, are compiled with `--load-dynlib`.
set -euo pipefail
cd "$(dirname "$0")"
lake exe cache get
TC=$(lean --print-prefix)
export LEAN_PATH="$PWD/.build/lib:$(lake env printenv LEAN_PATH)"
export LEAN_TC="$TC" TC="$TC" LIBDIR="$PWD/.build/lib"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-4}"
mkdir -p .build/lib
if [ $# -gt 0 ]; then
  order=$(python3 scripts/topo_order.py . "$@")
else
  order=$(cat build_order.txt)
fi
n=$(printf '%s\n' "$order" | wc -l)
i=0
t0=$(date +%s)
LF=(-DElab.async=false -DmaxHeartbeats=400000)
while IFS= read -r m; do
  i=$((i + 1))
  t=$(date +%s)
  f="${m//.//}.lean"; o=".build/lib/${m//.//}"
  mkdir -p "$(dirname "$o")"
  case "$m" in
    NPT.CP3.D1Core)
      bash scripts/d1lib.sh build "$PWD" "$PWD/native1" ;;
    NPT.CP3.D3Fast)
      "$TC/bin/lean" "${LF[@]}" -R . -o "$o.olean" -i "$o.ilean" "$f"
      bash scripts/d3lib.sh "$PWD" 16 ;;
    NPT.CP3.D1Nat.*)
      bash scripts/d1lib.sh run "$PWD" "$PWD/native1/libcp3d1.so" "$m" ;;
    NPT.CP3.Chk.D3N)
      "$TC/bin/lean" -DElab.async=false --load-dynlib="$PWD/native/libcp3d3.so" -R . -o "$o.olean" -i "$o.ilean" "$f" ;;
    *)
      "$TC/bin/lean" "${LF[@]}" -R . -o "$o.olean" -i "$o.ilean" "$f" ;;
  esac
  echo "[$i/$n] $m: $(( $(date +%s) - t )) s"
done <<< "$order"
echo "built $n modules in $(( $(date +%s) - t0 )) s"
if [ $# -eq 0 ]; then
  "$TC/bin/lean" NPT/CP3/Axioms.lean
fi
