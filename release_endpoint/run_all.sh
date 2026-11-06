#!/bin/bash
# Checks for "Equality cases and every-copy results for the Werner endpoint inequality": rows C1, C2 and C3 of its
# Table 2 (the steps that the proofs use) and the further checks C4 to C7.
# Usage: ./run_all.sh        (about six minutes on one core; step 5 takes most of it)
set -euo pipefail
cd "$(dirname "$0")"
PY=${PYTHON:-python3}
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1
mkdir -p logs
echo "== 0. checksums"; sha256sum -c SHA256SUMS --quiet && echo "SHA256SUMS OK"
echo "== 1. C1: Theorem 4.7, the five identities of Steps 3 and 4 (symbolic) and numerical checks of its proof"
$PY -I code/check_sec10.py | tee logs/check_sec10.log
echo "== 2. C2: condition (G2) of Definition B.1 is nonempty (exact, Gaussian rationals); used in the proof of Theorem 5.1"
$PY -I code/fact_b_exact.py | tee logs/fact_b_exact.log
echo "== 3. C3: Theorem 7.2, the elementary inequalities of its proof (symbolic) and numerical checks"
$PY -I code/sd_check.py | tee logs/sd_check.log
echo "== 4. C4: Theorem 3.2, the Sym^2 computation (symbolic) and numerical checks at two-copy zeros"
$PY -I code/z2_check.py | tee logs/z2_check.log
echo "== 5. C5: Lemma B.8 for up to nine copies (exact ranks over a finite field; not used in the proofs)"
$PY -I code/fact_a_generic.py 9 0 | tee logs/fact_a_generic.log
echo "== 6. C6: Corollary 3.4, numerical illustration"
$PY -I code/d4_check.py | tee logs/d4_check.log
echo "== 7. C7: Conjecture 7.1, a small numerical instance (k = 3, d = 3)"
$PY -I code/qep_check.py | tee logs/qep_check.log
echo "== verdict"
fail=0
need() { if ! grep -q -F -- "$2" "logs/$1"; then echo "MISSING in $1: $2"; fail=1; fi; }
need check_sec10.log    "OK (I) per-copy minimum (dagger 1)"
need check_sec10.log    "OK (II) merge identity (dagger 2)"
need check_sec10.log    "OK (III) eigenvalues"
need check_sec10.log    "OK (IV) kappa_ij"
need check_sec10.log    "OK (V) one-copy sum of squares (dagger 5)"
need check_sec10.log    "OK Part B (all minima >= -1e-9)"
need fact_b_exact.log   "FACT C2 (G2 nonempty, both copies transverse): PASS"
need sd_check.log       "CHECK C3 (Theorem 7.2): PASS"
need z2_check.log       "CHECK C4 (Theorem 3.2): PASS"
need fact_a_generic.log "FACT C5 (good vectors exist for j = 1..9): PASS"
need d4_check.log       "CHECK C6 (Corollary 3.4): PASS"
need qep_check.log      "CHECK C7 (Conjecture 7.1, numerical instance k = 3, d = 3): PASS"
if [ "$fail" = 0 ]; then echo "ALL CHECKS PASSED"; else echo "CHECKS FAILED"; exit 1; fi
