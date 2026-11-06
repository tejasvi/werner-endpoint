#!/bin/bash
# Re-verifies the certificates of this package.
#   ./run_all.sh               the light rows R1-R8 (about 15 min on one core, at most about 8 GB of memory)
#   ./run_all.sh R3 H2         only the rows named; the heavy rows H1-H6 (10 min to 45 min each) run only when named
#   ./run_all.sh list          print the commands of the heavy rows without running them
#   DRY=1 ./run_all.sh [ROW]   print the commands of the selected rows without running them
# Environment: PYTHON (default python3), OUT (output directory, default <package>_out next to the package directory;
# it must lie outside the package).  Logs go to $OUT/logs; README.md lists what every row checks.
set -u -o pipefail
PKG=$(cd "$(dirname "$0")" && pwd)
OUT=${OUT:-${PKG}_out}
[ "${1:-}" = list ] && DRY=1
if [ -z "${DRY:-}" ]; then
    mkdir -p "$OUT/logs" && OUT=$(cd "$OUT" && pwd) || exit 2
fi
case "$OUT/" in "$PKG"/*) echo "OUT=$OUT lies inside the package; choose another directory" >&2; exit 2 ;; esac
read -r -a PY <<< "${PYTHON:-python3}"
PY+=(-I -B)
W=("${PY[@]}" "$PKG/pkgrun.py")
export PKG_OUT=$OUT OMP_NUM_THREADS=${OMP_NUM_THREADS:-1} OPENBLAS_NUM_THREADS=${OPENBLAS_NUM_THREADS:-1} MKL_NUM_THREADS=${MKL_NUM_THREADS:-1}
C3=$PKG/certificates/d3
CA=$PKG/certificates/alld
IW=$OUT/independent_check/alld/work
[ -n "${DRY:-}" ] || mkdir -p "$IW" "$OUT/independent_check/work" "$OUT/independent_check/alld/logs"
fails=0

run() {  # run LOG CMD ...: run CMD in the package directory with its output in $OUT/logs/LOG
    local name=$1 log=$OUT/logs/$1 t0=$SECONDS rc
    shift
    if [ -n "${DRY:-}" ]; then
        printf '(cd %q && %s) > %q 2>&1\n' "$PKG" "$(printf '%q ' "$@")" "$log"
        return 0
    fi
    (cd "$PKG" && "$@") > "$log" 2>&1
    rc=$?
    echo "      $(( SECONDS - t0 )) s, exit $rc: logs/$name"
    return $rc
}

check() {  # check LABEL LOG REGEX [COUNT]: at least COUNT (default 1) lines of the log match REGEX
    [ -n "${DRY:-}" ] && return 0
    local n
    # the pattern goes through the environment: awk -v would strip the backslash escapes of the ERE
    n=$(RE="$3" awk '$0 ~ ENVIRON["RE"] { n++ } END { print n + 0 }' "$OUT/logs/$2")
    if [ "$n" -ge "${4:-1}" ]; then
        echo "PASS  $1"
    else
        echo "FAIL  $1: $n of ${4:-1} lines matching /$3/ in logs/$2"
        fails=$((fails + 1))
    fi
}

absent() {  # absent LABEL LOG REGEX: no line of the log matches REGEX
    [ -n "${DRY:-}" ] && return 0
    if RE="$3" awk '$0 ~ ENVIRON["RE"] { f = 1 } END { exit !f }' "$OUT/logs/$2"; then
        echo "FAIL  $1: logs/$2 has lines matching /$3/"
        fails=$((fails + 1))
    fi
}

WPRIMES="1048573 1048571 1048559 1048549 1048517 1048507 1048447 1048433 1048423 1048391 1048387 1048367"
EPRIMES="1048573 1048571 1048559 1048549 1048517"

row() {
    case "$1" in
    R1) echo "R1  d = 3 certificate, producer checker (13 s)"
        run R1_xverify_d3.log "${PY[@]}" verifiers/xverify.py "$C3/data_k4d3_min.pkl" "$C3/cert_k4d3_min.pkl"
        check "R1 d = 3: identity exact, 302 blocks PD" R1_xverify_d3.log '^VERIFIED$' ;;
    R2) echo "R2  d = 3 certificate, independent checker (20 s)"
        run R2a_aud_local.log "${W[@]}" independent_check/aud_local.py
        run R2b_cert_check.log "${W[@]}" independent_check/cert_check.py
        check "R2 d = 3 (independent): identity and PSD" R2b_cert_check.log 'CERT_CHECK IDENTITY_OK PSD_OK' ;;
    R3) echo "R3  limit certificate s = 0, producer checker (15 s)"
        run R3_xverify_inf.log "${PY[@]}" verifiers/xverify.py "$CA/xk4dinf_s2.pkl" "$CA/xcert4inf.pkl"
        check "R3 s = 0: identity exact, 514 blocks PD" R3_xverify_inf.log '^VERIFIED$' ;;
    R4) echo "R4  limit certificate s = 0, independent checker (30 s)"
        run R4_cert_check2_inf.log "${W[@]}" independent_check/alld/cert_check2.py "$CA/xk4dinf_s2.pkl" "$CA/xcert4inf.pkl"
        check "R4 s = 0 (independent): identity and PSD" R4_cert_check2_inf.log 'CERT_CHECK IDENTITY_OK PSD_OK' ;;
    R5) echo "R5  Lemma-5.3 bounds, independent (own scaling, inverse and left-kernel basis; about 5 min, 8 GB)"
        run R5a_local4.log "${W[@]}" independent_check/alld/local4.py
        run R5b_limitcons.log "${W[@]}" independent_check/alld/limitcons.py
        run R5c_bounds_A0.log "${W[@]}" independent_check/alld/bounds_A.py 0 "$IW/bA_0.pkl"
        run R5d_bounds_A14.log "${W[@]}" independent_check/alld/bounds_A.py 1-4 "$IW/bA_1_4.pkl"
        run R5e_bounds_A58.log "${W[@]}" independent_check/alld/bounds_A.py 5-8 "$IW/bA_5_8.pkl"
        run R5f_bounds_B.log "${W[@]}" independent_check/alld/bounds_B.py "$IW/bA_0.pkl" "$IW/bB.pkl"
        run R5g_bounds_C72.log "${W[@]}" independent_check/alld/bounds_C.py 72
        check "R5 limit data = s^0 coefficients of the polynomial data" R5b_limitcons.log 'equal to the s\^0 coefficient: True' 4
        absent "R5 limit data consistency" R5b_limitcons.log ': False'
        check "R5 every Lemma-5.3 condition at s0 = 2^-72" R5g_bounds_C72.log 'BOUNDS_RESULT s0 = 2\^-72: PASS' ;;
    R6) echo "R6  left-kernel certificate, independent exact part (30 s, 8 GB)"
        run R6_wcheck_exact.log "${W[@]}" independent_check/alld/wcheck.py exact
        check "R6 w(s).c(s) = 0 for all 119 vectors (exact)" R6_wcheck_exact.log 'copy-major rows: columns w with w\(s\)\.c\(s\) not identically 0: 0 of 119'
        check "R6 rank W(0) = 119" R6_wcheck_exact.log 'rank W\(0\) = 119 \(q = 119\)' ;;
    R7) echo "R7  the uniform certificate x(s) at d = 2^80, producer checker on data evaluated from the polynomials (about 5 min)"
        run R7a_xpolyeval.log "${PY[@]}" verifiers/xpolyeval.py "$CA/xpoly4.pkl" 1208925819614629174706176 "$OUT/data_d2e80.pkl" "$CA/xk4dinf_s2.pkl"
        run R7b_xverify_2e80.log "${PY[@]}" verifiers/xverify.py "$OUT/data_d2e80.pkl" "$CA/xs4e80.pkl"
        check "R7 d = 2^80: identity exact, 514 blocks PD" R7b_xverify_2e80.log '^VERIFIED$' ;;
    R8) echo "R8  mutations must fail (independent checker; about 1 min)"
        for m in mutY mutdY mutlam; do run R8_cert_check_$m.log "${W[@]}" independent_check/cert_check.py $m; done
        run R8_cert_check2_mutlam.log "${W[@]}" independent_check/alld/cert_check2.py "$CA/xk4dinf_s2.pkl" "$CA/xcert4inf.pkl" mutlam
        for m in mutY mutdY mutlam; do check "R8 d = 3 mutation $m rejected" R8_cert_check_$m.log 'CERT_CHECK IDENTITY_FAIL|PSD_FAIL'; done
        check "R8 s = 0 mutation rejected" R8_cert_check2_mutlam.log 'CERT_CHECK IDENTITY_FAIL' ;;
    H1) echo "H1  left-kernel certificate, producer checker (about 45 min, 8 GB)"
        run H1_xlkverify2.log "${PY[@]}" verifiers/xlkverify2.py "$CA/xpoly4.pkl" "$CA/xred4inf.pkl" "$CA/xlk4.pkl"
        check "H1 W(s)^T A(s) = 0, w(s).c(s) = 0, rank W(0) = 119 (exact)" H1_xlkverify2.log 'LEFT-KERNEL CERTIFICATE VERIFIED' ;;
    H2) echo "H2  Lemma-5.3 bounds, producer checker (about 10 min, 8 GB)"
        run H2_xbounds2.log "${PY[@]}" verifiers/xbounds2.py "$CA/xpoly4.pkl" "$CA/xcert4inf.pkl" "$CA/xlk4.pkl"
        check "H2 every condition on (0, 2^-72], exact rationals" H2_xbounds2.log 'RESULT \(exact\): every condition holds for s in \(0, 2\^-72\]' ;;
    H3) echo "H3  left-kernel certificate, independent modular part: 12 primes (about 3 min each) and the product test"
        for p in $WPRIMES; do run H3_wcheck_modp_$p.log "${W[@]}" independent_check/alld/wcheck.py modp $p
            [ -n "${DRY:-}" ] || cp "$OUT/logs/H3_wcheck_modp_$p.log" "$OUT/independent_check/alld/logs/wcheck_modp_$p.log"; done
        run H3_wprod.log "${W[@]}" independent_check/alld/wprod.py
        for p in $WPRIMES; do check "H3 prime $p: zero residues" H3_wcheck_modp_$p.log "prime $p: \\(a\\) nonzero residues 0, \\(b\\) nonzero residues 0"; done
        check "H3 product of the primes exceeds the bound: W(s)^T A(s) = 0 exactly" H3_wprod.log '-> EXACT$' ;;
    H4) echo "H4  d = 2^80, independent data evaluation and checker (about 10 min)"
        run H4a_spot_data.log "${W[@]}" independent_check/alld/spot_data.py 1208925819614629174706176 "$IW/data_d2e80.pkl" "$CA/xs4e80.pkl"
        run H4b_cert_check2_2e80.log "${W[@]}" independent_check/alld/cert_check2.py "$IW/data_d2e80.pkl" "$CA/xs4e80.pkl"
        check "H4 d = 2^80 (independent): identity and PSD" H4b_cert_check2_2e80.log 'CERT_CHECK IDENTITY_OK PSD_OK' ;;
    H5) echo "H5  d = 3 data rebuilt by the independent engine (15 runs of about 2.5 min) and compared with the shipped data"
        run H5a_aud_local.log "${W[@]}" independent_check/aud_local.py
        for p in $EPRIMES; do for c in 0 1 2; do run H5_engine_${p}_$c.log "${W[@]}" independent_check/modp_engine.py $p $c 3 "$OUT/independent_check/work/eng_p${p}_c$c.pkl"; done; done
        run H5b_compare_d2.log "${W[@]}" independent_check/compare_d2.py $EPRIMES
        run H5c_compare_d3.log "${W[@]}" independent_check/compare_d3.py 1048573 1048571 1048559 1048549
        check "H5 cut-() blocks, objective and E rows equal (exact)" H5b_compare_d2.log 'P = 2\^100 vs need 2\^96 -> EXACT'
        check "H5 cut-(3,) blocks equal (exact)" H5c_compare_d3.log 'EXACT EQUALITY PROVED' ;;
    H6) echo "H6  structure checks with the independent operators: d = 3 (about 1.5 min) and all-d (about 7 min)"
        run H6a_aud_local.log "${W[@]}" independent_check/aud_local.py
        run H6b_theta_checks.log "${W[@]}" independent_check/theta_checks.py
        run H6c_local4.log "${W[@]}" independent_check/alld/local4.py
        run H6d_theta_checks4.log "${W[@]}" independent_check/alld/theta_checks4.py 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20
        run H6e_theta_checks4_inf.log "${W[@]}" independent_check/alld/theta_checks4.py inf 14 16 20
        check "H6 d = 3 checks done" H6b_theta_checks.log '\] done$'
        absent "H6 d = 3 no mismatch" H6b_theta_checks.log ' [1-9][0-9]* mismatches'
        absent "H6 all-d no difference" H6d_theta_checks4.log ' [1-9][0-9]* of [0-9]+ coordinates differ'
        absent "H6 all-d (inf) no difference" H6e_theta_checks4_inf.log ' [1-9][0-9]* of [0-9]+ coordinates differ' ;;
    *) echo "unknown row $1" >&2; return 2 ;;
    esac
}

LIGHT="R1 R2 R3 R4 R5 R6 R7 R8"
HEAVY="H1 H2 H3 H4 H5 H6"
if [ "${1:-}" = list ]; then
    for r in $HEAVY; do DRY=1 row "$r"; done
    exit 0
fi
rows=${*:-$LIGHT}
for r in $rows; do row "$r" || true; done
[ -n "${DRY:-}" ] && exit 0
echo "failures: $fails"
exit $(( fails > 0 ))
