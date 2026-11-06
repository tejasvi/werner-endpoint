# Certificates: four copies, common-plane sector, every dimension

**Claim.** Let d ≥ 2 and let C be an operator on (C^d)^⊗4 whose range and co-range lie in one 2-dimensional subspace
(the common-plane sector; it contains the normal, the Hermitian and the PSD operators of rank two). Then

  q_4(1/2, C) = Σ_{J ⊆ {1,2,3,4}} (−1/2)^{|J|} ‖Tr_J C‖² ≥ 0.

This package contains the certificates of the proof and two independent implementations of their checks. The
producer's verifiers are in `verifiers/`. The independent checker in `independent_check/` was written separately,
from the problem definition, and builds its own operators, partial transposes, objective and Stiefel maps. In
Table 2 of the accompanying paper these are rows D1 (all-d certificate), D2 (d = 3) and D3 (independent check).

## Logical chain

Lemma 2.3(a) refers to the paper that this record accompanies; Lemmas 5.1 and 5.3 to the companion paper,
doi:10.5281/zenodo.23718035 (version 4).

1. **Relaxation.** For each d, q_4(1/2, ·) on the sector is bounded below by the optimum of a quartic moment
   relaxation on the normal slice. Its PSD blocks are the cut-() blocks and the cut-(3,) blocks on the support S2.
   A dual certificate is an exact identity c = E^T λ + Σ_b F_b^*(N_b Y_b N_b^T) with every Y_b positive definite.
   Because q(H + iK) = q(H) + q(K), one certificate covering every angle θ covers the whole sector.
2. **d = 3.** An exact certificate is given (`certificates/d3`). Rows R1, R2.
3. **Polynomial data.** For d ≥ 4 the data have a fixed structure. With s = 1/d they are polynomials:
   - F̂_b(s) = d^−deg_b F_b(d), with deg_b = 2F_t (F_t = the number of contracted sites of the label);
   - Ê_r(s) = d^−4 E_r(d);
   - an objective c(s) of degree 16 in s.

   `certificates/alld/xpoly4.pkl` stores all coefficients as exact integers. The module bases are J(d) = D(d)C
   with a fixed C, and Lemma 5.1 (loop counting) gives the degree bounds. The coefficients of the blocks and equality
   rows were interpolated exactly from exact data at d = 4…13, and those of the objective from its exact values at
   d = 4…20; every coefficient above its degree vanishes. The independent checker rebuilt the data at the limit and at
   eight more dimensions (d = 14, 20, 22, …, 32) and found them equal, the equality rows up to scalar factors (row H5
   has the d = 3 analogue; the all-d rebuild needs a 64-core machine).
4. **Limit certificate.** `xcert4inf.pkl` is an exact certificate of the s = 0 data (`xk4dinf_s2.pkl`, the s^0
   coefficients; checked in R5). The row and column sets R and S of size 4,780 are fixed (`sel_info`, `rows`), and
   A_RS(0) is invertible. Rows R3, R4.
5. **Rational dual.** For s > 0 put x(s) = x0 + δ(s), with δ_S = A_RS(s)^−1 r_R(s), r(s) = c(s) − A(s)x0, and δ = 0
   off S. By Cramer's rule x(s) is rational in d.
6. **Consistency.** `xlk4.pkl` holds 119 polynomial vectors W(s) of degree 8. They satisfy W(s)^T A(s) ≡ 0 and
   W(s)·c(s) ≡ 0, and W(0) has rank 119 = 4,899 − 4,780. While W(s) keeps rank 119, A(s) has rank 4,780, so x(s)
   satisfies all equations. Rows R6, H1, H3.
7. **Bounds** (Lemma 5.3). Every bound is a polynomial in s with nonnegative coefficients. At s0 = 2^−72 they show,
   in exact rationals, three things for every s ∈ (0, s0]:
   - A_RS(s) is invertible (Neumann series);
   - every Y_b(s) stays positive definite (Weyl);
   - W(s) keeps rank 119.

   So every d ≥ 2^72 has an exact certificate. Rows R5 (independent: own equilibration, own approximate inverse,
   own left-kernel basis) and H2 (producer).
8. **Embedding** (Lemma 2.3(a)). An isometry C^d → C^D keeps the common-plane property and the value of q_4.
   Hence the claim for D = 2^72 implies it for every d < 2^72.
9. **Cross-check.** `xs4e80.pkl` is x(s) built exactly at d = 2^80. It passes the d-specific checker on data
   evaluated from the polynomials (R7) and on the independent checker's own evaluation (H4).

## Running the checks

Requirements: see `requirements.txt` (Python 3.13/3.14, numpy, scipy, sympy, python-flint 0.9.0). Then:

    PYTHON=python3.14 ./run_all.sh            # rows R1-R8, about 15 min on one core, peak about 8 GB
    PYTHON=python3.14 ./run_all.sh H2 H1      # heavy rows only when named
    ./run_all.sh list                              # commands of the heavy rows

Outputs go to `$OUT` (default `<package>_out`, outside the package). Each row prints PASS/FAIL lines, and
`run_all.sh` exits non-zero on any FAIL. The independent scripts run through `pkgrun.py`. In the shipped copies
every absolute path of the original tree is written `<ROOT>/REL`; the wrapper maps such paths onto this package
(reads) and onto `$OUT` (writes). Four paths in the independent checker name copies of the certificate files and
are read from `certificates/`. Times and peak memory below are approximate, for one core of a 2026 server.

| row | what is checked | script(s) | time, memory |
|---|---|---|---|
| R1 | d = 3: identity exact over 3 × 1331 entries; 302 blocks PD (exact LDL of Ŷ − τI and ‖dY‖_F < τ) | `verifiers/xverify.py` | 13 s, 1 GB |
| R2 | d = 3, independent: own local operators; identity and PSD | `independent_check/aud_local.py`, `cert_check.py` | 20 s, 1 GB |
| R3 | s = 0 certificate: identity over 3 × 1633 entries, 514 blocks PD | `verifiers/xverify.py` | 15 s, 1.2 GB |
| R4 | s = 0 certificate, independent | `independent_check/alld/cert_check2.py` | 30 s, 2 GB |
| R5 | limit data = s^0 coefficients; Lemma-5.3 inequalities at s0 = 2^−72 with independent equilibration, inverse and left-kernel basis | `alld/local4.py`, `limitcons.py`, `bounds_A.py` (×3), `bounds_B.py`, `bounds_C.py` | 5 min, 8 GB |
| R6 | w(s)·c(s) ≡ 0 for all 119 vectors, exact (the coordinate-major control fails as it should); rank W(0) = 119 | `alld/wcheck.py exact` | 30 s, 8 GB |
| R7 | x(s) at d = 2^80: identity exact, 514 blocks PD, on data evaluated from the polynomials | `verifiers/xpolyeval.py`, `xverify.py` | 5 min, 8 GB |
| R8 | mutated certificates are rejected (Ŷ, dY, λ at d = 3; λ at s = 0) | `cert_check.py`, `cert_check2.py` | 1 min |
| H1 | W(s)^T A(s) ≡ 0 on every equality row and every compressed block, order by order, exact; W·c ≡ 0; rank W(0) | `verifiers/xlkverify2.py` | 45 min, 8 GB |
| H2 | Lemma 5.3 in exact rationals: θ0 = ‖I − At_0X‖∞ = 7.0e−7 (exact residual), β ≈ 8.0e6, margins ≥ 4.39e−10, σ_q² = 0.542 after an exact orthogonalisation; holds on (0, 2^−72] | `verifiers/xbounds2.py` | 10 min, 8 GB |
| H3 | W(s)^T A(s) ≡ 0 modulo 12 primes at 17 points; the product of the primes exceeds twice the coefficient bound, so the identity is exact | `alld/wcheck.py modp P`, `wprod.py` | 12 × 3 min |
| H4 | d = 2^80 with the independent evaluation of the data | `alld/spot_data.py`, `cert_check2.py` | 10 min |
| H5 | d = 3 data rebuilt by the independent engine (5 primes) and equal to the shipped data (exact by a CRT bound) | `modp_engine.py`, `compare_d2.py`, `compare_d3.py` | 15 × 2.5 min |
| H6 | structure checks with the independent operators: objective, blocks and maps at d = 3 and d = 4…20, ∞ | `theta_checks.py`, `alld/theta_checks4.py` | 9 min |

Not scripted here (64-core machine, hours):
- the independent all-d data rebuild: `alld/engine4.py P d c n` per prime and dimension, then `alld/compare4.py`,
  `finalize4.py`, `finalize5.py`, and the mutation test `alld/mut_alld.py`, which needs the engine's outputs at ∞;
- the producer pipeline that made the certificates:
  - `verifiers/xbuild.py 4 s2:d chunk c n` at d = 4…13 (exact data by CRT);
  - `xpoly.py` and `xinterp.py` (polynomial and limit data);
  - `xlim.py` (max-margin solve at s = 0) and `xrat4.py` (rationalisation);
  - `xlkx2.py` (left kernel modulo primes, CRT and rational reconstruction);
  - `xsample.py` (x(s) at d = 2^e);
  - `xnodecheck.py` (polynomial data against a build at a non-node d; d = 15 passed).

The d = 3 certificate came from `xatd.py`, `xrat2.py` and the same builder.

## Files

- `certificates/d3/`: data (8,820 equality rows, 353 blocks, N = 1331), certificate, coordinates (bases J, W, S, V).
- `certificates/alld/`:
  - `xpoly4.pkl`: polynomial data, 574 blocks, all orders;
  - `xk4dinf_s2.pkl`: limit data;
  - `xcert4inf.pkl`: limit certificate with S and R;
  - `xred4inf.pkl`: face bases N_b of the 514 active blocks;
  - `xlk4.pkl`: W(s);
  - `xs4e80.pkl`: certificate at d = 2^80;
  - `struct_k4d4_s2.pkl`, `reduced_dual_k4d4_s2.pkl`: coordinates and reduced dual at d = 4.
- `verifiers/`: producer code (verifiers and pipeline; the scripts import each other from this directory).
- `independent_check/`: the independent checker. The d = 3 scripts are at the top, the all-d scripts in `alld/`.
- `expected/original/`: the logs of the original runs (the producer's all-d pipeline; the independent d = 3 and all-d
  checks), for comparison with the logs in `$OUT/logs`.
- `pkgrun.py`: the path wrapper. `run_all.sh`: the checks. `SHA256SUMS`: `sha256sum -c SHA256SUMS`.

All data files are pickles of Python ints, Fractions and numpy object arrays. The independent scripts read them
through a restricted unpickler (`independent_check/safeload.py`).

License: CC BY 4.0 (`LICENSE`).
