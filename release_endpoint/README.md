# Equality cases and every-copy results for the Werner endpoint inequality: verification package

This package accompanies the paper *Equality cases and every-copy results for the Werner endpoint inequality*
(Zenodo, doi:10.5281/zenodo.23718037). It contains the computer-verified steps that the proofs use, rows C1, C2 and C3 of
the paper's Table 2, and four further checks that no proof uses, labelled C4–C7 here: a symbolic check of a hand
computation, an exact check of a lemma for up to nine copies, and two numerical illustrations. The larger numerical
searches quoted in the paper are not part of the package.

Notation as in the paper: q_k(t, C) = Σ_{J ⊆ {1,…,k}} (−t)^{|J|} ‖Tr_J C‖²_F for an operator C on (C^d)^{⊗k}. For a plane V,
m_k(V) is the minimum of q_k(1/2, C) over operators C with ‖C‖_F = 1 and co-range in V, and ν₃^(l)(V) is the third largest
eigenvalue of the reduced operator of the projector onto V on copy l.

## What is checked

| check | script | paper | kind | used in a proof |
|---|---|---|---|---|
| C1 | `code/check_sec10.py` | Theorem 4.7: the five identities marked (†) in Steps 3 and 4; numerical checks of Steps 1–4 | symbolic; floating point | the five identities |
| C2 | `code/fact_b_exact.py` | Theorem 5.1, Definition B.1, Lemma B.7 | exact (Gaussian rationals) | yes |
| C3 | `code/sd_check.py` | Theorem 7.2 and Appendix B.3 | symbolic; floating point | the step L′ > R_i′ of Appendix B.3 |
| C4 | `code/z2_check.py` | Theorem 3.2, sub-case dim E_s = 2; numerical checks at two-copy zeros | symbolic; floating point | no (the symbolic part repeats a hand computation) |
| C5 | `code/fact_a_generic.py` | Lemma B.8, for up to nine copies | exact (ranks modulo p = 10⁹ + 9) | no (independent check) |
| C6 | `code/d4_check.py` | Corollary 3.4 | floating point | no |
| C7 | `code/qep_check.py` | Conjecture 7.1, one instance (k = 3, d = 3) | floating point | no |

- **C1.** Verifies with sympy the five identities marked (†) in Steps 3 and 4 of the proof of Theorem 4.7, typed as
  displayed in the paper, and the eigenvalues of the quadratic part in Step 4. It then checks Steps 1–4 numerically for
  k = 2, …, 5, with random positive coefficients from a fixed seed: the operator identity for q_k and (B.5), the formula for
  A_10, the block structure of A_00, Lemma B.11 on one to six copies, the bound Ã_00 ≥ A̲_00, the scalar form of Step 3 and
  the chain down to G ≥ 0.
- **C2.** For the vector ψ₀ = (3−5i, −5−4i, −4−2i, −3−i, −4+i, 3, 4−3i, 1−4i) on two copies with two-dimensional local
  supports (order: first copy, second copy, Q), the second-order form of Lemma B.7 annihilates the tilts, has rank two, and
  is positive definite on their orthogonal complement, with either copy taken as the transverse copy. So condition (G2) is
  nonempty. The form is computed exactly from its formula and, independently, in floating point from the full operator
  E = D ⊗ D ⊗ id_Q on (C³)^{⊗2} ⊗ C².
- **C3.** Checks symbolically the identity c² − 8c + 8 = 0 at c = 4 − 2√2, the two slack expressions at m = 1/4, and the
  inequality L′ > R_i′ on (1/4, 2/(8 − c)) of Appendix B.3. In floating point it compares formula (B.3) with the full
  operator, tests the bound of Theorem 7.2 on random planes of the class for d = 3, …, 6, and confirms equality at
  V = span{|00⟩, (|11⟩ + |22⟩)/√2} together with the values of C_*.
- **C4.** Checks symbolically the vectors T₁₁, T₂₂, T₁₂, the determinant 4 Tr(C_S) det(C_S), the vector y, the Schur-form
  case and the functional ℓ in the proof of Theorem 3.2. Checks numerically the identity q₂ = t₁ + β of Song and Chen,
  verifies t₁ = β = 0, z ≠ 0 and Nz = ξ₀ at zeros on random qubit-supported planes, and confirms that random planes whose
  local supports have dimension three are not zeros.
- **C5.** For j = 1, …, 9 a random vector with Gaussian-integer entries satisfies the three conditions of Lemma B.8. Ranks
  over F_p are lower bounds for ranks over C, because reduction from Z[i] to F_p (i ↦ a square root of −1) is a ring map.
- **C6.** Pairs (A, B) built from two-copy zeros in C⁴ ⊗ C⁴ attain the bound σ₁² + σ₂² ≤ 2(‖A‖² + ‖B‖²) and satisfy the
  rank condition; the pair A = diag(1, −1, 0, 0), B = 0 satisfies the rank condition with ratio 1/2; the two explicit
  diagonal saturating pairs of Liu and Chen attain the bound; random traceless pairs do not.
- **C7.** For k = 3 and d = 3, random planes give ratios 2^k m_k(V) / min_l ν₃^(l)(V) between 4 and 8; four local
  minimisations of m_k(V), with ν₃^(l)(V) ≥ 0.1 imposed at every copy, end at ratios between 1.021 and 1.027.

The scripts were first published with version 3 of *Undistillability of Werner states from three, four and five copies*
(doi:10.5281/zenodo.23682914, packages `release_zeros` and `release_allk`). Here only the labels in their comments and
output (row, theorem and section numbers) and one file path in a comment have been changed to match the present paper.

## Quick start

    python3 -m venv .venv && .venv/bin/pip install -r requirements.txt     # numpy >= 2, scipy, sympy
    PYTHON=.venv/bin/python ./run_all.sh

The run takes about six minutes on one core and ends with `ALL CHECKS PASSED`. Logs go to `logs/`, and the reference
outputs are in `expected/`. The floating-point steps use fixed seeds; their printed values may differ in the last digits on
other platforms, but each step's verdict line must read PASS or OK.

## Files

- `code/`: the seven scripts listed above.
- `expected/`: reference logs of a complete run.
- `run_all.sh`: runs every step and prints the verdict.
- `requirements.txt`, `LICENSE` (CC BY 4.0), `SHA256SUMS` (all files except itself).
