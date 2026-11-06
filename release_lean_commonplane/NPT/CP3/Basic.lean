/-
NPT.CP3.Basic — reduction of the common-plane statement to Stiefel pairs with real diagonal weights.

An operator `C = U c Uᴴ` (`U` an isometry `ℂ² → (ℂ^d)^{⊗ι}`, so range and co-range of `C` lie in the plane `ran U`)
splits as `C = H + i K` with `H = U h Uᴴ`, `K = U k Uᴴ` Hermitian, and `q t (H + i K) = q t H + q t K`
(`q_add_I`: the cross terms vanish because `Tr_J H` and `Tr_J K` are Hermitian). A Hermitian `U h Uᴴ` equals
`A diag(w) Aᴴ` with `A = U V` Stiefel (`V` unitary, `h = V diag(w) Vᴴ`). So `q t ≥ 0` on the common-plane sector
follows from `q t (A diag(w) Aᴴ) ≥ 0` for all Stiefel `A` and real `w` (`q_nonneg_of_stiefel`).
-/
import NPT.Basic
import Mathlib.Analysis.Matrix.Spectrum

open Matrix BigOperators Finset

namespace NPT.CP3

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ} [NeZero d]

/-! ### Linearity of the partial trace -/

lemma ptrace_add (J : Finset ι) (A B : Op ι d) : ptrace J (A + B) = ptrace J A + ptrace J B := by
  funext x y
  rw [Matrix.add_apply]
  by_cases h : ZeroOn J x ∧ ZeroOn J y
  · simp only [ptrace_apply_pos h, Matrix.add_apply, Finset.sum_add_distrib]
  · simp only [ptrace_apply_neg h, add_zero]

lemma ptrace_smul (J : Finset ι) (c : ℂ) (A : Op ι d) : ptrace J (c • A) = c • ptrace J A := by
  funext x y
  rw [Matrix.smul_apply]
  by_cases h : ZeroOn J x ∧ ZeroOn J y
  · simp only [ptrace_apply_pos h, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  · simp only [ptrace_apply_neg h, smul_zero]

lemma ptrace_conjTranspose (J : Finset ι) (A : Op ι d) : ptrace J Aᴴ = (ptrace J A)ᴴ := by
  funext x y
  rw [Matrix.conjTranspose_apply]
  by_cases h : ZeroOn J x ∧ ZeroOn J y
  · have h' : ZeroOn J y ∧ ZeroOn J x := ⟨h.2, h.1⟩
    rw [ptrace_apply_pos h, ptrace_apply_pos h', star_sum]
    simp only [Matrix.conjTranspose_apply]
  · have h' : ¬ (ZeroOn J y ∧ ZeroOn J x) := fun h'' => h ⟨h''.2, h''.1⟩
    rw [ptrace_apply_neg h, ptrace_apply_neg h', star_zero]

lemma ptrace_isHermitian (J : Finset ι) {H : Op ι d} (hH : H.IsHermitian) : (ptrace J H).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [← ptrace_conjTranspose, hH.eq]

/-! ### The Hermitian split -/

omit [NeZero d] in
/-- `‖H + i K‖² = ‖H‖² + ‖K‖²` for Hermitian `H, K` (Frobenius norm). -/
lemma frobSq_add_I {H K : Op ι d} (hH : H.IsHermitian) (hK : K.IsHermitian) :
    frobSq (H + Complex.I • K) = frobSq H + frobSq K := by
  set T : ℂ := ∑ x, ∑ y, H x y * star (K x y) with hTdef
  have hconj : star T = T := by
    rw [hTdef, star_sum]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [star_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [star_mul', star_star, ← hH.apply y x, hK.apply x y]
  have hT : T.im = 0 := Complex.conj_eq_iff_im.mp hconj
  have hsum : ∑ x, ∑ y, (H x y * star (K x y)).im = 0 := by
    rw [← hT, hTdef]
    simp only [Complex.im_sum]
  have key : ∀ x y, Complex.normSq ((H + Complex.I • K) x y) =
      Complex.normSq (H x y) + Complex.normSq (K x y) + 2 * (H x y * star (K x y)).im := by
    intro x y
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.normSq_add, Complex.normSq_mul,
      Complex.normSq_I, one_mul]
    congr 2
    simp only [map_mul, Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
      Complex.I_re, Complex.I_im, Complex.star_def]
    ring
  unfold frobSq
  calc ∑ x, ∑ y, Complex.normSq ((H + Complex.I • K) x y)
      = ∑ x, ∑ y, (Complex.normSq (H x y) + Complex.normSq (K x y) + 2 * (H x y * star (K x y)).im) := by
        simp_rw [key]
    _ = (∑ x, ∑ y, Complex.normSq (H x y)) + (∑ x, ∑ y, Complex.normSq (K x y)) +
          2 * ∑ x, ∑ y, (H x y * star (K x y)).im := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = (∑ x, ∑ y, Complex.normSq (H x y)) + ∑ x, ∑ y, Complex.normSq (K x y) := by
        rw [hsum, mul_zero, add_zero]

/-- **Hermitian split.** `q t (H + i K) = q t H + q t K` for Hermitian `H, K`. -/
theorem q_add_I (t : ℝ) {H K : Op ι d} (hH : H.IsHermitian) (hK : K.IsHermitian) :
    q t (H + Complex.I • K) = q t H + q t K := by
  unfold q
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [ptrace_add, ptrace_smul, frobSq_add_I (ptrace_isHermitian J hH) (ptrace_isHermitian J hK), mul_add]

/-! ### Normal form on the plane -/

/-- Hermitian part of a 2×2 matrix. -/
noncomputable def hpart (c : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℂ) • (c + cᴴ)

/-- `-i` times the anti-Hermitian part of a 2×2 matrix. -/
noncomputable def kpart (c : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := (-Complex.I / 2) • (c - cᴴ)

lemma hpart_add_kpart (c : Matrix (Fin 2) (Fin 2) ℂ) : hpart c + Complex.I • kpart c = c := by
  unfold hpart kpart
  rw [smul_smul]
  have h1 : Complex.I * (-Complex.I / 2) = 1 / 2 := by
    rw [mul_div_assoc', mul_neg, Complex.I_mul_I, neg_neg]
  rw [h1, ← smul_add]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  ring

lemma hpart_isHermitian (c : Matrix (Fin 2) (Fin 2) ℂ) : (hpart c).IsHermitian := by
  unfold Matrix.IsHermitian hpart
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]
  congr 1
  simp

lemma kpart_isHermitian (c : Matrix (Fin 2) (Fin 2) ℂ) : (kpart c).IsHermitian := by
  unfold Matrix.IsHermitian kpart
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  have hs : star (-Complex.I / 2) = Complex.I / 2 := by
    simp [Complex.star_def, map_div₀, Complex.conj_I]
  rw [hs]
  ring

omit [NeZero d] in
/-- A Hermitian operator on the plane `ran U` is `A diag(w) Aᴴ` for a Stiefel `A` and real `w`. -/
lemma herm_plane_normal (U : Matrix (Idx ι d) (Fin 2) ℂ) (hU : Uᴴ * U = 1) {h : Matrix (Fin 2) (Fin 2) ℂ}
    (hh : h.IsHermitian) :
    ∃ A : Matrix (Idx ι d) (Fin 2) ℂ, Aᴴ * A = 1 ∧ ∃ w : Fin 2 → ℝ,
      U * h * Uᴴ = A * diagonal (fun i => (w i : ℂ)) * Aᴴ := by
  set V : Matrix (Fin 2) (Fin 2) ℂ := (hh.eigenvectorUnitary : Matrix (Fin 2) (Fin 2) ℂ) with hVdef
  have hV : star V * V = 1 := by
    rw [hVdef]
    exact Matrix.mem_unitaryGroup_iff'.mp hh.eigenvectorUnitary.2
  have hspec : h = V * diagonal (fun i => ((hh.eigenvalues i : ℝ) : ℂ)) * star V := by
    rw [hVdef]
    conv_lhs => rw [hh.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, Function.comp_def]
  refine ⟨U * V, ?_, fun i => hh.eigenvalues i, ?_⟩
  · rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul,
      ← Matrix.star_eq_conjTranspose, hV]
  · conv_lhs => rw [hspec]
    rw [Matrix.conjTranspose_mul, ← Matrix.star_eq_conjTranspose V]
    simp only [Matrix.mul_assoc]

/-- **Reduction.** If `q t (A diag(w) Aᴴ) ≥ 0` for every Stiefel `A` (two orthonormal columns) and every real `w`,
then `q t (U c Uᴴ) ≥ 0` for every isometry `U : ℂ² → (ℂ^d)^{⊗ι}` and every `c`, i.e. on the whole common-plane
sector. -/
theorem q_nonneg_of_stiefel (t : ℝ)
    (hS : ∀ A : Matrix (Idx ι d) (Fin 2) ℂ, Aᴴ * A = 1 → ∀ w : Fin 2 → ℝ,
      0 ≤ q t (A * diagonal (fun i => (w i : ℂ)) * Aᴴ))
    (U : Matrix (Idx ι d) (Fin 2) ℂ) (hU : Uᴴ * U = 1) (c : Matrix (Fin 2) (Fin 2) ℂ) :
    0 ≤ q t (U * c * Uᴴ) := by
  have hdecomp : U * c * Uᴴ = U * hpart c * Uᴴ + Complex.I • (U * kpart c * Uᴴ) := by
    conv_lhs => rw [← hpart_add_kpart c]
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have herm : ∀ h : Matrix (Fin 2) (Fin 2) ℂ, h.IsHermitian → 0 ≤ q t (U * h * Uᴴ) := by
    intro h hh
    obtain ⟨A, hA, w, hw⟩ := herm_plane_normal U hU hh
    rw [hw]
    exact hS A hA w
  rw [hdecomp, q_add_I t (isHermitian_mul_mul_conjTranspose _ (hpart_isHermitian c))
    (isHermitian_mul_mul_conjTranspose _ (kpart_isHermitian c))]
  exact add_nonneg (herm _ (hpart_isHermitian c)) (herm _ (kpart_isHermitian c))

omit [NeZero d] in
/-- Range form: if `P = U Uᴴ` is the projector onto the plane `ran U` and `P C P = C` (range and co-range of `C`
inside the plane), then `C = U (Uᴴ C U) Uᴴ`. -/
lemma eq_of_plane (U : Matrix (Idx ι d) (Fin 2) ℂ) (C : Op ι d) (hC : U * Uᴴ * C * (U * Uᴴ) = C) :
    C = U * (Uᴴ * C * U) * Uᴴ := by
  conv_lhs => rw [← hC]
  simp only [Matrix.mul_assoc]

end NPT.CP3
