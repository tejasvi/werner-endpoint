/-
NPT.Cert.CondExp — Lemma P: the Hilbert–Schmidt "conditional expectation" onto a unital
*-subalgebra of matrices preserves positive semidefiniteness.

This replaces the Haar twirl in the soundness proof of the moment certificates
(see `DESIGN_soundness.md`): if `Z ∈ 𝒜` reproduces all traces `Tr(Yᴴ X)`, `Y ∈ 𝒜`, of a PSD
matrix `X`, then `Z` is PSD.
-/
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Matrix.PosDef

open Matrix
open scoped ComplexOrder

namespace NPT

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- Members of a star subalgebra of matrices are closed under conjugate transpose. -/
lemma conjTranspose_mem (𝒜 : StarSubalgebra ℂ (Matrix m m ℂ)) {Y : Matrix m m ℂ} (hY : Y ∈ 𝒜) :
    Yᴴ ∈ 𝒜 := by
  simpa [Matrix.star_eq_conjTranspose] using star_mem hY

/-- A matrix `Z` in a star subalgebra that reproduces the traces of a Hermitian `X` against the
subalgebra is Hermitian. -/
lemma isHermitian_of_trace_eq (𝒜 : StarSubalgebra ℂ (Matrix m m ℂ)) {X Z : Matrix m m ℂ}
    (hX : X.IsHermitian) (hZ : Z ∈ 𝒜)
    (hproj : ∀ Y ∈ 𝒜, (Yᴴ * Z).trace = (Yᴴ * X).trace) : Z.IsHermitian := by
  have hstar : ∀ Y ∈ 𝒜, (Yᴴ * Zᴴ).trace = (Yᴴ * Z).trace := by
    intro Y hY
    have h1 : (Y * Z).trace = (Y * X).trace := by
      simpa using hproj Yᴴ (conjTranspose_mem 𝒜 hY)
    calc (Yᴴ * Zᴴ).trace = star ((Z * Y).trace) := by
          rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul]
      _ = star ((Y * Z).trace) := by rw [Matrix.trace_mul_comm]
      _ = star ((Y * X).trace) := by rw [h1]
      _ = (Xᴴ * Yᴴ).trace := by rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul]
      _ = (Yᴴ * X).trace := by rw [hX.eq, Matrix.trace_mul_comm]
      _ = (Yᴴ * Z).trace := (hproj Y hY).symm
  have hDmem : Z - Zᴴ ∈ 𝒜 := 𝒜.sub_mem hZ (conjTranspose_mem 𝒜 hZ)
  have htr : ((Z - Zᴴ)ᴴ * (Z - Zᴴ)).trace = 0 := by
    rw [Matrix.mul_sub, Matrix.trace_sub, hstar _ hDmem, sub_self]
  have h0 : (Z - Zᴴ)ᴴ * (Z - Zᴴ) = 0 :=
    (Matrix.PosSemidef.trace_eq_zero_iff (Matrix.posSemidef_conjTranspose_mul_self _)).1 htr
  have hD0 : Z - Zᴴ = 0 := Matrix.conjTranspose_mul_self_eq_zero.1 h0
  exact (sub_eq_zero.1 hD0).symm

open scoped ComplexOrder in
/-- **Lemma P.** Let `𝒜` be a star subalgebra of `Matrix m m ℂ`. If `X` is positive semidefinite
and `Z ∈ 𝒜` satisfies `Tr(Yᴴ Z) = Tr(Yᴴ X)` for every `Y ∈ 𝒜`, then `Z` is positive
semidefinite. -/
theorem condexp_posSemidef (𝒜 : StarSubalgebra ℂ (Matrix m m ℂ)) {X Z : Matrix m m ℂ}
    (hX : X.PosSemidef) (hZ : Z ∈ 𝒜)
    (hproj : ∀ Y ∈ 𝒜, (Yᴴ * Z).trace = (Yᴴ * X).trace) : Z.PosSemidef := by
  have hherm : Z.IsHermitian := isHermitian_of_trace_eq 𝒜 hX.1 hZ hproj
  -- the negative part `N = f(Z)`, `f x = max (-x) 0`, lies in `𝒜`
  set f : ℝ → ℝ := fun x => max (-x) 0 with hf
  have hcl : IsClosed (𝒜 : Set (Matrix m m ℂ)) :=
    Submodule.closed_of_finiteDimensional (Subalgebra.toSubmodule 𝒜.toSubalgebra)
  have hN : cfc f Z ∈ 𝒜 := by
    have := hcl
    exact cfc_mem f hZ
  -- spectral data
  set U : Matrix m m ℂ := (hherm.eigenvectorUnitary : Matrix m m ℂ) with hUdef
  set lam := hherm.eigenvalues with hlam
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hZspec : Z = U * diagonal (fun i => ((lam i : ℝ) : ℂ)) * star U := by
    conv_lhs => rw [hherm.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply]
    rfl
  have hNspec : cfc f Z = U * diagonal (fun i => ((f (lam i) : ℝ) : ℂ)) * star U := by
    rw [hherm.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
    rfl
  -- `N` is Hermitian
  have hNH : (cfc f Z)ᴴ = cfc f Z := by
    have : IsSelfAdjoint (cfc f Z) := cfc_predicate f Z
    simpa [Matrix.star_eq_conjTranspose] using this.star_eq
  -- the two traces
  set D1 := diagonal (fun i => ((f (lam i) : ℝ) : ℂ)) with hD1
  set D2 := diagonal (fun i => ((lam i : ℝ) : ℂ)) with hD2
  have hTZ : (cfc f Z * Z).trace = ∑ i, (((f (lam i) * lam i : ℝ)) : ℂ) := by
    rw [hNspec, hZspec]
    have e1 : U * D1 * star U * (U * D2 * star U) = U * (D1 * (D2 * star U)) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul]
    rw [e1, Matrix.trace_mul_comm]
    have e2 : D1 * (D2 * star U) * U = D1 * D2 := by
      simp only [Matrix.mul_assoc]
      rw [hUU, Matrix.mul_one]
    rw [e2, hD1, hD2, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
    simp
  have hTX : 0 ≤ (cfc f Z * X).trace := by
    rw [hNspec]
    have hc : (U * D1 * star U * X).trace = (D1 * (star U * X * U)).trace := by
      rw [show U * D1 * star U * X = U * (D1 * star U * X) by simp only [Matrix.mul_assoc]]
      rw [Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    rw [hc, Matrix.trace]
    refine Finset.sum_nonneg fun i _ => ?_
    rw [hD1, Matrix.diag_apply, Matrix.diagonal_mul]
    have hpsd : (star U * X * U).PosSemidef := by
      have := hX.conjTranspose_mul_mul_same U
      simpa [Matrix.star_eq_conjTranspose] using this
    have hdi : 0 ≤ (star U * X * U) i i := hpsd.diag_nonneg
    have hfi : (0 : ℂ) ≤ ((f (lam i) : ℝ) : ℂ) := by
      have : (0 : ℝ) ≤ f (lam i) := by simp only [hf]; exact le_max_right _ _
      exact_mod_cast this
    exact mul_nonneg hfi hdi
  -- combine
  have heq : (cfc f Z * Z).trace = (cfc f Z * X).trace := by
    simpa [hNH] using hproj (cfc f Z) hN
  have hsum : (0 : ℝ) ≤ ∑ i, f (lam i) * lam i := by
    have h := hTX
    rw [← heq, hTZ] at h
    have h' : ((0 : ℝ) : ℂ) ≤ ((∑ i, f (lam i) * lam i : ℝ) : ℂ) := by
      simpa [Complex.ofReal_sum] using h
    exact_mod_cast h'
  have hterm : ∀ i, f (lam i) * lam i ≤ 0 := by
    intro i
    simp only [hf]
    rcases le_total (lam i) 0 with h | h
    · rw [max_eq_left (by linarith)]; nlinarith
    · rw [max_eq_right (by linarith)]; simp
  have hsum0 : ∑ j, f (lam j) * lam j = 0 :=
    le_antisymm (Finset.sum_nonpos fun j _ => hterm j) hsum
  have hzero : ∀ i, f (lam i) * lam i = 0 := fun i =>
    (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => hterm j)).1 hsum0 i (Finset.mem_univ _)
  rw [hherm.posSemidef_iff_eigenvalues_nonneg]
  intro i
  have h := hzero i
  by_contra hneg
  have hlt : lam i < 0 := lt_of_not_ge hneg
  have hmax : max (-lam i) 0 = -lam i := max_eq_left (by linarith)
  simp only [hf, hmax] at h
  nlinarith

end NPT

#print axioms NPT.condexp_posSemidef
