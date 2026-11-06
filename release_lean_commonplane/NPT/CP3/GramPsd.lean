/-
NPT.CP3.GramPsd — Gram forms of positive semidefinite operators on real modules are positive semidefinite.
-/
import NPT.CP3.Site

open Matrix BigOperators Finset NPT.Brauer
open scoped ComplexOrder

namespace NPT.CP3

/-- Padded module data with real entries. -/
def PadData.Real (P : PadData) : Prop :=
  (∀ k x a, star (P.Ms k x a) = P.Ms k x a) ∧ (∀ k x a, star (P.Ma k x a) = P.Ma k x a)

lemma PadData.M_real {P : PadData} (hP : P.Real) (l k : Fin 5) (x : Dig (nfC l) 4) (a : Fin (dpad l)) :
    star (P.M l k x a) = P.M l k x a := by
  unfold PadData.M
  split_ifs
  · exact hP.1 _ _ _
  · exact hP.2 _ _ _

lemma Jt_conjTranspose {P : PadData} (hP : P.Real) (τ : Tup P.fam) : (Jt P.fam τ)ᴴ = (Jt P.fam τ)ᵀ := by
  ext μ i
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Jt, kronR, star_prod]
  exact Finset.prod_congr rfl fun l _ => PadData.M_real hP l (τ l) (i l) (μ l)

/-- Gram forms of PSD operators on real modules are PSD. -/
theorem gram_psd {P : PadData} (hP : P.Real) (τ : Tup P.fam) {Y : Matrix GC GC ℂ} (hY : Y.PosSemidef) :
    (gram P.fam τ Y).PosSemidef := by
  have h := hY.conjTranspose_mul_mul_same (Jt P.fam τ)
  rw [Jt_conjTranspose hP] at h
  exact h

/-- Compressions of Gram forms of PSD operators are PSD. -/
theorem gram_compress_psd {P : PadData} (hP : P.Real) (τ : Tup P.fam) {Y : Matrix GC GC ℂ} (hY : Y.PosSemidef)
    {m : ℕ} (V : Matrix MI (Fin m) ℂ) : (Vᴴ * gram P.fam τ Y * V).PosSemidef :=
  (gram_psd hP τ hY).conjTranspose_mul_mul_same V

end NPT.CP3
