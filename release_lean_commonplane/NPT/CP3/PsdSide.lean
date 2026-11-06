/-
NPT.CP3.PsdSide — the positive semidefinite side of the active blocks.

The padded module data of the certificate are real (`PD_real`), and so are the padded output bases `padR dims V` of
integer matrices. Hence the compressed Gram forms `Vᵀ H_τ(Y) V` of `Y = Yp A` (cut `()`) and of `Y^{Γ₃}` (cut `(3,)`)
are positive semidefinite (`psd_cut0`, `psd_cut3`).
-/
import NPT.CP3.PD
import NPT.CP3.GramPsd
import NPT.CP3.PadB

open Matrix BigOperators Finset NPT.Brauer NPT.Cert
open scoped ComplexOrder

namespace NPT.CP3.Inst

open NPT.CP3

/-- The padded module data of every cut are real. -/
lemma PD_real (c : ℕ) : (PD c).Real := by
  refine ⟨fun k x a => ?_, fun k z j => ?_⟩
  · show star (MsC c k x a) = MsC c k x a
    unfold MsC
    split_ifs <;> simp
  · show star (MaC c k z j) = MaC c k z j
    unfold MaC
    split_ifs <;> simp

/-- A padded basis of a real matrix is real: `(padR V)ᴴ = (padR V)ᵀ`. -/
lemma padR_conjTranspose {dims : Fin 5 → ℕ} {n m : ℕ} (V : Matrix (Fin n) (Fin m) ℂ)
    (hV : ∀ p u, star (V p u) = V p u) : (padR dims V)ᴴ = (padR dims V)ᵀ := by
  ext u μ
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, padR]
  cases flatPos dims (n := n) μ <;> simp [hV]

/-- **Cut `()`:** compressed Gram forms of the projected moment are PSD. -/
theorem psd_cut0 {P : PadData} (hP : P.Real) (A : MatA) (τ : Tup P.fam) {m : ℕ} (V : Matrix MI (Fin m) ℂ)
    (hV : Vᴴ = Vᵀ) : (Vᵀ * gram P.fam τ (Yp A) * V).PosSemidef := by
  rw [← hV]
  exact gram_compress_psd hP τ (Yp_psd A) V

/-- **Cut `(3,)`:** compressed Gram forms of the partially transposed projected moment are PSD. -/
theorem psd_cut3 {P : PadData} (hP : P.Real) (A : MatA) (τ : Tup P.fam) {m : ℕ} (V : Matrix MI (Fin m) ℂ)
    (hV : Vᴴ = Vᵀ) : (Vᵀ * gram P.fam τ (gam3 (Yp A)) * V).PosSemidef := by
  rw [← hV]
  exact gram_compress_psd hP τ (gam3_Yp_psd A) V

end NPT.CP3.Inst
