/-
NPT.CP3.MainR — the common-plane theorem from the certificate (real data indexed by `ℕ`, the form of `NPT.CP3.Sem`)
and the link facts at the physical coordinate vector `yvec T A`.
-/
import NPT.CP3.Basic
import NPT.CP3.SoundR
import NPT.CP3.Assemble

open Matrix BigOperators Finset
open scoped ComplexOrder

namespace NPT.CP3

lemma fin2_etaR (w : Fin 2 → ℝ) : w = ![w 0, w 1] := by
  funext i; fin_cases i <;> rfl

/-- **The common-plane theorem from the certificate and the link facts** (real data). -/
theorem q4_commonPlane_of_linksR {P : PadData}
    {πp : (l : Fin 5) → Fin 5 → Fin 24 → Matrix (Fin (dpad l)) (Fin (dpad l)) ℂ}
    {nV : ℕ} (T : Fin nV → TupleData P πp)
    (nC nK nE : ℕ) (mOf : ℕ → ℕ) (Fmat : (k i : ℕ) → Matrix (Fin (mOf k)) (Fin (mOf k)) ℝ)
    (Erow lam cvec : ℕ → ℕ → ℝ) (Zmat : (k : ℕ) → Matrix (Fin (2 * mOf k)) (Fin (2 * mOf k)) ℝ)
    (hident : ∀ c < 3, ∀ i < nC, cvec c i = (∑ e ∈ range nE, Erow e i * lam c e) +
      ∑ k ∈ range nK, ∑ u : Fin (mOf k), ∑ v : Fin (mOf k), Fmat k i u v * partH c (Zmat k) u v)
    (hFsym : ∀ k i u v, Fmat k i u v = Fmat k i v u)
    (hZt : ∀ k < nK, (Zmat k)ᵀ = Zmat k) (hZ : ∀ k < nK, (crm (Zmat k)).PosSemidef)
    (hF : ∀ A : MatA, Aᴴ * A = 1 → ∀ k < nK, (∑ i ∈ range nC, yvec T A i • crm (Fmat k i)).PosSemidef)
    (hE : ∀ A : MatA, Aᴴ * A = 1 → ∀ e < nE, ∑ i ∈ range nC, yvec T A i * (Erow e i : ℂ) = 0)
    (κ : ℝ) (hκ : 0 < κ)
    (hobj : ∀ A : MatA, Aᴴ * A = 1 → ∀ x₁ x₂ : ℝ,
      ∑ i ∈ range nC, yvec T A i * ((x₁ : ℂ) ^ 2 * (cvec 0 i : ℂ) + (x₂ : ℂ) ^ 2 * (cvec 1 i : ℂ) +
        (x₁ : ℂ) * x₂ * (cvec 2 i : ℂ)) = (κ : ℂ) * (Ow ![x₁, x₂] * Yp A).trace)
    (U : Matrix (NPT.Idx (Fin 4) 3) (Fin 2) ℂ) (hU : Uᴴ * U = 1) (c : Matrix (Fin 2) (Fin 2) ℂ) :
    0 ≤ NPT.q (1 / 2) (U * c * Uᴴ) := by
  refine q_nonneg_of_stiefel (1 / 2) (fun A hA w => ?_) U hU c
  have hs := sound_real nC nK nE mOf Fmat Erow lam cvec Zmat hident hFsym hZt hZ (yvec T A) (hF A hA) (hE A hA)
    (w 0) (w 1)
  rw [hobj A hA (w 0) (w 1), trace_Ow_Yp_q hA, ← fin2_etaR w] at hs
  have h3 : (0 : ℂ) ≤ ((κ * (3072 * NPT.q (1 / 2) (A * diagonal (fun i => (w i : ℂ)) * Aᴴ)) : ℝ) : ℂ) := by
    push_cast at hs ⊢
    exact hs
  have h4 : 0 ≤ κ * (3072 * NPT.q (1 / 2) (A * diagonal (fun i => (w i : ℂ)) * Aᴴ)) := Complex.zero_le_real.mp h3
  have h5 : 0 ≤ 3072 * NPT.q (1 / 2) (A * diagonal (fun i => (w i : ℂ)) * Aᴴ) :=
    nonneg_of_mul_nonneg_right (by linarith [h4]) hκ |>.trans_eq' rfl
  nlinarith [h5]

end NPT.CP3
