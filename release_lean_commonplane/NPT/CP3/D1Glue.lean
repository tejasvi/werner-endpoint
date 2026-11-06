/-
NPT.CP3.D1Glue — small glue between the padded matrices of `NPT.CP3.PadB` and the bridge of the D1 check.

* `padR_transpose`: `(padR X)ᵀ = padC Xᵀ`;
* `padR_mul`: `padR X * S = padR (X * S)`;
* `padR_WSW`: `padR W * S * (padR W)ᵀ = padRC (W * S * Wᵀ)` (the Gram forms of the coordinate basis).
-/
import NPT.CP3.D1Bridge5

open Matrix BigOperators Finset

namespace NPT.CP3

variable {dims : Fin 5 → ℕ} {n : ℕ}

lemma padR_transpose {m : Type*} (X : Matrix (Fin n) m ℂ) : (padR dims X)ᵀ = padC dims Xᵀ := by
  ext j μ
  simp only [Matrix.transpose_apply, padR, padC]

lemma padR_mul {m m' : Type*} [Fintype m] (X : Matrix (Fin n) m ℂ) (S : Matrix m m' ℂ) :
    padR dims X * S = padR dims (X * S) := by
  ext μ j
  rw [Matrix.mul_apply]
  unfold padR
  cases flatPos dims (n := n) μ <;> simp [Matrix.mul_apply]

/-- **Padded Gram forms of the coordinate basis.** -/
lemma padR_WSW {m : ℕ} (W : Matrix (Fin n) (Fin m) ℂ) (S : Matrix (Fin m) (Fin m) ℂ) :
    padR dims W * S * (padR dims W)ᵀ = padRC dims (W * S * Wᵀ) := by
  rw [padR_mul, padR_transpose, padR_mul_padC]

end NPT.CP3
