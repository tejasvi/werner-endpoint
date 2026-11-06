/-
NPT.CP3.PadB — padding of flat matrices (rows and/or columns indexed by the flat true-dimension index of a tuple) to
the padded Gram index `MI`, and the product rules (`BoxOK dims n` turns sums over `MI` into sums over `Fin n`).
-/
import NPT.CP3.Pad
import NPT.CP3.Bos

open Matrix BigOperators Finset

namespace NPT.CP3

variable (dims : Fin 5 → ℕ) {n : ℕ}

/-- The flat position of a padded index, if it lies in the box and below `n`. -/
def flatPos (μ : MI) : Option (Fin n) :=
  if h : inBox dims μ ∧ flatTrue dims μ < n then some ⟨flatTrue dims μ, h.2⟩ else none

/-- Rows padded. -/
noncomputable def padR {m : Type*} (X : Matrix (Fin n) m ℂ) : Matrix MI m ℂ :=
  fun μ j => match flatPos dims (n := n) μ with | some t => X t j | none => 0

/-- Columns padded. -/
noncomputable def padC {m : Type*} (X : Matrix m (Fin n) ℂ) : Matrix m MI ℂ :=
  fun j μ => match flatPos dims (n := n) μ with | some t => X j t | none => 0

/-- Rows and columns padded. -/
noncomputable def padRC (X : Matrix (Fin n) (Fin n) ℂ) : Matrix MI MI ℂ :=
  fun μ ν => match flatPos dims (n := n) μ, flatPos dims (n := n) ν with
    | some t, some s => X t s
    | _, _ => 0

variable {dims}

/-- A sum over `MI` of a function supported on the box is the flat sum. -/
lemma sum_MI_flat (h : BoxOK dims n) (f : Fin n → ℂ) :
    ∑ μ : MI, (match flatPos dims (n := n) μ with | some t => f t | none => 0) = ∑ t : Fin n, f t := by
  have e : ∀ μ : MI, (match flatPos dims (n := n) μ with | some t => f t | none => 0) =
      if inBox dims μ then (fun k : ℕ => if hk : k < n then f ⟨k, hk⟩ else 0) (flatTrue dims μ) else 0 := by
    intro μ
    unfold flatPos
    by_cases hb : inBox dims μ
    · by_cases hn : flatTrue dims μ < n
      · simp [hb, hn]
      · exact absurd (h.1 μ hb).1 hn
    · simp [hb]
  rw [Finset.sum_congr rfl fun μ _ => e μ]
  refine (sum_box h (fun k => if hk : k < n then f ⟨k, hk⟩ else 0)).trans ?_
  rw [Finset.sum_range (fun k => if hk : k < n then f ⟨k, hk⟩ else 0)]
  exact Finset.sum_congr rfl fun t _ => by simp [t.isLt]

lemma padC_mul_padR (h : BoxOK dims n) {m m' : Type*} [Fintype m] [Fintype m'] (X : Matrix m (Fin n) ℂ)
    (Y : Matrix (Fin n) m' ℂ) : padC dims X * padR dims Y = X * Y := by
  ext j k
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have e : ∀ μ : MI, padC dims X j μ * padR dims Y μ k =
      (match flatPos dims (n := n) μ with | some t => X j t * Y t k | none => 0) := by
    intro μ; unfold padC padR; cases flatPos dims (n := n) μ <;> simp
  rw [Finset.sum_congr rfl fun μ _ => e μ, sum_MI_flat h]

lemma padR_mul_padC {m : Type*} [Fintype m] (X : Matrix (Fin n) m ℂ) (Y : Matrix m (Fin n) ℂ) :
    padR dims X * padC dims Y = padRC dims (X * Y) := by
  ext μ ν
  rw [Matrix.mul_apply]
  unfold padR padC padRC
  cases flatPos dims (n := n) μ <;> cases flatPos dims (n := n) ν <;> simp [Matrix.mul_apply]

lemma padC_mul_padRC (h : BoxOK dims n) {m : Type*} [Fintype m] (X : Matrix m (Fin n) ℂ)
    (Y : Matrix (Fin n) (Fin n) ℂ) : padC dims X * padRC dims Y = padC dims (X * Y) := by
  ext j ν
  rw [Matrix.mul_apply]
  cases hν : flatPos dims (n := n) ν with
  | none =>
    have : ∀ μ : MI, padC dims X j μ * padRC dims Y μ ν = 0 := by
      intro μ; unfold padRC; rw [hν]; cases flatPos dims (n := n) μ <;> simp
    simp only [this, Finset.sum_const_zero]
    unfold padC; rw [hν]
  | some s =>
    have e : ∀ μ : MI, padC dims X j μ * padRC dims Y μ ν =
        (match flatPos dims (n := n) μ with | some t => X j t * Y t s | none => 0) := by
      intro μ; unfold padC padRC; rw [hν]; cases flatPos dims (n := n) μ <;> simp
    rw [Finset.sum_congr rfl fun μ _ => e μ, sum_MI_flat h]
    unfold padC; rw [hν]
    simp only [Matrix.mul_apply]

lemma padRC_transpose (X : Matrix (Fin n) (Fin n) ℂ) : (padRC dims X)ᵀ = padRC dims Xᵀ := by
  ext μ ν
  simp only [Matrix.transpose_apply]
  unfold padRC
  cases hμ : flatPos dims (n := n) μ <;> cases hν : flatPos dims (n := n) ν <;> simp [Matrix.transpose_apply]

/-- **Bosonic-range check, padded from flat.** -/
theorem hK_of_flat (h : BoxOK dims n) {m : ℕ} (W : Matrix (Fin n) (Fin m) ℂ) (Wi : Matrix (Fin m) (Fin n) ℂ)
    (Pf : Matrix (Fin n) (Fin n) ℂ) (hD2 : Pfᵀ = W * (Wi * Pfᵀ)) :
    (padRC dims Pf)ᵀ = padR dims W * (padC dims Wi * (padRC dims Pf)ᵀ) := by
  rw [padRC_transpose, padC_mul_padRC h, padR_mul_padC, ← hD2]

/-- **Stabilizer action, padded from flat**: if `permMI σ` acts on flat positions by `πσ`, a flat identity
`W (πσ t) = (W B) t` gives `Q_σ W = W B` on padded matrices. -/
theorem hB_of_flat (σ : Equiv.Perm (Fin 4)) (πσ : Fin n → Fin n)
    (hperm : ∀ μ : MI, flatPos dims (n := n) (permMI σ μ) = (flatPos dims (n := n) μ).map πσ)
    {m : ℕ} (W : Matrix (Fin n) (Fin m) ℂ) (B : Matrix (Fin m) (Fin m) ℂ) (hflat : ∀ t j, W (πσ t) j = (W * B) t j) :
    Qperm σ * padR dims W = padR dims W * B := by
  ext μ j
  rw [Qperm_mul_apply, Matrix.mul_apply]
  unfold padR
  rw [hperm μ]
  cases flatPos dims (n := n) μ with
  | none => simp
  | some t =>
    simp only [Option.map_some]
    rw [hflat t j, Matrix.mul_apply]

/-- **Left inverse, padded from flat.** -/
theorem hWp_of_flat (h : BoxOK dims n) {m : ℕ} (W : Matrix (Fin n) (Fin m) ℂ) (Wi : Matrix (Fin m) (Fin n) ℂ)
    (hW : Wi * W = 1) : padC dims Wi * padR dims W = 1 := by
  rw [padC_mul_padR h, hW]

end NPT.CP3
