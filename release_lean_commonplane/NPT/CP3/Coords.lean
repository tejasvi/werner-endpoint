/-
NPT.CP3.Coords — the coordinates of one tuple's Gram form of the projected moment (G3 + G4 combined).

Given intertwining modules, the bosonic-range data (`W`, `W⁺`, `K`), the stabilizer data (`σ_i`, `B_i`) and the span
certificate of the variable basis `S_j`, the Gram form of `Yp A` at the tuple `τ` is `Σ_j y_j W S_j Wᵀ` with explicit
coordinates `y_j`. With an empty basis (`ι` empty) this says that the Gram form vanishes (the skipped tuples).
-/
import NPT.CP3.Bos

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem

namespace NPT.CP3

/-- The coordinates of a tuple's Gram form (`S = W⁺ H W⁺ᵀ`). -/
noncomputable def ycoord {r ι : Type*} [Fintype r] {n : ℕ} (S : Matrix r r ℂ) (c : r → r → ι → ℂ) (j : ι) : ℂ :=
  (∑ a, ∑ b, S a b * c a b j) / (2 * n)

/-- **Coordinates of a tuple.** -/
theorem tuple_coords (P : PadData) {πp : (l : Fin 5) → Fin 5 → Fin 24 → Matrix (Fin (dpad l)) (Fin (dpad l)) ℂ}
    (h : Intertw P πp) (τ : Tup P.fam) (A : MatA)
    {r : Type*} [Fintype r] [DecidableEq r] (W : Matrix MI r ℂ) (Wp K : Matrix r MI ℂ) (hWp : Wp * W = 1)
    (hK : (Pav πp τ)ᵀ = W * K)
    {n : ℕ} (σs : Fin n → Equiv.Perm (Fin 4)) (hσ : ∀ i, (fun l => τ (sigHat (σs i) l)) = τ)
    (B : Fin n → Matrix r r ℂ) (hB : ∀ i, Qperm (σs i) * W = W * B i)
    {ι : Type*} [Fintype ι] (Sj : ι → Matrix r r ℂ) (c : r → r → ι → ℂ)
    (hc : ∀ a b, ∑ i, B i * symU a b * (B i)ᵀ = ∑ j, c a b j • Sj j) (hn : n ≠ 0) :
    gram P.fam τ (Yp A) =
      ∑ j, ycoord (n := n) (Wp * gram P.fam τ (Yp A) * Wpᵀ) c j • (W * Sj j * Wᵀ) := by
  set H := gram P.fam τ (Yp A) with hHdef
  set S := Wp * H * Wpᵀ with hSdef
  have hH : H = W * S * Wᵀ := gram_range P h τ W Wp K hWp hK A
  have hSt : Sᵀ = S := by
    rw [hSdef, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, gram_Yp_transpose,
      Matrix.mul_assoc]
  have hS : ∀ i, B i * S * (B i)ᵀ = S := fun i =>
    coord_stab P (σs i) τ (hσ i) A W Wp hWp (B i) (hB i) hH
  have hSsum : S = ∑ j, ycoord (n := n) S c j • Sj j := stab_coord B S hSt hS Sj c hc hn
  calc H = W * S * Wᵀ := hH
    _ = W * (∑ j, ycoord (n := n) S c j • Sj j) * Wᵀ := by rw [← hSsum]
    _ = ∑ j, ycoord (n := n) S c j • (W * Sj j * Wᵀ) := by
        rw [Matrix.mul_sum, Matrix.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.mul_smul, Matrix.smul_mul]

/-- A tuple whose variable basis is empty has a vanishing Gram form. -/
theorem tuple_zero (P : PadData) {πp : (l : Fin 5) → Fin 5 → Fin 24 → Matrix (Fin (dpad l)) (Fin (dpad l)) ℂ}
    (h : Intertw P πp) (τ : Tup P.fam) (A : MatA)
    {r : Type*} [Fintype r] [DecidableEq r] (W : Matrix MI r ℂ) (Wp K : Matrix r MI ℂ) (hWp : Wp * W = 1)
    (hK : (Pav πp τ)ᵀ = W * K)
    {n : ℕ} (σs : Fin n → Equiv.Perm (Fin 4)) (hσ : ∀ i, (fun l => τ (sigHat (σs i) l)) = τ)
    (B : Fin n → Matrix r r ℂ) (hB : ∀ i, Qperm (σs i) * W = W * B i)
    (hc : ∀ a b, ∑ i, B i * symU a b * (B i)ᵀ = 0) (hn : n ≠ 0) :
    gram P.fam τ (Yp A) = 0 := by
  have := tuple_coords P h τ A W Wp K hWp hK σs hσ B hB (ι := Fin 0) (fun j => Fin.elim0 j)
    (fun _ _ j => Fin.elim0 j) (fun a b => by rw [hc a b]; simp) hn
  simpa using this

end NPT.CP3
