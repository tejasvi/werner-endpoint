/-
NPT.CP3.Psem — scalar functionals of the Gram forms as functions of the coordinates (the objective and the equality
rows, after `lift_c`): for local functionals `ell`,
`Σ_τ ⟨⊗_l ell_l(τ l), H_τ(Y)⟩ = Σ_v Σ_j y_(off v + j) Σ_c ⟨⊗_l ell_l(new_c l), reindexMI perm_c (WSW_j)⟩`
under the hypotheses of `fsem_sound0` (`psem_sound`).
-/
import NPT.CP3.Fsem

open Matrix BigOperators Finset NPT.Brauer NPT.Cert

namespace NPT.CP3

lemma pairing_finsum {ι W : Type*} [Fintype ι] (G : Matrix ι ι ℂ) (s : Finset W) (M : W → Matrix ι ι ℂ) :
    pairing G (∑ w ∈ s, M w) = ∑ w ∈ s, pairing G (M w) := by
  have h := pairing_sum G s (fun _ => (1 : ℂ)) M
  simp only [one_smul, one_mul] at h
  exact h

lemma pairing_ite {ι : Type*} [Fintype ι] (G M : Matrix ι ι ℂ) (p : Prop) [Decidable p] :
    pairing G (if p then M else 0) = if p then pairing G M else 0 := by
  split_ifs <;> simp [pairing]

/-- **Scalar functionals as functions of the coordinates.** -/
theorem psem_sound (P0 : PadData) (D : OrbitData) (hcos : D.CosOK) (hinj : Function.Injective D.newOf)
    {Y : Matrix GC GC ℂ} (hsym : ∀ σ : Equiv.Perm (Fin 4), ∀ i j, Y (permIdx σ i) (permIdx σ j) = Y i j)
    (hout : ∀ τ : Tup P0.fam, (∀ x, D.newOf x ≠ τ) → gram P0.fam τ Y = 0) (y : ℕ → ℂ)
    (hcoord : ∀ v, gram P0.fam (D.tup v) Y = ∑ j : Fin (D.m v), y (D.off v + j.val) • D.WSW v j)
    (ell : (l : Fin 5) → Fin 5 → Matrix (Fin (dpad l)) (Fin (dpad l)) ℂ) :
    ∑ τ : Tup P0.fam, pairing (kronR fun l => ell l (τ l)) (gram P0.fam τ Y) =
      ∑ v, ∑ j : Fin (D.m v), y (D.off v + j.val) *
        ∑ c : Fin (D.nc v), pairing (kronR fun l => ell l (D.new v c l)) (reindexMI (D.perm v c) (D.WSW v j)) := by
  have e1 : ∀ τ : Tup P0.fam, pairing (kronR fun l => ell l (τ l)) (gram P0.fam τ Y) = ∑ x : D.I,
      if D.newOf x = τ then
        pairing (kronR fun l => ell l (D.newOf x l)) (reindexMI (D.perm x.1 x.2) (gram P0.fam (D.tup x.1) Y))
      else 0 := by
    intro τ
    rw [gram_decomp P0 D hcos hinj hsym hout τ, pairing_finsum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [pairing_ite]
    split_ifs with h
    · rw [h]
    · rfl
  rw [Finset.sum_congr rfl fun τ _ => e1 τ, Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [OrbitData.newOf, hcoord v, reindexMI_sum, pairing_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]

end NPT.CP3
