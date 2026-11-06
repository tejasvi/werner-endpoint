/-
NPT.Cert.EqLocal — the local kernels of the equality functionals: partial trace over a replica with
survivors relabelled (`delK`, ep3core 'del'), and the Stiefel contrast on the auxiliary qubit
(`stK = 2·id − del†∘del`, ep3core 'stiefel_aux'); their action on selection operators.
-/
import NPT.Cert.EqMaps

open Matrix BigOperators Finset NPT.Brauer

namespace NPT.Cert

variable {n : ℕ}

/-- Partial trace over replica `sl`, survivor `u` = old replica `ordF u`. -/
def delK (sl : Fin 4) (ordF : Fin 3 → Fin 4) : LKer n 3 :=
  fun i' j' i j => if i ∘ ordF = i' ∧ j ∘ ordF = j' ∧ i sl = j sl then 1 else 0

/-- Identity kernel. -/
def idK : LKer n 4 := fun i' j' i j => if i = i' ∧ j = j' then 1 else 0

/-- `I_sl ⊗ Tr_sl` (survivors in the order `ordF`), the kernel of `del† ∘ del`. -/
def etK (sl : Fin 4) (ordF : Fin 3 → Fin 4) : LKer n 4 :=
  fun i' j' i j => if i' sl = j' sl ∧ i ∘ ordF = i' ∘ ordF ∧ j ∘ ordF = j' ∘ ordF ∧ i sl = j sl then 1 else 0

/-- Stiefel contrast `2 M − I_sl ⊗ Tr_sl M`. -/
def stK (sl : Fin 4) (ordF : Fin 3 → Fin 4) : LKer n 4 :=
  fun i' j' i j => 2 * idK i' j' i j - etK sl ordF i' j' i j

/-- A kernel applied to a selection operator: the sums over the input indices collapse. -/
lemma applyK_SelOp {mo : ℕ} (κ : LKer n mo) (α β : Fin 4 → Fin 4) (i' j' : Dig n mo) :
    applyK κ (SelOp ℂ n α β) i' j' = ∑ x : Dig n 4, κ i' j' (x ∘ α) (x ∘ β) := by
  have hS : ∀ i j, SelOp ℂ n α β i j = ∑ x : Dig n 4, if x ∘ α = i ∧ x ∘ β = j then (1 : ℂ) else 0 := by
    intro i j; simp only [SelOp, Matrix.sum_apply, single_apply]
  simp only [applyK, hS, Finset.mul_sum]
  calc ∑ i : Dig n 4, ∑ j : Dig n 4, ∑ x : Dig n 4,
        κ i' j' i j * (if x ∘ α = i ∧ x ∘ β = j then (1 : ℂ) else 0)
      = ∑ i : Dig n 4, ∑ x : Dig n 4, ∑ j : Dig n 4,
        κ i' j' i j * (if x ∘ α = i ∧ x ∘ β = j then (1 : ℂ) else 0) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ x : Dig n 4, ∑ i : Dig n 4, ∑ j : Dig n 4,
        κ i' j' i j * (if x ∘ α = i ∧ x ∘ β = j then (1 : ℂ) else 0) := Finset.sum_comm
    _ = ∑ x : Dig n 4, κ i' j' (x ∘ α) (x ∘ β) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_eq_single (x ∘ α)]
        · rw [Finset.sum_eq_single (x ∘ β)]
          · simp
          · intro j _ hj; simp [Ne.symm hj]
          · simp
        · intro i _ hi
          exact Finset.sum_eq_zero fun j _ => by simp [Ne.symm hi]
        · simp

/-- Adjoint kernels applied to a selection operator. -/
lemma applyA_SelOp {mo : ℕ} (κ : LKer n mo) (α β : Fin mo → Fin mo) (i j : Dig n 4) :
    applyA κ (SelOp ℂ n α β) i j = ∑ y : Dig n mo, adjK κ i j (y ∘ α) (y ∘ β) := by
  have hS : ∀ i' j', SelOp ℂ n α β i' j' = ∑ y : Dig n mo, if y ∘ α = i' ∧ y ∘ β = j' then (1 : ℂ) else 0 := by
    intro i' j'; simp only [SelOp, Matrix.sum_apply, single_apply]
  simp only [applyA, hS, Finset.mul_sum]
  calc ∑ i' : Dig n mo, ∑ j' : Dig n mo, ∑ y : Dig n mo,
        adjK κ i j i' j' * (if y ∘ α = i' ∧ y ∘ β = j' then (1 : ℂ) else 0)
      = ∑ i' : Dig n mo, ∑ y : Dig n mo, ∑ j' : Dig n mo,
        adjK κ i j i' j' * (if y ∘ α = i' ∧ y ∘ β = j' then (1 : ℂ) else 0) :=
        Finset.sum_congr rfl fun i' _ => Finset.sum_comm
    _ = ∑ y : Dig n mo, ∑ i' : Dig n mo, ∑ j' : Dig n mo,
        adjK κ i j i' j' * (if y ∘ α = i' ∧ y ∘ β = j' then (1 : ℂ) else 0) := Finset.sum_comm
    _ = ∑ y : Dig n mo, adjK κ i j (y ∘ α) (y ∘ β) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_eq_single (y ∘ α)]
        · rw [Finset.sum_eq_single (y ∘ β)]
          · simp
          · intro j' _ hj; simp [Ne.symm hj]
          · simp
        · intro i' _ hi
          exact Finset.sum_eq_zero fun j' _ => by simp [Ne.symm hi]
        · simp

/-- **Partial trace of a selection operator** as a constrained sum (one constraint). -/
lemma delK_SelOp (sl : Fin 4) (ordF : Fin 3 → Fin 4) (α β : Fin 4 → Fin 4) :
    applyK (delK (n := n) sl ordF) (SelOp ℂ n α β) =
      CSum ℂ n (fun _ : Fin 1 => (α sl, β sl)) (α ∘ ordF) (β ∘ ordF) := by
  ext i' j'
  rw [applyK_SelOp]
  simp only [CSum, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : x (α sl) = x (β sl)
  · have h' : ∀ _ : Fin 1, x (α sl) = x (β sl) := fun _ => h
    rw [ite_eq_left h']
    simp only [delK, single_apply, Function.comp_apply, h, and_true]
    rfl
  · have h' : ¬ ∀ _ : Fin 1, x (α sl) = x (β sl) := fun hh => h (hh 0)
    rw [ite_eq_right h']
    simp only [delK, Function.comp_apply, h, and_false, if_false, Matrix.zero_apply]

/-- A traced slot with its survivor enumeration (`ordF : Fin 3 → Fin 4` a bijection onto the other slots). -/
structure SlotOrd where
  sl : Fin 4
  ordF : Fin 3 → Fin 4
  ordInv : Fin 4 → Fin 3
  h1 : ∀ u, ordF u ≠ sl
  h2 : ∀ u, ordInv (ordF u) = u
  h3 : ∀ t, t ≠ sl → ordF (ordInv t) = t

namespace SlotOrd

variable (so : SlotOrd)

/-- `i ↦ (i sl, i ∘ ordF)`. -/
def split : (Fin 4 → Fin n) ≃ Fin n × (Fin 3 → Fin n) where
  toFun i := (i so.sl, i ∘ so.ordF)
  invFun zy t := if t = so.sl then zy.1 else zy.2 (so.ordInv t)
  left_inv i := by
    funext t
    by_cases ht : t = so.sl
    · simp [ht]
    · simp [ht, so.h3 t ht]
  right_inv zy := by
    obtain ⟨z, y⟩ := zy
    simp only [Prod.mk.injEq, if_pos]
    refine ⟨by simp, ?_⟩
    funext u
    simp [so.h1 u, so.h2 u]

/-- Variable layout of the embedded operator: slot `sl` holds the new variable. -/
def emb (α : Fin 3 → Fin 3) (t : Fin 4) : Fin 4 := if t = so.sl then so.sl else so.ordF (α (so.ordInv t))

lemma split_symm_emb (α : Fin 3 → Fin 3) (x : Fin 4 → Fin n) :
    x ∘ so.emb α = so.split.symm ((so.split x).1, (so.split x).2 ∘ α) := by
  funext t
  by_cases ht : t = so.sl
  · simp [emb, split, ht]
  · simp [emb, split, ht]

/-- **The adjoint of the partial trace** maps a three-replica selection operator to a four-replica one. -/
lemma adj_delK_SelOp (α β : Fin 3 → Fin 3) :
    applyA (delK (n := n) so.sl so.ordF) (SelOp ℂ n α β) = SelOp ℂ n (so.emb α) (so.emb β) := by
  ext i j
  rw [applyA_SelOp]
  simp only [SelOp, Matrix.sum_apply, single_apply, adjK, delK]
  rw [← Fintype.sum_equiv (so.split (n := n)).symm
      (fun p => if (so.split.symm p) ∘ so.emb α = i ∧ (so.split.symm p) ∘ so.emb β = j then (1 : ℂ) else 0)
      (fun x => if x ∘ so.emb α = i ∧ x ∘ so.emb β = j then (1 : ℂ) else 0) (fun _ => rfl)]
  simp only [split_symm_emb, Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  have key : ∀ z : Fin n, (so.split.symm (z, y ∘ α) = i ∧ so.split.symm (z, y ∘ β) = j) ↔
      (z = i so.sl ∧ (i ∘ so.ordF = y ∘ α ∧ j ∘ so.ordF = y ∘ β ∧ i so.sl = j so.sl)) := by
    intro z
    rw [Equiv.symm_apply_eq, Equiv.symm_apply_eq]
    simp only [split, Equiv.coe_fn_mk, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h1, h2.symm, h4.symm, h1.symm.trans h3⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h2.symm⟩, h1.trans h4, h3.symm⟩
  simp only [key, ite_and]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  split_ifs <;> simp

end SlotOrd

end NPT.Cert
