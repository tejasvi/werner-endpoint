/-
NPT.Cert.PhysEq — the marginal (partial-trace) identities on physical points: tracing one replica of a
product rank-one operator `|⊗_r φ_r⟩⟨⊗_r φ_r|` gives `‖φ_sl‖² · |⊗_u φ_{ordF u}⟩⟨…|`; hence, when
`‖a‖ = ‖b‖`, `Tr_2 X_31 = Tr_2 X_22` (survivors `0, 1, 3`) and `Tr_1 X_22 = Tr_1 X_13` (survivors `0, 2, 3`
resp. `3, 0, 2`).
-/
import NPT.Cert.EqLocal
import NPT.Cert.Phys

open Matrix BigOperators Finset NPT.Brauer NPT.Cert.Sem

namespace NPT.Cert.Phys

/-- Survivor orders of the marginal identities. -/
abbrev o013 : Fin 3 → Fin 4 := ![0, 1, 3]
abbrev o023 : Fin 3 → Fin 4 := ![0, 2, 3]
abbrev o302 : Fin 3 → Fin 4 := ![3, 0, 2]

/-! Helper lemmas live in `NPT.Cert.Phys.Marg`. -/
namespace Marg

/-- Slot `2`, survivors `0, 1, 3`. -/
def so013 : SlotOrd where
  sl := 2
  ordF := o013
  ordInv := ![0, 1, 0, 2]
  h1 := by decide
  h2 := by decide
  h3 := by decide

/-- Slot `1`, survivors `0, 2, 3`. -/
def so023 : SlotOrd where
  sl := 1
  ordF := o023
  ordInv := ![0, 0, 1, 2]
  h1 := by decide
  h2 := by decide
  h3 := by decide

/-- Slot `1`, survivors `3, 0, 2`. -/
def so302 : SlotOrd where
  sl := 1
  ordF := o302
  ordInv := ![1, 0, 2, 0]
  h1 := by decide
  h2 := by decide
  h3 := by decide

lemma prod_slot (so : SlotOrd) {M : Type*} [CommMonoid M] (f : Fin 4 → M) :
    ∏ r, f r = f so.sl * ∏ u, f (so.ordF u) := by
  rw [← Finset.mul_prod_erase univ f (Finset.mem_univ so.sl)]
  congr 1
  refine Finset.prod_nbij' so.ordInv so.ordF ?_ ?_ ?_ ?_ ?_
  · intros; exact Finset.mem_univ _
  · intro u _; simp [so.h1 u]
  · intro t ht; exact so.h3 t (Finset.ne_of_mem_erase ht)
  · intro u _; exact so.h2 u
  · intro t ht; rw [so.h3 t (Finset.ne_of_mem_erase ht)]

lemma split_symm_sl (so : SlotOrd) {n : ℕ} (z : Fin n) (y : Fin 3 → Fin n) :
    so.split.symm (z, y) so.sl = z :=
  congrArg Prod.fst (so.split.apply_symm_apply (z, y))

lemma split_symm_ord (so : SlotOrd) {n : ℕ} (z : Fin n) (y : Fin 3 → Fin n) :
    so.split.symm (z, y) ∘ so.ordF = y :=
  congrArg Prod.snd (so.split.apply_symm_apply (z, y))

variable {k d : ℕ}

/-- Product vector of three letters on three replicas. -/
def w3 (q : Fin 3 → Fin 4) (a b : V1 k d → ℂ) (i' : GO (nf k d) (fun _ => 3)) : ℂ :=
  ∏ u : Fin 3, chi (q u) a b (fun l => i' l u)

variable (k d) in
/-- Factorwise split `i ↦ (replica sl, survivors)`. -/
def gsplit (so : SlotOrd) : GI (nf k d) ≃ V1 k d × GO (nf k d) (fun _ => 3) :=
  (Equiv.piCongrRight fun l => so.split (n := nf k d l)).trans (Equiv.arrowProdEquivProdArrow _ _ _)

lemma gsplit_symm_apply (so : SlotOrd) (v : V1 k d) (y : GO (nf k d) (fun _ => 3)) (l : Fin (k + 1)) :
    (gsplit k d so).symm (v, y) l = so.split.symm (v l, y l) := rfl

lemma sum_gsplit (so : SlotOrd) (f : GI (nf k d) → ℂ) :
    ∑ i, f i = ∑ v, ∑ y, f ((gsplit k d so).symm (v, y)) := by
  rw [← (gsplit k d so).symm.sum_comp, Fintype.sum_prod_type]

lemma patVec_gsplit (so : SlotOrd) (p : Fin 4 → Fin 4) (a b : V1 k d → ℂ) (v : V1 k d)
    (y : GO (nf k d) (fun _ => 3)) :
    patVec p a b ((gsplit k d so).symm (v, y)) = chi (p so.sl) a b v * w3 (p ∘ so.ordF) a b y := by
  have hsl : repl ((gsplit k d so).symm (v, y)) so.sl = v := by
    funext l; exact split_symm_sl so (v l) (y l)
  have hord : ∀ u, repl ((gsplit k d so).symm (v, y)) (so.ordF u) = fun l => y l u := by
    intro u; funext l; exact congrFun (split_symm_ord so (v l) (y l)) u
  rw [patVec, prod_slot so, hsl]
  simp only [hord, w3, Function.comp]

lemma prod_delK_gsplit (so : SlotOrd) (i' j' y y' : GO (nf k d) (fun _ => 3)) (v v' : V1 k d) :
    ∏ l, delK (n := nf k d l) so.sl so.ordF (i' l) (j' l) ((gsplit k d so).symm (v, y) l)
        ((gsplit k d so).symm (v', y') l) =
      if y = i' ∧ y' = j' ∧ v = v' then 1 else 0 := by
  simp only [delK, gsplit_symm_apply, split_symm_sl, split_symm_ord]
  rw [Fintype.prod_boole]
  by_cases h : y = i' ∧ y' = j' ∧ v = v'
  · obtain ⟨rfl, rfl, rfl⟩ := h
    rw [ite_eq_left (fun l => ⟨rfl, rfl, rfl⟩), ite_eq_left ⟨rfl, rfl, rfl⟩]
  · rw [ite_eq_right h, ite_eq_right]
    intro hl
    exact h ⟨funext fun l => (hl l).1, funext fun l => (hl l).2.1, funext fun l => (hl l).2.2⟩

lemma sum4_collapse {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (i' j' : β)
    (F : α → β → α → β → ℂ) :
    ∑ v, ∑ y, ∑ v', ∑ y', (if y = i' ∧ y' = j' ∧ v = v' then (1 : ℂ) else 0) * F v y v' y' =
      ∑ v, F v i' v j' := by
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_eq_single i']
  · rw [Finset.sum_eq_single v]
    · rw [Finset.sum_eq_single j']
      · simp
      · intro y' _ hy'; simp [hy']
      · simp
    · intro v' _ hv'; exact Finset.sum_eq_zero fun y' _ => by simp [Ne.symm hv']
    · simp
  · intro y _ hy; exact Finset.sum_eq_zero fun v' _ => Finset.sum_eq_zero fun y' _ => by simp [hy]
  · simp

/-- **Partial trace of a product rank-one operator** over replica `so.sl`. -/
lemma applyG_delK_rank1 (so : SlotOrd) (p : Fin 4 → Fin 4) (a b : V1 k d → ℂ) :
    applyG (fun l => delK (n := nf k d l) so.sl so.ordF) (vecMulVec (patVec p a b) (star (patVec p a b))) =
      (∑ v, chi (p so.sl) a b v * star (chi (p so.sl) a b v)) •
        vecMulVec (w3 (p ∘ so.ordF) a b) (star (w3 (p ∘ so.ordF) a b)) := by
  ext i' j'
  simp only [applyG, vecMulVec_apply, Pi.star_apply, Matrix.smul_apply, smul_eq_mul,
    sum_gsplit so, prod_delK_gsplit, patVec_gsplit]
  rw [sum4_collapse, Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [star_mul']
  ring

lemma nsq_eq (a : V1 k d → ℂ) : (nsq k d a : ℂ) = ∑ v, a v * star (a v) := by
  unfold nsq; push_cast
  exact Finset.sum_congr rfl fun v _ => (Complex.mul_conj (a v)).symm

end Marg

open Marg

/-- `Tr_2 |aaab⟩⟨aaab| = Tr_2 |aabb⟩⟨aabb|` (survivors `0, 1, 3`) when `‖a‖ = ‖b‖`. -/
theorem aab_phys {k d : ℕ} (a b : V1 k d → ℂ) (hab : nsq k d a = nsq k d b) :
    applyG (fun _ => delK 2 o013) (Xf 0 a b) = applyG (fun _ => delK 2 o013) (Xf 1 a b) := by
  have e0 : applyG (fun l => delK (n := nf k d l) 2 o013) (Xf 0 a b) =
      (∑ v, a v * star (a v)) • vecMulVec (w3 (famPat 0 ∘ o013) a b) (star (w3 (famPat 0 ∘ o013) a b)) :=
    applyG_delK_rank1 so013 (famPat 0) a b
  have e1 : applyG (fun l => delK (n := nf k d l) 2 o013) (Xf 1 a b) =
      (∑ v, b v * star (b v)) • vecMulVec (w3 (famPat 1 ∘ o013) a b) (star (w3 (famPat 1 ∘ o013) a b)) :=
    applyG_delK_rank1 so013 (famPat 1) a b
  have hq : famPat 0 ∘ o013 = famPat 1 ∘ o013 := by decide
  rw [e0, e1, hq, ← nsq_eq a, ← nsq_eq b, hab]

/-- `Tr_1 |aabb⟩⟨aabb|` (survivors `0, 2, 3`) `= Tr_1 |bbba⟩⟨bbba|` (survivors `3, 0, 2`) when `‖a‖ = ‖b‖`. -/
theorem abb_phys {k d : ℕ} (a b : V1 k d → ℂ) (hab : nsq k d a = nsq k d b) :
    applyG (fun _ => delK 1 o023) (Xf 1 a b) = applyG (fun _ => delK 1 o302) (Xf 2 a b) := by
  have e1 : applyG (fun l => delK (n := nf k d l) 1 o023) (Xf 1 a b) =
      (∑ v, a v * star (a v)) • vecMulVec (w3 (famPat 1 ∘ o023) a b) (star (w3 (famPat 1 ∘ o023) a b)) :=
    applyG_delK_rank1 so023 (famPat 1) a b
  have e2 : applyG (fun l => delK (n := nf k d l) 1 o302) (Xf 2 a b) =
      (∑ v, b v * star (b v)) • vecMulVec (w3 (famPat 2 ∘ o302) a b) (star (w3 (famPat 2 ∘ o302) a b)) :=
    applyG_delK_rank1 so302 (famPat 2) a b
  have hq : famPat 1 ∘ o023 = famPat 2 ∘ o302 := by decide
  rw [e1, e2, hq, ← nsq_eq a, ← nsq_eq b, hab]

end NPT.Cert.Phys

#print axioms NPT.Cert.Phys.aab_phys
#print axioms NPT.Cert.Phys.abb_phys
