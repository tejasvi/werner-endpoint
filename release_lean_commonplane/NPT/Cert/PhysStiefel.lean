/-
NPT.Cert.PhysStiefel — the Stiefel identities on physical points (helper task H3b): with the kernel family
`stF sl ordF` (`I_sl ⊗ Tr_sl` on the sites, the contrast `stK = 2·id − I_sl ⊗ Tr_sl` on the auxiliary
qubit) and `a = vecOf A` with `Aᴴ A = c·1`, `applyG (stF sl ordF) X_f = 0` whenever replica `sl` of the
family pattern carries `a`: families `31` and `22` with `sl = 0`, family `13` with `sl = 3`.

Route: split every factor index as (replica `sl`, survivors) (`gsplit`); the kernel pins the survivors, so
`applyG stF |w⟩⟨w|` is the survivor operator times the scalar `Σ_{v,v'} Π_l g_l(v_l, v'_l) a(v) ā(v')`.
On the sites `g` forces `v = v'`, which leaves `Tr_sites |a⟩⟨a| = Aᴴ A = c·1` on the aux qubit, where
`2·(c·1) − (2c)·1 = 0` (`aux_contrast`).
-/
import NPT.Cert.EqLocal
import NPT.Cert.Phys

open Matrix BigOperators Finset NPT.Brauer NPT.Cert.Sem

namespace NPT.Cert.Phys

variable {k d : ℕ}

/-- Kernel family of the Stiefel identities: `I_sl ⊗ Tr_sl` (`etK`) on the sites, the Stiefel contrast
`stK = 2·id − etK` on the auxiliary qubit. -/
def stF (sl : Fin 4) (ordF : Fin 3 → Fin 4) : (l : Fin (k + 1)) → LKer (nf k d l) 4 :=
  fun l => if l.val < k then etK sl ordF else stK sl ordF

namespace Stiefel

/-- Slot `0`, survivors `1, 2, 3`. -/
def so0 : SlotOrd where
  sl := 0
  ordF := ![1, 2, 3]
  ordInv := ![0, 0, 1, 2]
  h1 := by decide
  h2 := by decide
  h3 := by decide

/-- Slot `3`, survivors `0, 1, 2`. -/
def so3 : SlotOrd where
  sl := 3
  ordF := ![0, 1, 2]
  ordInv := ![0, 1, 2, 0]
  h1 := by decide
  h2 := by decide
  h3 := by decide

lemma split_symm_sl (so : SlotOrd) {n : ℕ} (z : Fin n) (y : Fin 3 → Fin n) :
    so.split.symm (z, y) so.sl = z :=
  congrArg Prod.fst (so.split.apply_symm_apply (z, y))

lemma split_symm_ord (so : SlotOrd) {n : ℕ} (z : Fin n) (y : Fin 3 → Fin n) :
    so.split.symm (z, y) ∘ so.ordF = y :=
  congrArg Prod.snd (so.split.apply_symm_apply (z, y))

lemma split_symm_eq_iff (so : SlotOrd) {n : ℕ} (z : Fin n) (y : Fin 3 → Fin n) (x : Fin 4 → Fin n) :
    so.split.symm (z, y) = x ↔ z = x so.sl ∧ y = x ∘ so.ordF := by
  rw [Equiv.symm_apply_eq]
  exact Prod.mk.injEq _ _ _ _ ▸ Iff.rfl

/-- `I_sl ⊗ Tr_sl` in split coordinates. -/
lemma etK_split (so : SlotOrd) {n : ℕ} (i' j' : Fin 4 → Fin n) (z z' : Fin n) (y y' : Fin 3 → Fin n) :
    etK so.sl so.ordF i' j' (so.split.symm (z, y)) (so.split.symm (z', y')) =
      if y = i' ∘ so.ordF ∧ y' = j' ∘ so.ordF then
        (if i' so.sl = j' so.sl ∧ z = z' then 1 else 0) else 0 := by
  simp only [etK, split_symm_sl, split_symm_ord]
  split_ifs <;> first | rfl | (exfalso; tauto)

/-- The identity kernel in split coordinates. -/
lemma idK_split (so : SlotOrd) {n : ℕ} (i' j' : Fin 4 → Fin n) (z z' : Fin n) (y y' : Fin 3 → Fin n) :
    idK i' j' (so.split.symm (z, y)) (so.split.symm (z', y')) =
      if y = i' ∘ so.ordF ∧ y' = j' ∘ so.ordF then
        (if z = i' so.sl ∧ z' = j' so.sl then 1 else 0) else 0 := by
  simp only [idK, split_symm_eq_iff]
  split_ifs <;> first | rfl | (exfalso; tauto)

/-- The Stiefel kernel in split coordinates. -/
lemma stK_split (so : SlotOrd) {n : ℕ} (i' j' : Fin 4 → Fin n) (z z' : Fin n) (y y' : Fin 3 → Fin n) :
    stK so.sl so.ordF i' j' (so.split.symm (z, y)) (so.split.symm (z', y')) =
      if y = i' ∘ so.ordF ∧ y' = j' ∘ so.ordF then
        2 * (if z = i' so.sl ∧ z' = j' so.sl then 1 else 0) -
          (if i' so.sl = j' so.sl ∧ z = z' then 1 else 0) else 0 := by
  rw [stK, idK_split, etK_split]
  split_ifs <;> ring

/-- Local scalar of the kernel family `stF` (sites: `I_sl ⊗ Tr_sl`; aux: `2·id − I_sl ⊗ Tr_sl`). -/
def gSt (l : Fin (k + 1)) (sl : Fin 4) (i' j' : Fin 4 → Fin (nf k d l)) (z z' : Fin (nf k d l)) : ℂ :=
  if l.val < k then (if i' sl = j' sl ∧ z = z' then 1 else 0)
  else 2 * (if z = i' sl ∧ z' = j' sl then 1 else 0) - (if i' sl = j' sl ∧ z = z' then 1 else 0)

lemma stF_split (so : SlotOrd) (l : Fin (k + 1)) (i' j' : Fin 4 → Fin (nf k d l))
    (z z' : Fin (nf k d l)) (y y' : Fin 3 → Fin (nf k d l)) :
    stF so.sl so.ordF l i' j' (so.split.symm (z, y)) (so.split.symm (z', y')) =
      if y = i' ∘ so.ordF ∧ y' = j' ∘ so.ordF then gSt l so.sl i' j' z z' else 0 := by
  by_cases hl : l.val < k
  · simp only [stF, gSt, hl, ite_true, etK_split]
  · simp only [stF, gSt, hl, ite_false, stK_split]

variable (k d) in
/-- Factorwise split `i ↦ (replica sl, survivors)`. -/
def gsplit (so : SlotOrd) : GI (nf k d) ≃ V1 k d × GO (nf k d) (fun _ => 3) :=
  (Equiv.piCongrRight fun l => so.split (n := nf k d l)).trans (Equiv.arrowProdEquivProdArrow _ _ _)

lemma gsplit_symm_apply (so : SlotOrd) (v : V1 k d) (y : GO (nf k d) (fun _ => 3)) (l : Fin (k + 1)) :
    (gsplit k d so).symm (v, y) l = so.split.symm (v l, y l) := rfl

lemma sum_gsplit (so : SlotOrd) (f : GI (nf k d) → ℂ) :
    ∑ i, f i = ∑ v, ∑ y, f ((gsplit k d so).symm (v, y)) := by
  rw [← (gsplit k d so).symm.sum_comp, Fintype.sum_prod_type]

/-- The global kernel `stF` in split coordinates: the survivors are pinned, the traced replica
carries the local scalars `gSt`. -/
lemma prod_stF_gsplit (so : SlotOrd) (i' j' : GI (nf k d)) (v v' : V1 k d)
    (y y' : GO (nf k d) (fun _ => 3)) :
    ∏ l, stF so.sl so.ordF l (i' l) (j' l) ((gsplit k d so).symm (v, y) l)
        ((gsplit k d so).symm (v', y') l) =
      if y = (fun l => i' l ∘ so.ordF) ∧ y' = (fun l => j' l ∘ so.ordF) then
        ∏ l, gSt l so.sl (i' l) (j' l) (v l) (v' l) else 0 := by
  simp only [gsplit_symm_apply, stF_split]
  rw [Fintype.prod_ite_zero]
  simp only [funext_iff, forall_and]

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

lemma patVec_gsplit (so : SlotOrd) (p : Fin 4 → Fin 4) (a b : V1 k d → ℂ) (v : V1 k d)
    (y : GO (nf k d) (fun _ => 3)) :
    patVec p a b ((gsplit k d so).symm (v, y)) =
      chi (p so.sl) a b v * ∏ u, chi (p (so.ordF u)) a b (fun l => y l u) := by
  have hsl : repl ((gsplit k d so).symm (v, y)) so.sl = v := by
    funext l; exact split_symm_sl so (v l) (y l)
  have hord : ∀ u, repl ((gsplit k d so).symm (v, y)) (so.ordF u) = fun l => y l u := by
    intro u; funext l; exact congrFun (split_symm_ord so (v l) (y l)) u
  rw [patVec, prod_slot so, hsl]
  simp only [hord]

/-- Collapse of two pinned summation variables. -/
lemma sum_collapse {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [DecidableEq β] [DecidableEq δ] (F : α → β → γ → δ → ℂ) (b0 : β) (e0 : δ) :
    ∑ a, ∑ b, ∑ c, ∑ e, (if b = b0 ∧ e = e0 then F a b c e else 0) = ∑ a, ∑ c, F a b0 c e0 := by
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_eq_single b0]
  · simp
  · intro b hb; simp [hb]

/-- Collapse of a diagonal pair of summation variables. -/
lemma sum_diag {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α]
    (F : α → β → α → γ → ℂ) :
    ∑ x, ∑ b, ∑ x', ∑ c, (if x = x' then F x b x' c else 0) = ∑ x, ∑ b, ∑ c, F x b x c := by
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Fintype.sum_eq_single x]
  · simp
  · intro x' hx'; simp [Ne.symm hx']

variable (k d) in
/-- Site/auxiliary decomposition `V1 ≃ (Fin k → Fin d) × Fin 2`. -/
def siteAux : V1 k d ≃ (Fin k → Fin d) × Fin 2 :=
  (Fin.snocEquiv fun l => Fin (nf k d l)).symm.trans
    (((finCongr (nf_aux k d)).prodCongr (Equiv.piCongrRight fun s => finCongr (nf_site k d s))).trans
      (Equiv.prodComm _ _))

lemma siteAux_apply (v : V1 k d) : siteAux k d v = (sitePart v, auxPart v) := rfl

lemma sitePart_siteAux_symm (x : Fin k → Fin d) (α : Fin 2) :
    sitePart ((siteAux k d).symm (x, α)) = x :=
  congrArg Prod.fst ((siteAux k d).apply_symm_apply (x, α))

lemma auxPart_siteAux_symm (x : Fin k → Fin d) (α : Fin 2) :
    auxPart ((siteAux k d).symm (x, α)) = α :=
  congrArg Prod.snd ((siteAux k d).apply_symm_apply (x, α))

lemma sum_V1 (f : V1 k d → ℂ) : ∑ v, f v = ∑ x, ∑ α, f ((siteAux k d).symm (x, α)) := by
  rw [← (siteAux k d).symm.sum_comp, Fintype.sum_prod_type]

/-- Aux factor of the Stiefel scalar: `2 δ_{α α0} δ_{α' β0} − δ_{α0 β0} δ_{α α'}`. -/
def gaux (α0 β0 α α' : Fin 2) : ℂ :=
  2 * (if α = α0 ∧ α' = β0 then 1 else 0) - (if α0 = β0 ∧ α = α' then 1 else 0)

/-- The local scalars of `stF` through the site/aux parts of the traced replica. -/
lemma prod_gSt (sl : Fin 4) (i' j' : GI (nf k d)) (v v' : V1 k d) :
    ∏ l, gSt l sl (i' l) (j' l) (v l) (v' l) =
      if (∀ s : Fin k, i' s.castSucc sl = j' s.castSucc sl) ∧ sitePart v = sitePart v' then
        gaux (Fin.cast (nf_aux k d) (i' (Fin.last k) sl)) (Fin.cast (nf_aux k d) (j' (Fin.last k) sl))
          (auxPart v) (auxPart v')
      else 0 := by
  rw [Fin.prod_univ_castSucc]
  have hs : ∀ s : Fin k, gSt s.castSucc sl (i' s.castSucc) (j' s.castSucc) (v s.castSucc) (v' s.castSucc) =
      if i' s.castSucc sl = j' s.castSucc sl ∧ sitePart v s = sitePart v' s then 1 else 0 := by
    intro s
    simp only [gSt, Fin.val_castSucc, s.isLt, ite_true, sitePart, Fin.cast_inj]
  have ha : gSt (Fin.last k) sl (i' (Fin.last k)) (j' (Fin.last k)) (v (Fin.last k)) (v' (Fin.last k)) =
      gaux (Fin.cast (nf_aux k d) (i' (Fin.last k) sl)) (Fin.cast (nf_aux k d) (j' (Fin.last k) sl))
        (auxPart v) (auxPart v') := by
    simp only [gSt, gaux, Fin.val_last, lt_self_iff_false, ite_false, auxPart, Fin.cast_inj]
  rw [ha]
  simp only [hs]
  rw [Fintype.prod_boole]
  simp only [forall_and, funext_iff, ite_mul, one_mul, zero_mul]

/-- `Tr_sites |a⟩⟨a| = c·1` kills the aux contrast. -/
lemma aux_contrast (A : Matrix (Fin k → Fin d) (Fin 2) ℂ) (c : ℝ) (hA : Aᴴ * A = (c : ℂ) • 1)
    (α0 β0 : Fin 2) :
    ∑ x, ∑ α, ∑ α', gaux α0 β0 α α' * (A x α * star (A x α')) = 0 := by
  have hcol : ∀ α α', ∑ x, A x α * star (A x α') = if α = α' then (c : ℂ) else 0 := by
    intro α α'
    have h := congrFun (congrFun hA α') α
    simp only [mul_apply, conjTranspose_apply, Matrix.smul_apply, one_apply, smul_eq_mul] at h
    rw [Finset.sum_congr rfl fun x _ => mul_comm (A x α) (star (A x α')), h]
    by_cases hαα : α = α'
    · subst hαα; simp
    · simp [hαα, Ne.symm hαα]
  calc ∑ x, ∑ α, ∑ α', gaux α0 β0 α α' * (A x α * star (A x α'))
      = ∑ α, ∑ α', gaux α0 β0 α α' * ∑ x, A x α * star (A x α') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun α _ => ?_
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ = 0 := by
        simp only [hcol, Fin.sum_univ_two, gaux]
        fin_cases α0 <;> fin_cases β0 <;> simp <;> ring

/-- The scalar factor of `applyG stF |w⟩⟨w|` vanishes when the traced replica carries `a = vecOf A`
with `Aᴴ A = c·1`. -/
lemma stiefel_scalar (sl : Fin 4) (i' j' : GI (nf k d)) (A : Matrix (Fin k → Fin d) (Fin 2) ℂ) (c : ℝ)
    (hA : Aᴴ * A = (c : ℂ) • 1) :
    ∑ v : V1 k d, ∑ v' : V1 k d,
      (∏ l, gSt l sl (i' l) (j' l) (v l) (v' l)) * (vecOf A v * star (vecOf A v')) = 0 := by
  simp only [prod_gSt, ite_mul, zero_mul, sum_V1, vecOf, sitePart_siteAux_symm, auxPart_siteAux_symm]
  by_cases hD : ∀ s : Fin k, i' s.castSucc sl = j' s.castSucc sl
  · simp only [hD, implies_true, true_and]
    rw [sum_diag]
    exact aux_contrast A c hA _ _
  · simp only [hD, false_and, ite_false, Finset.sum_const_zero]

/-- **Stiefel identity** for any row pattern whose traced replica carries `a = vecOf A`. -/
theorem applyG_stF_patVec (so : SlotOrd) (p : Fin 4 → Fin 4) (hp : p so.sl = 0)
    (A : Matrix (Fin k → Fin d) (Fin 2) ℂ) (c : ℝ) (hA : Aᴴ * A = (c : ℂ) • 1) (b : V1 k d → ℂ) :
    applyG (stF so.sl so.ordF) (vecMulVec (patVec p (vecOf A) b) (star (patVec p (vecOf A) b))) = 0 := by
  ext i' j'
  simp only [applyG, vecMulVec_apply, Pi.star_apply, Matrix.zero_apply]
  simp only [sum_gsplit so, prod_stF_gsplit, ite_mul, zero_mul]
  rw [sum_collapse]
  simp only [patVec_gsplit, hp]
  have hchi : ∀ v, chi 0 (vecOf A) b v = vecOf A v := fun v => rfl
  simp only [hchi]
  set Ri := ∏ u, chi (p (so.ordF u)) (vecOf A) b (fun l => (fun l => i' l ∘ so.ordF) l u)
  set Rj := ∏ u, chi (p (so.ordF u)) (vecOf A) b (fun l => (fun l => j' l ∘ so.ordF) l u)
  have e : ∀ v v' : V1 k d, (∏ l, gSt l so.sl (i' l) (j' l) (v l) (v' l)) *
      (vecOf A v * Ri * star (vecOf A v' * Rj)) =
      (∏ l, gSt l so.sl (i' l) (j' l) (v l) (v' l)) * (vecOf A v * star (vecOf A v')) *
        (Ri * star Rj) := by
    intro v v'; rw [star_mul']; ring
  simp only [e, ← Finset.sum_mul]
  rw [stiefel_scalar so.sl i' j' A c hA, zero_mul]

end Stiefel

open Stiefel in
/-- Stiefel identity, family `31` (`aaab`), traced replica `0`. -/
theorem stiefel31_phys (A : Matrix (Fin k → Fin d) (Fin 2) ℂ) (c : ℝ) (hA : Aᴴ * A = (c : ℂ) • 1)
    (b : V1 k d → ℂ) : applyG (stF 0 ![1, 2, 3]) (Xf 0 (vecOf A) b) = 0 :=
  applyG_stF_patVec so0 (famPat 0) rfl A c hA b

open Stiefel in
/-- Stiefel identity, family `22` (`aabb`), traced replica `0`. -/
theorem stiefel22_phys (A : Matrix (Fin k → Fin d) (Fin 2) ℂ) (c : ℝ) (hA : Aᴴ * A = (c : ℂ) • 1)
    (b : V1 k d → ℂ) : applyG (stF 0 ![1, 2, 3]) (Xf 1 (vecOf A) b) = 0 :=
  applyG_stF_patVec so0 (famPat 1) rfl A c hA b

open Stiefel in
/-- Stiefel identity, family `13` (`bbba`), traced replica `3`. -/
theorem stiefel13_phys (A : Matrix (Fin k → Fin d) (Fin 2) ℂ) (c : ℝ) (hA : Aᴴ * A = (c : ℂ) • 1)
    (b : V1 k d → ℂ) : applyG (stF 3 ![0, 1, 2]) (Xf 2 (vecOf A) b) = 0 :=
  applyG_stF_patVec so3 (famPat 2) rfl A c hA b

end NPT.Cert.Phys
