/-
NPT.Cert.EqLink — the semantic link of the equality functionals: per word, every factor of `Sem.eqVal` is a
fixed linear functional of the local partial trace (`del`) resp. Stiefel contrast (`stiefel_aux`) of `V_p`,
so coefficient sums of `eqVal` are functionals of the global maps `trKer`, `stKer` at the moment operator
`Σ_w x_w V_w`; the operator identities there give the agreement resp. vanishing of the sums.
-/
import NPT.Cert.EqInt
import NPT.Cert.SemLink

open Matrix BigOperators Finset NPT.Brauer NPT.Cert.Sem

namespace NPT.Cert

namespace EqLink

/-! ### Linear functionals with coefficient matrices -/

/-- `⟨F, Q⟩ = Σ_{i,j} F i j · Q i j`. -/
def pairF {ι : Type*} [Fintype ι] (F : ι → ι → ℂ) (Q : Matrix ι ι ℂ) : ℂ := ∑ i, ∑ j, F i j * Q i j

lemma pairF_add {ι : Type*} [Fintype ι] (F : ι → ι → ℂ) (Q R : Matrix ι ι ℂ) :
    pairF F (Q + R) = pairF F Q + pairF F R := by
  simp only [pairF, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

lemma pairF_smul {ι : Type*} [Fintype ι] (F : ι → ι → ℂ) (a : ℂ) (Q : Matrix ι ι ℂ) :
    pairF F (a • Q) = a * pairF F Q := by
  simp only [pairF, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma pairF_zero {ι : Type*} [Fintype ι] (F : ι → ι → ℂ) : pairF F 0 = 0 := by
  simp [pairF]

lemma pairF_sum {ι α : Type*} [Fintype ι] [DecidableEq α] (F : ι → ι → ℂ) (s : Finset α)
    (Q : α → Matrix ι ι ℂ) : pairF F (∑ a ∈ s, Q a) = ∑ a ∈ s, pairF F (Q a) := by
  induction s using Finset.induction_on with
  | empty => simp [pairF]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pairF_add, ih]

lemma pairF_mul_left {ι : Type*} [Fintype ι] (r : ℂ) (F : ι → ι → ℂ) (Q : Matrix ι ι ℂ) :
    pairF (fun i j => r * F i j) Q = r * pairF F Q := by
  simp only [pairF, Finset.mul_sum, mul_assoc]

/-- Pulling a functional back along a kernel. -/
lemma pairF_applyK {n mo : ℕ} (F : Dig n mo → Dig n mo → ℂ) (κ : LKer n mo)
    (M : Matrix (Dig n 4) (Dig n 4) ℂ) :
    pairF F (applyK κ M) = pairF (fun a b => ∑ x, ∑ y, F x y * κ x y a b) M := by
  unfold pairF applyK
  simp only [Finset.mul_sum, Finset.sum_mul]
  calc ∑ x, ∑ y, ∑ a, ∑ b, F x y * (κ x y a b * M a b)
      = ∑ x, ∑ a, ∑ y, ∑ b, F x y * (κ x y a b * M a b) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ a, ∑ x, ∑ y, ∑ b, F x y * (κ x y a b * M a b) := Finset.sum_comm
    _ = ∑ a, ∑ x, ∑ b, ∑ y, F x y * (κ x y a b * M a b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ x, ∑ y, F x y * (κ x y a b * M a b) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ a, ∑ b, ∑ x, ∑ y, F x y * κ x y a b * M a b := by
        simp only [mul_assoc]

/-- `(Jᵀ A J)[μ, ν] = ⟨J(·, μ) J(·, ν), A⟩`. -/
lemma sandwich_apply {ι κ : Type*} [Fintype ι] (J : Matrix ι κ ℂ) (A : Matrix ι ι ℂ) (μ ν : κ) :
    (Jᵀ * A * J) μ ν = pairF (fun x y => J x μ * J y ν) A := by
  simp only [pairF, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

/-! ### Products over factors -/

section Global

variable {L : Type*} [Fintype L] [DecidableEq L] {nf : L → ℕ} {mo : L → ℕ}

/-- A product of local functionals of `κ_l(V_{w l})` is a functional of `applyG κ (V_w)`. -/
lemma prod_pairF (κ : (l : L) → LKer (nf l) (mo l))
    (F : (l : L) → Dig (nf l) (mo l) → Dig (nf l) (mo l) → ℂ) (w : L → Fin 24) :
    ∏ l, pairF (F l) (applyK (κ l) (VG ℂ (nf l) 0 (w l))) =
      pairF (fun i j : GO nf mo => ∏ l, F l (i l) (j l)) (applyG κ (VW nf 0 w)) := by
  unfold VW
  rw [applyG_kron]
  simp only [pairF, kron, ← Finset.prod_mul_distrib]
  exact (sum_pair_prod (fun l x y => F l x y * applyK (κ l) (VG ℂ (nf l) 0 (w l)) x y)).symm

/-- Linearity in the word. -/
lemma sum_prod_pairF (κ : (l : L) → LKer (nf l) (mo l))
    (F : (l : L) → Dig (nf l) (mo l) → Dig (nf l) (mo l) → ℂ) (x : (L → Fin 24) → ℂ) :
    ∑ w, x w * ∏ l, pairF (F l) (applyK (κ l) (VG ℂ (nf l) 0 (w l))) =
      pairF (fun i j : GO nf mo => ∏ l, F l (i l) (j l)) (applyG κ (∑ w, x w • VW nf 0 w)) := by
  have h : applyG κ (∑ w, x w • VW nf 0 w) = ∑ w, x w • applyG κ (VW nf 0 w) := by
    change applyGL κ (∑ w, x w • VW nf 0 w) = ∑ w, x w • applyGL κ (VW nf 0 w)
    rw [map_sum]
    simp only [map_smul]
  rw [h, pairF_sum]
  simp only [pairF_smul, prod_pairF]

end Global

/-! ### The local partial trace -/

lemma split_symm_sl (so : SlotOrd) {n : ℕ} (z : Fin n) (y : Fin 3 → Fin n) :
    so.split.symm (z, y) so.sl = z :=
  congrArg Prod.fst (so.split.apply_symm_apply (z, y))

lemma split_symm_ord (so : SlotOrd) {n : ℕ} (z : Fin n) (y : Fin 3 → Fin n) :
    so.split.symm (z, y) ∘ so.ordF = y :=
  congrArg Prod.snd (so.split.apply_symm_apply (z, y))

lemma sum_split (so : SlotOrd) {n : ℕ} (f : Dig n 4 → ℂ) :
    ∑ i, f i = ∑ z : Fin n, ∑ y : Dig n 3, f (so.split.symm (z, y)) := by
  rw [← (so.split (n := n)).symm.sum_comp f, Fintype.sum_prod_type]

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

/-- The partial trace as a sum over the traced digit. -/
lemma applyK_delK_apply (so : SlotOrd) {n : ℕ} (M : Matrix (Dig n 4) (Dig n 4) ℂ) (i' j' : Dig n 3) :
    applyK (delK so.sl so.ordF) M i' j' = ∑ z, M (so.split.symm (z, i')) (so.split.symm (z, j')) := by
  simp only [applyK]
  calc ∑ i, ∑ j, delK so.sl so.ordF i' j' i j * M i j
      = ∑ z, ∑ y, ∑ z', ∑ y', delK so.sl so.ordF i' j' (so.split.symm (z, y)) (so.split.symm (z', y')) *
          M (so.split.symm (z, y)) (so.split.symm (z', y')) := by
        rw [sum_split so]
        refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => ?_
        rw [sum_split so]
    _ = ∑ z, ∑ y, ∑ z', ∑ y', (if y = i' ∧ y' = j' ∧ z = z' then (1 : ℂ) else 0) *
          M (so.split.symm (z, y)) (so.split.symm (z', y')) := by
        simp only [delK, split_symm_sl, split_symm_ord]
    _ = ∑ z, M (so.split.symm (z, i')) (so.split.symm (z, j')) :=
        sum4_collapse i' j' (fun z y z' y' => M (so.split.symm (z, y)) (so.split.symm (z', y')))

/-- The adjoint of the partial trace, entrywise. -/
lemma applyA_delK_apply {n : ℕ} (sl : Fin 4) (ordF : Fin 3 → Fin 4) (N : Matrix (Dig n 3) (Dig n 3) ℂ)
    (i j : Dig n 4) :
    applyA (delK sl ordF) N i j = if i sl = j sl then N (i ∘ ordF) (j ∘ ordF) else 0 := by
  simp only [applyA, adjK, delK]
  rw [Finset.sum_eq_single (i ∘ ordF)]
  · rw [Finset.sum_eq_single (j ∘ ordF)]
    · by_cases h : i sl = j sl <;> simp [h]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · intro a _ ha; exact Finset.sum_eq_zero fun b _ => by simp [Ne.symm ha]
  · simp

/-- `del ∘ del† = n · id` (`SlotOrd.split` counting). -/
lemma delK_adj_delK (so : SlotOrd) {n : ℕ} (N : Matrix (Dig n 3) (Dig n 3) ℂ) :
    applyK (delK so.sl so.ordF) (applyA (delK so.sl so.ordF) N) = (n : ℂ) • N := by
  ext i' j'
  rw [applyK_delK_apply]
  simp only [applyA_delK_apply, split_symm_sl, split_symm_ord, ite_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Matrix.smul_apply, smul_eq_mul]

/-- `del(M) = n⁻¹ • del(etK M)`. -/
lemma delK_via_etK (so : SlotOrd) {n : ℕ} (hn : n ≠ 0) (M : Matrix (Dig n 4) (Dig n 4) ℂ) :
    applyK (delK so.sl so.ordF) M =
      (n : ℂ)⁻¹ • applyK (delK so.sl so.ordF) (applyK (etK so.sl so.ordF) M) := by
  rw [applyK_etK, delK_adj_delK, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn), one_smul]

/-- `etK` entrywise: `[i sl = j sl] · del(M)(i ∘ ordF, j ∘ ordF)`. -/
lemma applyK_etK_apply {n : ℕ} (sl : Fin 4) (ordF : Fin 3 → Fin 4) (M : Matrix (Dig n 4) (Dig n 4) ℂ)
    (i j : Dig n 4) :
    applyK (etK sl ordF) M i j = if i sl = j sl then applyK (delK sl ordF) M (i ∘ ordF) (j ∘ ordF) else 0 := by
  simp only [applyK, etK, delK]
  by_cases h : i sl = j sl
  · simp only [h, true_and, ite_true]
  · simp only [h, false_and, ite_false, zero_mul, Finset.sum_const_zero]

/-! ### The five slot combinations of the data -/

/-- The survivor relabelling of `Sem.insAt` is the slot splitting of the combination. -/
lemma insAt_ok : ∀ c, c < 5 → ∀ t : Fin 4, (t.val = sget c 0 ↔ t = csl c) ∧
    (t = csl c ∨ Fin.ofNat 3 ([sget c 1, sget c 2, sget c 3].idxOf t.val) = cinv c t) := by
  decide +kernel

/-- Slot data of the combination `c < 5`. -/
def soc {c : ℕ} (hc : c < 5) : SlotOrd := soOf (c := c) (slotTab_ok ⟨c, hc⟩)

lemma insAt_eq {c : ℕ} (hc : c < 5) {n : ℕ} (i : Dig n 3) (z : Fin n) :
    Sem.insAt (sget c 0) [sget c 1, sget c 2, sget c 3] i z = (soc hc).split.symm (z, i) := by
  funext t
  obtain ⟨h1, h2⟩ := insAt_ok c hc t
  show (if t.val = sget c 0 then z else i (Fin.ofNat 3 ([sget c 1, sget c 2, sget c 3].idxOf t.val))) =
    (if t = csl c then z else i (cinv c t))
  by_cases ht : t = csl c
  · rw [ite_eq_left (h1.2 ht), ite_eq_left ht]
  · rw [ite_eq_right (fun h => ht (h1.1 h)), ite_eq_right ht]
    rcases h2 with h2 | h2
    · exact absurd h2 ht
    · rw [h2]

/-- `Sem.trSlot` of the data is the local partial trace `delK`. -/
lemma cq_trSlot {c : ℕ} (hc : c < 5) {n : ℕ} [NeZero n] (M : Matrix (Dig n 4) (Dig n 4) ℚ) :
    cq (Sem.trSlot (sget c 0) [sget c 1, sget c 2, sget c 3] M) =
      applyK (delK (csl c) (cord c)) (cq M) := by
  ext i' j'
  have e := applyK_delK_apply (soc hc) (cq M) i' j'
  change _ = applyK (delK (soc hc).sl (soc hc).ordF) (cq M) i' j'
  rw [e]
  simp only [cq, Matrix.map_apply, Sem.trSlot, insAt_eq hc, map_sum]

lemma restr_eq {c : ℕ} (hnat : [sget c 1, sget c 2, sget c 3] = Sem.natOrder (sget c 0)) {n : ℕ}
    (i : Dig n 4) : Sem.restr (sget c 0) i = i ∘ cord c := by
  funext u
  simp only [Sem.restr, ← hnat, Function.comp, cord]
  fin_cases u <;> rfl

/-- `Sem.stief` of the data is the local Stiefel contrast `stK`. -/
lemma cq_stief {c : ℕ} (hc : c < 5) (hnat : [sget c 1, sget c 2, sget c 3] = Sem.natOrder (sget c 0))
    (M : Matrix (Dig 2 4) (Dig 2 4) ℚ) :
    cq (Sem.stief (sget c 0) M) = applyK (stK (csl c) (cord c)) (cq M) := by
  rw [applyK_stK]
  ext i j
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, applyK_etK_apply, ← cq_trSlot hc,
    ← restr_eq hnat, ← restr_eq hnat, hnat]
  have e : Sem.stief (sget c 0) M i j = 2 * M i j - (if i (csl c) = j (csl c) then
      Sem.trSlot (sget c 0) (Sem.natOrder (sget c 0)) M (Sem.restr (sget c 0) i) (Sem.restr (sget c 0) j)
      else 0) := rfl
  simp only [cq, Matrix.map_apply]
  rw [e]
  by_cases hij : i (csl c) = j (csl c) <;> simp [hij]

/-! ### Local functionals of the equality factors -/

/-- Coefficients `e(x, y) = J(x, μ) J(y, ν)` of the stacked row `o` over the modules `mkeys` (zero when
`μ` or `ν` is out of range). -/
noncomputable def coef (C : CertD) (mkeys : List ℕ) (n m o : ℕ) : Dig n m → Dig n m → ℂ :=
  let dec := C.eqDecode mkeys o
  let md := C.mods.getD (mkeys.getD dec.1 0) default
  if hμ : dec.2.1 < md.dim then if hν : dec.2.2 < md.dim then
    fun x y => cq (Jm n m md.J md.dim) x ⟨dec.2.1, hμ⟩ * cq (Jm n m md.J md.dim) y ⟨dec.2.2, hν⟩
  else 0 else 0

lemma cast_sandwich_del {c : ℕ} (hc : c < 5) {n : ℕ} [NeZero n] {dim : ℕ} (J : Matrix (Dig n 3) (Fin dim) ℚ)
    (p : Fin 24) (μ ν : Fin dim) :
    (((Jᵀ * Sem.trSlot (sget c 0) [sget c 1, sget c 2, sget c 3] (VG ℚ n 0 p) * J) μ ν : ℚ) : ℂ) =
      pairF (fun x y => cq J x μ * cq J y ν) (applyK (delK (csl c) (cord c)) (VG ℂ n 0 p)) := by
  have e : (((Jᵀ * Sem.trSlot (sget c 0) [sget c 1, sget c 2, sget c 3] (VG ℚ n 0 p) * J) μ ν : ℚ) : ℂ) =
      cq (Jᵀ * Sem.trSlot (sget c 0) [sget c 1, sget c 2, sget c 3] (VG ℚ n 0 p) * J) μ ν := rfl
  rw [e, cq_mul, cq_mul, cq_transpose, cq_trSlot hc, cq_VG, sandwich_apply]

lemma cast_sandwich_stief {c : ℕ} (hc : c < 5)
    (hnat : [sget c 1, sget c 2, sget c 3] = Sem.natOrder (sget c 0)) {dim : ℕ}
    (J : Matrix (Dig 2 4) (Fin dim) ℚ) (p : Fin 24) (μ ν : Fin dim) :
    (((Jᵀ * Sem.stief (sget c 0) (VG ℚ 2 0 p) * J) μ ν : ℚ) : ℂ) =
      pairF (fun x y => cq J x μ * cq J y ν) (applyK (stK (csl c) (cord c)) (VG ℂ 2 0 p)) := by
  have e : (((Jᵀ * Sem.stief (sget c 0) (VG ℚ 2 0 p) * J) μ ν : ℚ) : ℂ) =
      cq (Jᵀ * Sem.stief (sget c 0) (VG ℚ 2 0 p) * J) μ ν := rfl
  rw [e, cq_mul, cq_mul, cq_transpose, cq_stief hc hnat, cq_VG, sandwich_apply]

/-- A `del` factor is a functional of `delK(V_p)`. -/
lemma eqLoc_del (C : CertD) {c : ℕ} (hc : c < 5) (mk : List ℕ) {n : ℕ} (hn : n ≠ 0) (p : Fin 24) (o : ℕ) :
    ((C.eqLoc ⟨sget c 0, [sget c 1, sget c 2, sget c 3], 0, mk⟩ n p o : ℚ) : ℂ) =
      pairF (coef C mk n 3 o) (applyK (delK (csl c) (cord c)) (VG ℂ n 0 p)) := by
  have : NeZero n := ⟨hn⟩
  simp only [CertD.eqLoc, coef, hn, ↓reduceIte, ↓reduceDIte]
  split_ifs <;> first | exact cast_sandwich_del hc _ p _ _ | simp [pairF]

/-- A `stiefel_aux` factor is a functional of `stK(V_p)`. -/
lemma eqLoc_stief (C : CertD) {c : ℕ} (hc : c < 5)
    (hnat : [sget c 1, sget c 2, sget c 3] = Sem.natOrder (sget c 0)) (mk : List ℕ) {n : ℕ} (hn : n = 2)
    (p : Fin 24) (o : ℕ) :
    ((C.eqLoc ⟨sget c 0, [sget c 1, sget c 2, sget c 3], 1, mk⟩ n p o : ℚ) : ℂ) =
      pairF (coef C mk n 4 o) (applyK (stK (csl c) (cord c)) (VG ℂ n 0 p)) := by
  subst hn
  simp only [CertD.eqLoc, coef]
  split_ifs <;> first | contradiction | exact cast_sandwich_stief hc hnat _ p _ _ | simp [pairF]

/-- A `del` factor is a functional of `etK(V_p)`. -/
lemma eqLoc_del_etK (C : CertD) {c : ℕ} (hc : c < 5) (mk : List ℕ) {n : ℕ} (hn : n ≠ 0) (p : Fin 24)
    (o : ℕ) :
    ((C.eqLoc ⟨sget c 0, [sget c 1, sget c 2, sget c 3], 0, mk⟩ n p o : ℚ) : ℂ) =
      pairF (fun a b => (n : ℂ)⁻¹ * ∑ x, ∑ y, coef C mk n 3 o x y * delK (csl c) (cord c) x y a b)
        (applyK (etK (csl c) (cord c)) (VG ℂ n 0 p)) := by
  rw [eqLoc_del C hc mk hn p o, pairF_mul_left, ← pairF_applyK, ← pairF_smul]
  exact congrArg _ (delK_via_etK (soc hc) hn _)

/-! ### Coefficient sums of `eqVal` -/

lemma sum_mul_cast_list_sum {α β : Type*} [Fintype β] (L : List α) (x : β → ℂ) (f : α → β → ℚ) :
    ∑ w, x w * (((L.map fun a => f a w).sum : ℚ) : ℂ) = (L.map fun a => ∑ w, x w * ((f a w : ℚ) : ℂ)).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons, Rat.cast_add, mul_add, Finset.sum_add_distrib, ih]

lemma sum_eqVal (C : CertD) (g : EqGroupD) (P : EqPartD) (x : (Fin (C.k + 1) → Fin 24) → ℂ) :
    ∑ w, x w * ((C.eqVal g P w : ℚ) : ℂ) =
      (g.lam.map fun ol => (((ol.2 : ℚ) / C.lamDen : ℚ) : ℂ) *
        ∑ w, x w * ∏ l : Fin (C.k + 1),
          ((C.eqLoc (P.specs.getD l.val default) (Sem.nf C.k C.d l) (w l) (ol.1.getD l.val 0) : ℚ) : ℂ)).sum := by
  refine (sum_mul_cast_list_sum g.lam x (fun ol w => ((ol.2 : ℚ) / C.lamDen) * ∏ l : Fin (C.k + 1),
    C.eqLoc (P.specs.getD l.val default) (Sem.nf C.k C.d l) (w l) (ol.1.getD l.val 0))).trans ?_
  congr 1
  refine List.map_congr_left fun ol _ => ?_
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun w _ => by ring

end EqLink

open EqLink

/-! ### The links -/

/-- **Marginal link.** If the global partial traces of combinations `c1`, `c2` agree at the moment operators
`Σ_w x_w V_w`, then the coefficient sums of the two `del` parts (same modules) agree. -/
theorem eq_marg_link (C : Sem.CertD) (g : Sem.EqGroupD) (P1 P2 : Sem.EqPartD) {c1 c2 : ℕ}
    (hc1 : c1 < 5) (hc2 : c2 < 5) (mk : Fin (C.k + 1) → List ℕ)
    (h1 : ∀ l : Fin (C.k + 1), P1.specs.getD l.val default = ⟨sget c1 0, [sget c1 1, sget c1 2, sget c1 3], 0, mk l⟩)
    (h2 : ∀ l : Fin (C.k + 1), P2.specs.getD l.val default = ⟨sget c2 0, [sget c2 1, sget c2 2, sget c2 3], 0, mk l⟩)
    (hd : 0 < C.d) (x1 x2 : (Fin (C.k + 1) → Fin 24) → ℂ)
    (hY : applyG (trKer (nf := Sem.nf C.k C.d) c1) (∑ w, x1 w • VW (Sem.nf C.k C.d) 0 w) =
          applyG (trKer (nf := Sem.nf C.k C.d) c2) (∑ w, x2 w • VW (Sem.nf C.k C.d) 0 w)) :
    ∑ w, x1 w * ((C.eqVal g P1 w : ℚ) : ℂ) = ∑ w, x2 w * ((C.eqVal g P2 w : ℚ) : ℂ) := by
  have hn : ∀ l : Fin (C.k + 1), Sem.nf C.k C.d l ≠ 0 := by
    intro l; unfold Sem.nf; split_ifs <;> omega
  rw [sum_eqVal, sum_eqVal]
  congr 1
  refine List.map_congr_left fun ol _ => ?_
  congr 1
  set F : (l : Fin (C.k + 1)) → Dig (Sem.nf C.k C.d l) 3 → Dig (Sem.nf C.k C.d l) 3 → ℂ :=
    fun l => coef C (mk l) (Sem.nf C.k C.d l) 3 (ol.1.getD l.val 0) with hF
  have e1 : ∀ w : Fin (C.k + 1) → Fin 24, ∏ l : Fin (C.k + 1),
      ((C.eqLoc (P1.specs.getD l.val default) (Sem.nf C.k C.d l) (w l) (ol.1.getD l.val 0) : ℚ) : ℂ) =
      ∏ l, pairF (F l) (applyK (trKer (nf := Sem.nf C.k C.d) c1 l) (VG ℂ (Sem.nf C.k C.d l) 0 (w l))) :=
    fun w => Finset.prod_congr rfl fun l _ => by
      rw [h1 l]; exact eqLoc_del C hc1 (mk l) (hn l) (w l) _
  have e2 : ∀ w : Fin (C.k + 1) → Fin 24, ∏ l : Fin (C.k + 1),
      ((C.eqLoc (P2.specs.getD l.val default) (Sem.nf C.k C.d l) (w l) (ol.1.getD l.val 0) : ℚ) : ℂ) =
      ∏ l, pairF (F l) (applyK (trKer (nf := Sem.nf C.k C.d) c2 l) (VG ℂ (Sem.nf C.k C.d l) 0 (w l))) :=
    fun w => Finset.prod_congr rfl fun l _ => by
      rw [h2 l]; exact eqLoc_del C hc2 (mk l) (hn l) (w l) _
  simp only [e1, e2]
  rw [sum_prod_pairF (trKer (nf := Sem.nf C.k C.d) c1) F x1,
    sum_prod_pairF (trKer (nf := Sem.nf C.k C.d) c2) F x2, hY]

/-- **Stiefel link.** If the Stiefel map of combination `c` (`stK` on the auxiliary qubit, `etK` on the
sites) vanishes at the moment operator `Σ_w x_w V_w`, then the coefficient sum of the part vanishes. -/
theorem eq_stief_link (C : Sem.CertD) (g : Sem.EqGroupD) (P : Sem.EqPartD) {c : ℕ} (hc : c < 5)
    (hnat : [sget c 1, sget c 2, sget c 3] = Sem.natOrder (sget c 0)) (mk : Fin (C.k + 1) → List ℕ)
    (h : ∀ l : Fin (C.k + 1), P.specs.getD l.val default =
      ⟨sget c 0, [sget c 1, sget c 2, sget c 3], if l.val < C.k then 0 else 1, mk l⟩)
    (hd : 0 < C.d) (x : (Fin (C.k + 1) → Fin 24) → ℂ)
    (hY : applyG (stKer (nf := Sem.nf C.k C.d) (fun l : Fin (C.k + 1) => ¬ l.val < C.k) c)
          (∑ w, x w • VW (Sem.nf C.k C.d) 0 w) = 0) :
    ∑ w, x w * ((C.eqVal g P w : ℚ) : ℂ) = 0 := by
  rw [sum_eqVal]
  refine List.sum_eq_zero fun t ht => ?_
  obtain ⟨ol, -, rfl⟩ := List.mem_map.1 ht
  set F : (l : Fin (C.k + 1)) → Dig (Sem.nf C.k C.d l) 4 → Dig (Sem.nf C.k C.d l) 4 → ℂ :=
    fun l => if l.val < C.k then
      (fun a b => (Sem.nf C.k C.d l : ℂ)⁻¹ * ∑ x, ∑ y,
        coef C (mk l) (Sem.nf C.k C.d l) 3 (ol.1.getD l.val 0) x y * delK (csl c) (cord c) x y a b)
      else coef C (mk l) (Sem.nf C.k C.d l) 4 (ol.1.getD l.val 0) with hF
  have e : ∀ w : Fin (C.k + 1) → Fin 24, ∏ l : Fin (C.k + 1),
      ((C.eqLoc (P.specs.getD l.val default) (Sem.nf C.k C.d l) (w l) (ol.1.getD l.val 0) : ℚ) : ℂ) =
      ∏ l, pairF (F l) (applyK (stKer (nf := Sem.nf C.k C.d) (fun l : Fin (C.k + 1) => ¬ l.val < C.k) c l)
        (VG ℂ (Sem.nf C.k C.d l) 0 (w l))) := by
    intro w
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [h l]
    by_cases hl : l.val < C.k
    · have hn : Sem.nf C.k C.d l ≠ 0 := by unfold Sem.nf; rw [ite_eq_left hl]; omega
      simp only [hF, stKer, hl, ite_true, not_true_eq_false, ite_false]
      exact eqLoc_del_etK C hc (mk l) hn (w l) _
    · have hn : Sem.nf C.k C.d l = 2 := by unfold Sem.nf; rw [ite_eq_right hl]
      simp only [hF, stKer, hl, ite_false, not_false_eq_true, ite_true]
      exact eqLoc_stief C hc hnat (mk l) hn (w l) _
  simp only [e]
  rw [sum_prod_pairF (stKer (nf := Sem.nf C.k C.d) (fun l : Fin (C.k + 1) => ¬ l.val < C.k) c) F x, hY,
    pairF_zero, mul_zero]

end NPT.Cert

#print axioms NPT.Cert.eq_marg_link
#print axioms NPT.Cert.eq_stief_link
