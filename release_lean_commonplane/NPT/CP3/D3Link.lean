/-
NPT.CP3.D3Link — the objective link `hobj` and the equality links `hE` of `MainR`, from the D3 data identities.

* Objective: `Tr(O_w Yp) = Σ_k cw_k Tr(O_k Yp)` (`Ow_split`) and `Tr(O_k Yp) = Σ_v Σ_j y_(off v + j) cobjFlat k v j`
  (`obj_coords`); with `cobjFlat k v j = 16 · 162⁴ · cvec k (off v + j)` (D3) this is `hobj` with `κ = 1/(8 · 162⁴)`.
* Equality row `e` (`erows[e] = qi · 70 + u`, words `q = sortedQ[qi]`): the functional
  `ψ_e(Y) = ⟨⊗_l F_l, stK0(Y)⟩` (matrix units: word `q_l` on site `l`, unit `u` on the aux factor) vanishes at `Yp A`
  (`stK0_Yp`), and `ψ_e(Yp A) = Σ_v Σ_j y_(off v + j) cEFlat e v j` (`lift_c`, orbits, cosets); with
  `Erow e (off v + j) = 192⁴ · cEFlat e v j` (D3) this is `hE`.
-/
import NPT.CP3.D3Obj

open Matrix BigOperators Finset NPT.Brauer NPT.Cert

namespace NPT.CP3.Inst

open NPT.CP3 NPT.CP3.Data NPT.CP3.Chk NPT.CP3.Sem

/-! ### The objective link -/

/-- **`hobj` of `MainR`** from the D3 objective identity. -/
theorem hobj_of (hd3 : ∀ k < 3, ∀ v < 175, ∀ j < (vb v).S.length,
      cobjFlat k v j = 16 * 162 ^ 4 * (tN k ((vb v).off + j) : ℚ) / cDen)
    (A : MatA) (x₁ x₂ : ℝ) :
    ∑ i ∈ Finset.range 1331, yvec T A i * ((x₁ : ℂ) ^ 2 * (Sem.cvec 0 i : ℂ) + (x₂ : ℂ) ^ 2 * (Sem.cvec 1 i : ℂ) +
      (x₁ : ℂ) * x₂ * (Sem.cvec 2 i : ℂ)) = (((1 / (8 * 162 ^ 4) : ℝ)) : ℂ) * (Ow ![x₁, x₂] * Yp A).trace := by
  have hk : ∀ k : Fin 3, (kron (Gobj k) * Yp A).trace =
      ∑ i ∈ Finset.range 1331, yvec T A i * ((16 * 162 ^ 4 : ℂ) * (Sem.cvec k i : ℂ)) := by
    intro k
    rw [obj_coords k A, ← sum_vj_coord A (fun i => (16 * 162 ^ 4 : ℂ) * (Sem.cvec k i : ℂ))]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1
    show ((cobjFlat k v j : ℚ) : ℂ) = (16 * 162 ^ 4 : ℂ) * (Sem.cvec k ((vb v).off + j.val) : ℂ)
    rw [hd3 k k.isLt v v.isLt j j.isLt]
    simp only [Sem.cvec]
    push_cast
    ring
  rw [Ow_split, Matrix.sum_mul, Matrix.trace_sum]
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, hk, Fin.sum_univ_three, cw]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
    Finset.mul_sum, ← Finset.sum_add_distrib, Fin.val_zero, Fin.val_one, Fin.val_two]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-! ### The equality rows -/

lemma etK_cast {n m : ℕ} (h : n = m) (sl : Fin 4) (ordF : Fin 3 → Fin 4) (i' j' i j : Dig n 4) :
    etK (n := m) sl ordF (Fin.cast h ∘ i') (Fin.cast h ∘ j') (Fin.cast h ∘ i) (Fin.cast h ∘ j) =
      etK (n := n) sl ordF i' j' i j := by
  subst h; rfl

lemma stK_cast {n m : ℕ} (h : n = m) (sl : Fin 4) (ordF : Fin 3 → Fin 4) (i' j' i j : Dig n 4) :
    stK (n := m) sl ordF (Fin.cast h ∘ i') (Fin.cast h ∘ j') (Fin.cast h ∘ i) (Fin.cast h ∘ j) =
      stK (n := n) sl ordF i' j' i j := by
  subst h; rfl

/-- Transport of `Gk` along a digit relabelling `Fin n ≃ Fin m` (`n = m`). -/
lemma Gk_cast {n m : ℕ} (h : n = m) (κn : LKer n 4) (κm : LKer m 4)
    (hκ : ∀ i' j' i j : Dig n 4, κm (Fin.cast h ∘ i') (Fin.cast h ∘ j') (Fin.cast h ∘ i) (Fin.cast h ∘ j) = κn i' j' i j)
    (F : Dig m 4 → Dig m 4 → ℂ) (a b : Dig n 4) :
    Gk κn (fun x y => F (Fin.cast h ∘ x) (Fin.cast h ∘ y)) a b = Gk κm F (Fin.cast h ∘ a) (Fin.cast h ∘ b) := by
  subst h
  unfold Gk
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [← hκ x y b a]
  rfl

/-- The coefficient functional of row `e` on factor `l` (words on the sites, the unit on the aux factor). -/
noncomputable def Fe (e : ℕ) : (l : Fin 5) → Dig (nfC l) 4 → Dig (nfC l) 4 → ℂ := fun l =>
  if h : l.val < 4 then fun x y => unitF ((eQ e).getD l 0) (Fin.cast (nfC_site h) ∘ x) (Fin.cast (nfC_site h) ∘ y)
  else fun x y => unitFA (eU e) (Fin.cast (nfC_aux h) ∘ x) (Fin.cast (nfC_aux h) ∘ y)

/-- The local trace-form factors of `ψ_e`. -/
noncomputable def GE (e : ℕ) : LocM := fun l => Gk (stK0 l) (Fe e l)

lemma GE_site (e : ℕ) {l : Fin 5} (hl : l.val < 4) :
    GE e l = (Gk (etK (n := 3) (csl 0) (cord 0)) (unitF ((eQ e).getD l 0))).submatrix (digE hl) (digE hl) := by
  ext a b
  have hk : stK0 l = etK (csl 0) (cord 0) := by
    show (if ¬ l.val < 4 then stK (csl 0) (cord 0) else etK (csl 0) (cord 0)) = _
    rw [if_neg (not_not_intro hl)]
  unfold GE
  rw [hk]
  have hF : Fe e l = fun x y => unitF ((eQ e).getD l 0) (Fin.cast (nfC_site hl) ∘ x) (Fin.cast (nfC_site hl) ∘ y) :=
    dif_pos hl
  rw [hF, Gk_cast (nfC_site hl) _ _ (fun i' j' i j => etK_cast (nfC_site hl) _ _ i' j' i j)]
  rfl

lemma GE_aux (e : ℕ) : GE e 4 = (Gk (stK (n := 2) (csl 0) (cord 0)) (unitFA (eU e))).submatrix digA digA := by
  ext a b
  have hk : stK0 4 = stK (csl 0) (cord 0) := by
    show (if ¬ (4 : Fin 5).val < 4 then stK (csl 0) (cord 0) else etK (csl 0) (cord 0)) = _
    rw [if_pos not4]
  unfold GE
  rw [hk]
  have hF : Fe e 4 = fun x y => unitFA (eU e) (Fin.cast (nfC_aux not4) ∘ x) (Fin.cast (nfC_aux not4) ∘ y) :=
    dif_neg not4
  rw [hF, Gk_cast (nfC_aux not4) _ _ (fun i' j' i j => stK_cast (nfC_aux not4) _ _ i' j' i j)]
  rfl

/-- Site and auxiliary entries of row `e`. -/
noncomputable def fsE (e : ℕ) : ℕ → ℕ → ℕ → ℕ → ℂ := fun s la a b => ((ellE ((eQ e).getD s 0) la a b : ℚ) : ℂ)
noncomputable def faE (e : ℕ) : ℕ → ℕ → ℕ → ℂ := fun li a b => ((ellAE (eU e) li a b : ℚ) : ℂ)

lemma eQ_lt : ∀ e < 146, ∀ s < 4, (eQ e).getD s 0 < 6 := by decide +kernel
lemma eU_lt (e : ℕ) : eU e < 70 := Nat.mod_lt _ (by norm_num)

theorem eq_lift (e : ℕ) (he : e < 146) (A : MatA) :
    (kron (GE e) * Yp A).trace =
      ∑ τ : Tup (PD 0).fam, pairing (kronR fun l => ellPad (fsE e) (faE e) l (τ l)) (gram (PD 0).fam τ (Yp A)) := by
  refine lift_c (PD 0).fam (GE e) (fun l la => ellPad (fsE e) (faE e) l la) (fun l hl p => ?_) (fun X => ?_) (Yp_mem A)
  · rw [GE_site e hl, VG0_site hl]
    have hq := eQ_lt e he l hl
    have he' : (fun la => ellPad (fsE e) (faE e) l la) =
        fun la => (ellE3 (⟨(eQ e).getD l 0, hq⟩ : Fin 6) la).submatrix (finE hl) (finE hl) := by
      funext la
      rw [ellPad_site_eq (fsE e) (faE e) hl la]
      rfl
    rw [he']
    exact traceAt_site hl _ (VG ℂ 3 0 p) _ (eq_site3 ⟨(eQ e).getD l 0, hq⟩ p)
  · rw [GE_aux]
    have he' : (fun la => ellPad (fsE e) (faE e) 4 la) = fun la => (mask6 (faE e) la).submatrix finA finA := by
      funext la
      exact ellPad_aux_eq (fsE e) (faE e) la
    rw [he']
    exact traceAt_aux _ (mask6 (faE e)) (eq_aux2 ⟨eU e, eU_lt e⟩) X

lemma fsPerm_fsE (e : ℕ) (σ : Equiv.Perm (Fin 4)) (s : ℕ) (hs : s < 4) :
    fsPerm σ (fsE e) s = fsE e (σ ⟨s, hs⟩).val := by
  unfold fsPerm
  rw [dif_pos hs]

/-- **The equality functional in the coordinates.** -/
theorem eq_coords (e : ℕ) (he : e < 146) (A : MatA) :
    (kron (GE e) * Yp A).trace =
      ∑ v : Fin 175, ∑ j : Fin (T v).nb, yvec T A ((T v).off + j.val) * ((cEFlat e v j : ℚ) : ℂ) := by
  rw [eq_lift e he, psem_sound (PD 0) Dcp Dcp_cos Dcp_inj (fun σ i j => Yp_site_entry σ A i j) (Dcp_out (Yp A))
    (yvec T A) (Dcp_coord A) (fun l la => ellPad (fsE e) (faE e) l la)]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [coset_flat v j (fsE e) (faE e)]
  unfold cEFlat
  push_cast
  rw [← Fin.sum_univ_eq_sum_range (fun c => ∑ a : Fin (nV v), ∑ b : Fin (nV v), ((Gflat v j a b : ℚ) : ℂ) *
    ((∏ m ∈ Finset.range 4, ((ellE ((eQ e).getD ((cosE v c).2.getD m m) 0) ((vb v).st.getD m 0)
      (digL (vb v).dims m a) (digL (vb v).dims m b) : ℚ) : ℂ)) *
      ((ellAE (eU e) (vb v).ai (digL (vb v).dims 4 a) (digL (vb v).dims 4 b) : ℚ) : ℂ)))]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 2
  refine Finset.prod_congr rfl fun m hm => ?_
  have hm' : m < 4 := Finset.mem_range.1 hm
  rw [fsPerm_fsE e (permT v c) m hm', (cos_ok v v.isLt c c.isLt).2 ⟨m, hm'⟩]
  rfl

set_option maxRecDepth 20000 in
/-- **`hE` of `MainR`** from the D3 equality identity. -/
theorem hE_of (hd3 : ∀ e < 146, ∀ v < 175, ∀ j < (vb v).S.length,
      (((Ecol.getD ((vb v).off + j) []).getD e 0 : ℤ) : ℚ) = 192 ^ 4 * cEFlat e v j)
    (A : MatA) (hA : Aᴴ * A = 1) (e : ℕ) (he : e < 146) :
    ∑ i ∈ Finset.range 1331, yvec T A i * (Sem.Erow e i : ℂ) = 0 := by
  have h0 : (kron (GE e) * Yp A).trace = 0 := by
    have hz : applyG stK0 (Yp A) = 0 := stK0_Yp hA
    rw [show GE e = fun l => Gk (stK0 l) (Fe e l) from rfl, ← pairF_applyG_trace stK0 (Fe e) (Yp A), hz]
    exact EqLink.pairF_zero _
  rw [← sum_vj_coord A (fun i => (Sem.Erow e i : ℂ))]
  have h1 : ∀ v : Fin 175, ∀ j : Fin (T v).nb,
      yvec T A ((T v).off + j.val) * (Sem.Erow e ((T v).off + j.val) : ℂ) =
        (192 ^ 4 : ℂ) * (yvec T A ((T v).off + j.val) * ((cEFlat e v j : ℚ) : ℂ)) := by
    intro v j
    show yvec T A ((T v).off + j.val) * ((((Ecol.getD ((vb v).off + j.val) []).getD e 0 : ℤ) : ℝ) : ℂ) = _
    have h := hd3 e he v v.isLt j j.isLt
    have h' : ((((Ecol.getD ((vb v).off + j.val) []).getD e 0 : ℤ) : ℝ) : ℂ) =
        (192 ^ 4 : ℂ) * ((cEFlat e v j : ℚ) : ℂ) := by
      have h2 := congrArg (fun q : ℚ => (q : ℂ)) h
      push_cast at h2 ⊢
      exact h2
    rw [h']
    ring
  simp only [h1, ← Finset.mul_sum]
  rw [← eq_coords e he A, h0, mul_zero]

end NPT.CP3.Inst
