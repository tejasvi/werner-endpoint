/-
NPT.CP3.D3Site — the local trace facts of the objective and of the equality rows on the sites.

A `Dig 3 4` identity `Tr(G X) = Σ_λ ⟨ℓ_λ, Jᵀ_λ X J_λ⟩` gives `TraceAt` on every site factor (`traceAt_site`).
The identities at `X = V_p` are finite: `Tr((2I − F₀₃) V_p) = zsObj2[p]`, `(I₀ ⊗ Tr₀ V_p)[i₀, j₀(q)] = delMat[q][p]`,
`Jᵀ V_p J = siteM[0][λ][p]`, and the data identities `zsObj2 = ellO · siteM`, `delMat = ellE · siteM` (kernel).
-/
import NPT.CP3.D3Sem

open Matrix BigOperators Finset NPT.Brauer NPT.Cert

namespace NPT.CP3.Inst

open NPT.CP3 NPT.CP3.Data NPT.CP3.Chk NPT.CP3.Sem

/-! ### Transport between a site factor and `Dig 3 4` -/

/-- Site factor relabelling `Dig (nfC l) 4 ≃ Dig 3 4`. -/
def digE {l : Fin 5} (hl : l.val < 4) : Dig (nfC l) 4 ≃ Dig 3 4 where
  toFun x := Fin.cast (nfC_site hl) ∘ x
  invFun x := Fin.cast (nfC_site hl).symm ∘ x
  left_inv x := by funext r; simp
  right_inv x := by funext r; simp

/-- Padded column relabelling `Fin (dpad l) ≃ Fin 3`. -/
def finE {l : Fin 5} (hl : l.val < 4) : Fin (dpad l) ≃ Fin 3 := finCongr (dpad_site hl)

lemma trace_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (A : Matrix κ κ ℂ) :
    (A.submatrix e e).trace = A.trace := by
  unfold Matrix.trace
  exact Fintype.sum_equiv e _ _ fun x => rfl

lemma pairing_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (A B : Matrix κ κ ℂ) :
    pairing (A.submatrix e e) (B.submatrix e e) = pairing A B := by
  unfold pairing
  refine Fintype.sum_equiv e _ _ fun x => ?_
  exact Fintype.sum_equiv e _ _ fun y => rfl

lemma PD0_M_site {l : Fin 5} (hl : l.val < 4) (la : Fin 5) :
    (PD 0).M l la = (MsC 0 la).submatrix (digE hl) (finE hl) := by
  ext x a
  exact dif_pos hl

lemma VG0_site {l : Fin 5} (hl : l.val < 4) (p : Fin 24) :
    VG ℂ (nfC l) 0 p = (VG ℂ 3 0 p).submatrix (digE hl) (digE hl) := by
  ext x y
  simp only [Matrix.submatrix_apply, Phys.SymAux.VG0_apply]
  have key : (digE hl x = digE hl y ∘ pinvf p) ↔ x = y ∘ pinvf p :=
    (Function.Injective.comp_left (Fin.cast_injective (nfC_site hl))).eq_iff
  by_cases h : x = y ∘ pinvf p
  · rw [if_pos h, if_pos (key.2 h)]
  · rw [if_neg h, if_neg (fun h' => h (key.1 h'))]

/-- **Site trace facts transported**: a `Dig 3 4` identity gives `TraceAt` on a site factor. -/
theorem traceAt_site {l : Fin 5} (hl : l.val < 4) (G3 X3 : Matrix (Dig 3 4) (Dig 3 4) ℂ)
    (ell3 : Fin 5 → Matrix (Fin 3) (Fin 3) ℂ)
    (h : (G3 * X3).trace = ∑ la : Fin 5, pairing (ell3 la) ((MsC 0 la)ᵀ * X3 * MsC 0 la)) :
    TraceAt (PD 0).fam l (G3.submatrix (digE hl) (digE hl)) (fun la => (ell3 la).submatrix (finE hl) (finE hl))
      (X3.submatrix (digE hl) (digE hl)) := by
  unfold TraceAt
  rw [Matrix.submatrix_mul_equiv, trace_submatrix_equiv, h]
  refine Finset.sum_congr rfl fun la _ => ?_
  have hg : gramLoc (PD 0).fam l la (X3.submatrix (digE hl) (digE hl)) =
      ((MsC 0 la)ᵀ * X3 * MsC 0 la).submatrix (finE hl) (finE hl) := by
    show ((PD 0).M l la)ᵀ * X3.submatrix (digE hl) (digE hl) * (PD 0).M l la = _
    rw [PD0_M_site hl la, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  rw [hg, pairing_submatrix_equiv]

/-! ### Masked sums -/

lemma sum_fin_mask2 {d e : ℕ} (he : e ≤ d) (f : ℕ → ℕ → ℂ) :
    ∑ a : Fin d, ∑ b : Fin d, (if a.val < e ∧ b.val < e then f a b else 0) =
      ∑ a ∈ Finset.range e, ∑ b ∈ Finset.range e, f a b := by
  rw [← sum_fin_range he (fun a => ∑ b ∈ Finset.range e, f a b)]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : a.val < e
  · rw [if_pos ha, ← sum_fin_range he (fun b => f a b)]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b.val < e <;> simp [ha, hb]
  · rw [if_neg ha]
    exact Finset.sum_eq_zero fun b _ => by simp [ha]

/-- Masked `3 × 3` matrices of label `la` (cut `()`). -/
noncomputable def mask3 (la : Fin 5) (f : ℕ → ℕ → ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun a b => if a.val < sdim 0 la ∧ b.val < sdim 0 la then f a b else 0

lemma pairing_mask3 (la : Fin 5) (f g : ℕ → ℕ → ℂ) :
    pairing (mask3 la f) (mask3 la g) = ∑ a ∈ Finset.range (sdim 0 la), ∑ b ∈ Finset.range (sdim 0 la), f a b * g a b := by
  rw [← sum_fin_mask2 (sdim_le la)]
  unfold pairing mask3
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp

lemma sum_label5 (F : ℕ → ℂ) (h4 : F 4 = 0) :
    ∑ la : Fin 5, F la = ∑ la ∈ Finset.range 4, F la := by
  rw [Fin.sum_univ_eq_sum_range F 5, Finset.sum_range_succ, h4, add_zero]

/-! ### The site Gram forms of `V_p` -/

/-- The cast `siteM[0][la][p]` (masked). -/
noncomputable def siteMC (la : Fin 5) (p : Fin 24) : Matrix (Fin 3) (Fin 3) ℂ :=
  mask3 la fun a b => ((mget (((siteM.getD 0 []).getD la []).getD p []) a b : ℤ) : ℂ)

lemma siteGram_int : ∀ la : Fin 5, ∀ p : Fin 24, ∀ a b : Fin 3,
    (∑ y : Dig 3 4, (if a.val < sdim 0 la then mget ((siteJ.getD 0 []).getD la []) (Sem.flat (y ∘ pinvf p)) a else 0) *
      (if b.val < sdim 0 la then mget ((siteJ.getD 0 []).getD la []) (Sem.flat y) b else 0)) =
    (if a.val < sdim 0 la ∧ b.val < sdim 0 la then mget (((siteM.getD 0 []).getD la []).getD p []) a b else 0) := by
  decide +kernel

theorem siteGram (la : Fin 5) (p : Fin 24) : (MsC 0 la)ᵀ * VG ℂ 3 0 p * MsC 0 la = siteMC la p := by
  ext a b
  have h := congrArg (fun z : ℤ => (z : ℂ)) (siteGram_int la p a b)
  simp only [Int.cast_sum, Int.cast_mul, Int.cast_ite, Int.cast_zero] at h
  unfold siteMC mask3
  rw [← h]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Phys.SymAux.VG0_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single (y ∘ pinvf p)]
  · rw [if_pos rfl, mul_one]
    rfl
  · intro x _ hx
    rw [if_neg hx, mul_zero, zero_mul]
  · intro h'; exact absurd (Finset.mem_univ _) h'

/-! ### The objective on a site -/

lemma trace_obj_int : ∀ p : Fin 24, (∑ j : Dig 3 4, ((2 * (if j = (j ∘ pinvf p) ∘ pinvf 0 then 1 else 0) -
    (if j = (j ∘ pinvf p) ∘ pinvf 21 then 1 else 0) : ℤ))) = zsObj2.getD p 0 := by decide +kernel

theorem trace_obj3 (p : Fin 24) :
    (((2 : ℂ) • VG ℂ 3 0 0 - VG ℂ 3 0 21) * VG ℂ 3 0 p).trace = (zsObj2.getD p 0 : ℂ) := by
  have h := congrArg (fun z : ℤ => (z : ℂ)) (trace_obj_int p)
  simp only [Int.cast_sum, Int.cast_sub, Int.cast_mul, Int.cast_ofNat, Int.cast_ite, Int.cast_one,
    Int.cast_zero] at h
  rw [← h]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Phys.SymAux.VG0_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single (j ∘ pinvf p)]
  · simp
  · intro i _ hi
    simp [hi]
  · intro h'; exact absurd (Finset.mem_univ _) h'

lemma obj_site_num : ∀ p : Fin 24, (576 : ℤ) * zsObj2.getD p 0 =
    ∑ la ∈ Finset.range 4, ∑ a ∈ Finset.range (sdim 0 la), ∑ b ∈ Finset.range (sdim 0 la),
      (∑ p' ∈ Finset.range 24, zsObj2.getD p' 0 * (ifgNum.getD p' []).getD (scoord la a b) 0) *
        mget (((siteM.getD 0 []).getD la []).getD p []) a b := by decide +kernel

/-- The objective site functional of label `la` (masked, `3 × 3`). -/
noncomputable def ellO3 (la : Fin 5) : Matrix (Fin 3) (Fin 3) ℂ := mask3 la fun a b => ((ellO la a b : ℚ) : ℂ)

theorem obj_site3 (p : Fin 24) :
    (((2 : ℂ) • VG ℂ 3 0 0 - VG ℂ 3 0 21) * VG ℂ 3 0 p).trace =
      ∑ la : Fin 5, pairing (ellO3 la) ((MsC 0 la)ᵀ * VG ℂ 3 0 p * MsC 0 la) := by
  rw [trace_obj3]
  simp only [siteGram, ellO3, siteMC, pairing_mask3]
  rw [sum_label5 (fun la => ∑ a ∈ Finset.range (sdim 0 la), ∑ b ∈ Finset.range (sdim 0 la),
      ((ellO la a b : ℚ) : ℂ) * ((mget (((siteM.getD 0 []).getD la []).getD p []) a b : ℤ) : ℂ))
    (by rw [show sdim 0 4 = 0 from sdim4]; simp)]
  have h := congrArg (fun z : ℤ => ((z : ℚ) / 576 : ℚ)) (obj_site_num p)
  simp only [Int.cast_mul, Int.cast_sum, Int.cast_ofNat] at h
  have h' : ((zsObj2.getD p 0 : ℤ) : ℚ) = ∑ la ∈ Finset.range 4, ∑ a ∈ Finset.range (sdim 0 la),
      ∑ b ∈ Finset.range (sdim 0 la), ellO la a b * ((mget (((siteM.getD 0 []).getD la []).getD p []) a b : ℤ) : ℚ) := by
    rw [mul_div_cancel_left₀ _ (by norm_num : (576 : ℚ) ≠ 0)] at h
    rw [h, Finset.sum_div]
    refine Finset.sum_congr rfl fun la _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [ellO, zr2, ifgDen]
    push_cast
    ring
  have h'' := congrArg (fun z : ℚ => (z : ℂ)) h'
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast] at h''
  exact_mod_cast h''

/-! ### The equality rows on a site -/

/-- The witness entry of the three-replica word `q` after deleting replica `0`. -/
def i0E : Dig 3 4 := ![0, 0, 1, 2]
def j0E (q : ℕ) : Dig 3 4 := fun r => if r = 0 then 0 else Fin.ofNat 3 ((permL3.getD q []).getD (r.val - 1) 0)

lemma etK_int : ∀ q : Fin 6, ∀ p : Fin 24,
    (∑ x : Dig 3 4, (if i0E (csl 0) = j0E q (csl 0) ∧ (x ∘ pinvf p) ∘ cord 0 = i0E ∘ cord 0 ∧
      x ∘ cord 0 = j0E q ∘ cord 0 ∧ (x ∘ pinvf p) (csl 0) = x (csl 0) then (1 : ℤ) else 0)) =
      ((delMat.getD q []).getD p 0 : ℤ) := by decide +kernel

theorem etK3 (q : Fin 6) (p : Fin 24) :
    applyK (etK (n := 3) (csl 0) (cord 0)) (VG ℂ 3 0 p) i0E (j0E q) = ((delMat.getD q []).getD p 0 : ℂ) := by
  have ha : aSel 0 p = pinvf p := by funext s; simp [aSel, inS]
  have hb : bSel 0 p = id := by funext s; simp [bSel, inS]
  have h := congrArg (fun z : ℤ => (z : ℂ)) (etK_int q p)
  simp only [Int.cast_sum, Int.cast_ite, Int.cast_one, Int.cast_zero, Int.cast_natCast] at h
  rw [← h]
  unfold VG
  rw [ha, hb, applyK_SelOp]
  simp only [etK, Function.comp_id]

/-- The coefficient functional of the word `q` (a matrix unit). -/
def unitF (q : ℕ) : Dig 3 4 → Dig 3 4 → ℂ := fun x y => if x = i0E ∧ y = j0E q then 1 else 0

lemma trace_Gk {n : ℕ} (κ : LKer n 4) (F : Dig n 4 → Dig n 4 → ℂ) (X : Matrix (Dig n 4) (Dig n 4) ℂ) :
    (Gk κ F * X).trace = ∑ x, ∑ y, F x y * applyK κ X x y := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Gk, applyK, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  calc ∑ a, ∑ b, ∑ x, ∑ y, F x y * (κ x y b a * X b a)
      = ∑ a, ∑ x, ∑ b, ∑ y, F x y * (κ x y b a * X b a) := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ x, ∑ a, ∑ b, ∑ y, F x y * (κ x y b a * X b a) := Finset.sum_comm
    _ = ∑ x, ∑ a, ∑ y, ∑ b, F x y * (κ x y b a * X b a) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ a, ∑ b, F x y * (κ x y b a * X b a) := Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x, ∑ y, ∑ b, ∑ a, F x y * (κ x y b a * X b a) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => Finset.sum_comm

lemma trace_unitF (q : ℕ) (X : Matrix (Dig 3 4) (Dig 3 4) ℂ) :
    (Gk (etK (n := 3) (csl 0) (cord 0)) (unitF q) * X).trace = applyK (etK (csl 0) (cord 0)) X i0E (j0E q) := by
  rw [trace_Gk]
  rw [Finset.sum_eq_single i0E]
  · rw [Finset.sum_eq_single (j0E q)]
    · simp [unitF]
    · intro y _ hy; simp [unitF, hy]
    · intro h'; exact absurd (Finset.mem_univ _) h'
  · intro x _ hx
    exact Finset.sum_eq_zero fun y _ => by simp [unitF, hx]
  · intro h'; exact absurd (Finset.mem_univ _) h'

lemma eq_site_num : ∀ q : Fin 6, ∀ p : Fin 24, (192 : ℤ) * ((delMat.getD q []).getD p 0 : ℤ) =
    ∑ la ∈ Finset.range 4, ∑ a ∈ Finset.range (sdim 0 la), ∑ b ∈ Finset.range (sdim 0 la),
      (eqNum.getD q []).getD (scoord la a b) 0 * mget (((siteM.getD 0 []).getD la []).getD p []) a b := by
  decide +kernel

/-- The equality site functional of word `q`, label `la` (masked, `3 × 3`). -/
noncomputable def ellE3 (q : ℕ) (la : Fin 5) : Matrix (Fin 3) (Fin 3) ℂ := mask3 la fun a b => ((ellE q la a b : ℚ) : ℂ)

theorem eq_site3 (q : Fin 6) (p : Fin 24) :
    (Gk (etK (n := 3) (csl 0) (cord 0)) (unitF q) * VG ℂ 3 0 p).trace =
      ∑ la : Fin 5, pairing (ellE3 q la) ((MsC 0 la)ᵀ * VG ℂ 3 0 p * MsC 0 la) := by
  rw [trace_unitF, etK3]
  simp only [siteGram, ellE3, siteMC, pairing_mask3]
  rw [sum_label5 (fun la => ∑ a ∈ Finset.range (sdim 0 la), ∑ b ∈ Finset.range (sdim 0 la),
      ((ellE q la a b : ℚ) : ℂ) * ((mget (((siteM.getD 0 []).getD la []).getD p []) a b : ℤ) : ℂ))
    (by rw [show sdim 0 4 = 0 from sdim4]; simp)]
  have h := congrArg (fun z : ℤ => ((z : ℚ) / 192 : ℚ)) (eq_site_num q p)
  simp only [Int.cast_mul, Int.cast_sum, Int.cast_ofNat] at h
  have h' : (((delMat.getD q []).getD p 0 : ℤ) : ℚ) = ∑ la ∈ Finset.range 4, ∑ a ∈ Finset.range (sdim 0 la),
      ∑ b ∈ Finset.range (sdim 0 la), ellE q la a b * ((mget (((siteM.getD 0 []).getD la []).getD p []) a b : ℤ) : ℚ) := by
    rw [mul_div_cancel_left₀ _ (by norm_num : (192 : ℚ) ≠ 0)] at h
    rw [h, Finset.sum_div]
    refine Finset.sum_congr rfl fun la _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [ellE, eqDen]
    push_cast
    ring
  have h'' := congrArg (fun z : ℚ => (z : ℂ)) h'
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast] at h''
  exact_mod_cast h''

end NPT.CP3.Inst
