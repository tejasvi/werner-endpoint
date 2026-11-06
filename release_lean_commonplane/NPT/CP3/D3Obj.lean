/-
NPT.CP3.D3Obj — the objective as a function of the coordinates.

`O_w = D_w O D_w` splits into three Kronecker products with site factors `2I − F₀₃` and auxiliary factors
`2 Π₀ F₀₃ Π₀`, `2 Π₁ F₀₃ Π₁`, `2 (Π₀ F₀₃ Π₁ + Π₁ F₀₃ Π₀)` with weights `w₀²/2`, `w₁²/2`, `w₀w₁/2` (`Ow_split`). Each has the
local trace facts of `D3Site`/`D3Aux`, so `lift_c`, the orbit decomposition `psem_sound` and the coset/flat conversion
give `Tr(O_k Yp) = Σ_v Σ_j y_(off v + j) · cobjFlat k v j` (`obj_coords`). With the D3 data identity
`cobjFlat k v j = 16 · 162⁴ · cvec k (off v + j)` this is the objective link `hobj` of `MainR` with `κ = 1/(8 · 162⁴)`.
-/
import NPT.CP3.D3Aux

open Matrix BigOperators Finset NPT.Brauer NPT.Cert

namespace NPT.CP3.Inst

open NPT.CP3 NPT.CP3.Data NPT.CP3.Chk NPT.CP3.Sem

/-! ### Padded functionals as transported matrices -/

lemma ellPad_site_eq (fs : ℕ → ℕ → ℕ → ℕ → ℂ) (fa : ℕ → ℕ → ℕ → ℂ) {l : Fin 5} (hl : l.val < 4) (la : Fin 5) :
    ellPad fs fa l la = (mask3 la (fun a b => fs l la a b)).submatrix (finE hl) (finE hl) := by
  ext a b
  simp only [ellPad, mask3, Matrix.submatrix_apply, finE, finCongr_apply, Fin.coe_cast, if_pos hl]

lemma ellPad_aux_eq (fs : ℕ → ℕ → ℕ → ℕ → ℂ) (fa : ℕ → ℕ → ℕ → ℂ) (la : Fin 5) :
    ellPad fs fa 4 la = (mask6 fa la).submatrix finA finA := by
  ext a b
  simp only [ellPad, mask6, Matrix.submatrix_apply, finA, finCongr_apply, Fin.coe_cast, if_neg not4]

/-! ### The split of `O_w` -/

/-- Site factor of the objective on `Dig 3 4`: `2I − F₀₃`. -/
noncomputable def O3 : Matrix (Dig 3 4) (Dig 3 4) ℂ := (2 : ℂ) • VG ℂ 3 0 0 - VG ℂ 3 0 21

/-- Site factors (the value at the auxiliary factor is replaced below). -/
noncomputable def Gsite : LocM := fun l => if h : l.val < 4 then O3.submatrix (digE h) (digE h) else 1

/-- The local factors of objective component `k`. -/
noncomputable def Gobj (k : ℕ) : LocM := Function.update Gsite 4 ((GAc k).submatrix digA digA)

lemma Gobj_site (k : ℕ) {l : Fin 5} (hl : l.val < 4) : Gobj k l = O3.submatrix (digE hl) (digE hl) := by
  have hne : l ≠ 4 := fun e => by rw [e] at hl; exact not4 hl
  unfold Gobj
  rw [Function.update_of_ne hne]
  exact dif_pos hl

lemma Gobj_aux (k : ℕ) : Gobj k 4 = (GAc k).submatrix digA digA := by
  unfold Gobj
  rw [Function.update_self]

lemma kron_update_apply (G0 : LocM) (M : Matrix (Dig (nfC 4) 4) (Dig (nfC 4) 4) ℂ) (i j : GC) :
    kron (Function.update G0 4 M) i j = M (i 4) (j 4) * ∏ l ∈ Finset.univ.erase 4, G0 l (i l) (j l) := by
  unfold kron
  have h4 : Function.update G0 4 M 4 (i 4) (j 4) = M (i 4) (j 4) := by rw [Function.update_self]
  have hr : ∏ l ∈ Finset.univ.erase 4, Function.update G0 4 M l (i l) (j l) =
      ∏ l ∈ Finset.univ.erase 4, G0 l (i l) (j l) :=
    Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ 4), h4, hr]

lemma kron_update_sum (G0 : LocM) (c : Fin 3 → ℂ) (A : Fin 3 → Matrix (Dig (nfC 4) 4) (Dig (nfC 4) 4) ℂ) :
    kron (Function.update G0 4 (∑ k, c k • A k)) = ∑ k, c k • kron (Function.update G0 4 (A k)) := by
  ext i j
  simp only [kron_update_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]

/-- The weights of the three components. -/
noncomputable def cw (w : Fin 2 → ℝ) : Fin 3 → ℂ := ![((w 0 : ℂ) ^ 2 / 2), ((w 1 : ℂ) ^ 2 / 2), ((w 0 : ℂ) * w 1 / 2)]

lemma w_split (w : Fin 2 → ℝ) (s t : Fin 2) :
    ((w s : ℝ) : ℂ) * ((w t : ℝ) : ℂ) = ∑ k : Fin 3, cw w k * ((GAfac k (fun _ => s) (fun _ => t) : ℤ) : ℂ) := by
  rw [Fin.sum_univ_three]
  fin_cases s <;> fin_cases t <;> simp [cw, GAfac] <;> ring

lemma GAfac_dep (k : ℕ) (z z' : Dig 2 4) : GAfac k z z' = GAfac k (fun _ => z 3) (fun _ => z' 3) := by
  unfold GAfac
  rcases k with _ | _ | k <;> rfl

/-- The auxiliary factor of `D_w O D_w` on `Dig 2 4`. -/
lemma DSD2 (w : Fin 2 → ℝ) :
    diagonal (fun x : Dig 2 4 => ((w (x 3) : ℝ) : ℂ)) * VG ℂ 2 0 21 * diagonal (fun x : Dig 2 4 => ((w (x 3) : ℝ) : ℂ)) =
      ∑ k : Fin 3, cw w k • GAc k := by
  ext z z'
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, GAc, GAi,
    Phys.SymAux.VG0_apply, Int.cast_mul, Int.cast_ite, Int.cast_one, Int.cast_zero]
  have e := w_split w (z 3) (z' 3)
  calc ((w (z 3) : ℝ) : ℂ) * (if z = z' ∘ pinvf 21 then 1 else 0) * ((w (z' 3) : ℝ) : ℂ)
      = (((w (z 3) : ℝ) : ℂ) * ((w (z' 3) : ℝ) : ℂ)) * (if z = z' ∘ pinvf 21 then 1 else 0) := by ring
    _ = ∑ k : Fin 3, cw w k * (((GAfac k z z' : ℤ) : ℂ) * (if z = z' ∘ pinvf 21 then 1 else 0)) := by
        rw [e, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [GAfac_dep k z z']
        ring

/-- **The split of the objective operator.** -/
theorem Ow_split (w : Fin 2 → ℝ) : Ow w = ∑ k : Fin 3, cw w k • kron (Gobj k) := by
  have h1 : Ow w = kron (fun l => DwF w l * (if l.val < 4 then (2 : ℂ) • VG ℂ (nfC l) 0 0 - VG ℂ (nfC l) 0 21
      else VG ℂ (nfC l) 0 21) * DwF w l) := by
    unfold Ow NPT.Cert.Phys.Oobj
    rw [Dw_eq_kron, kron_mul, kron_mul]
  have h2 : (fun l => DwF w l * (if l.val < 4 then (2 : ℂ) • VG ℂ (nfC l) 0 0 - VG ℂ (nfC l) 0 21
      else VG ℂ (nfC l) 0 21) * DwF w l) = Function.update Gsite 4 (∑ k : Fin 3, cw w k • (GAc k).submatrix digA digA) := by
    funext l
    by_cases hl : l.val < 4
    · have hne : l ≠ 4 := fun e => by rw [e] at hl; exact not4 hl
      rw [Function.update_of_ne hne]
      unfold Gsite DwF
      rw [dif_pos hl, dif_pos hl, if_pos hl, Matrix.one_mul, Matrix.mul_one, VG0_site hl, VG0_site hl]
      rfl
    · obtain rfl := fin5_eq4 l hl
      rw [Function.update_self]
      have hD : DwF w 4 = (diagonal (fun x : Dig 2 4 => ((w (x 3) : ℝ) : ℂ))).submatrix digA digA := by
        unfold DwF
        rw [dif_neg not4, Matrix.submatrix_diagonal_equiv]
        rfl
      rw [if_neg not4, hD, VG0_aux, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, DSD2]
      ext a b
      simp only [Matrix.submatrix_apply, Matrix.sum_apply, Matrix.smul_apply]
  rw [h1, h2, kron_update_sum]
  rfl

/-! ### Each component through `lift_c` and the orbits -/

/-- Site and auxiliary entries of objective component `k`. -/
noncomputable def fsO : ℕ → ℕ → ℕ → ℕ → ℂ := fun _ la a b => ((ellO la a b : ℚ) : ℂ)
noncomputable def faO (k : ℕ) : ℕ → ℕ → ℕ → ℂ := fun li a b => ((ellAO k li a b : ℚ) : ℂ)

theorem obj_lift (k : Fin 3) (A : MatA) :
    (kron (Gobj k) * Yp A).trace =
      ∑ τ : Tup (PD 0).fam, pairing (kronR fun l => ellPad fsO (faO k) l (τ l)) (gram (PD 0).fam τ (Yp A)) := by
  refine lift_c (PD 0).fam (Gobj k) (fun l la => ellPad fsO (faO k) l la) (fun l hl p => ?_) (fun X => ?_) (Yp_mem A)
  · rw [Gobj_site k hl, VG0_site hl]
    have he : (fun la => ellPad fsO (faO k) l la) = fun la => (ellO3 la).submatrix (finE hl) (finE hl) := by
      funext la
      rw [ellPad_site_eq fsO (faO k) hl la]
      rfl
    rw [he]
    exact traceAt_site hl O3 (VG ℂ 3 0 p) ellO3 (obj_site3 p)
  · rw [Gobj_aux]
    have he : (fun la => ellPad fsO (faO k) 4 la) = fun la => (mask6 (faO k) la).submatrix finA finA := by
      funext la
      exact ellPad_aux_eq fsO (faO k) la
    rw [he]
    exact traceAt_aux (GAc k) (mask6 (faO k)) (obj_aux2 k) X

lemma fsPerm_fsO (σ : Equiv.Perm (Fin 4)) : fsPerm σ fsO = fsO := by
  funext s
  unfold fsPerm
  split_ifs <;> rfl

lemma padRT {dims : Fin 5 → ℕ} {n : ℕ} {m : Type*} (X : Matrix (Fin n) m ℂ) : (padR dims X)ᵀ = padC dims Xᵀ := by
  ext j μ
  simp only [Matrix.transpose_apply, padR, padC]

lemma padRmul {dims : Fin 5 → ℕ} {n : ℕ} {m m' : Type*} [Fintype m] (X : Matrix (Fin n) m ℂ) (S : Matrix m m' ℂ) :
    padR dims X * S = padR dims (X * S) := by
  ext μ j
  rw [Matrix.mul_apply]
  unfold padR
  cases flatPos dims (n := n) μ <;> simp [Matrix.mul_apply]

lemma WSW_padRC (v j : ℕ) : Wc v * cq' (Sq v j) * (Wc v)ᵀ = padRC (dimsF v) (n := nV v) (cq' (Gflat v j)) := by
  unfold Wc Gflat
  rw [padRmul, padRT, padR_mul_padC, cq'_mul, cq'_mul, cq'_transpose]

/-- **The coset sum of a padded functional at the coordinate `(v, j)` as a flat sum.** -/
theorem coset_flat (v : Fin 175) (j : Fin (vb v).S.length) (fs : ℕ → ℕ → ℕ → ℕ → ℂ) (fa : ℕ → ℕ → ℕ → ℂ) :
    ∑ c : Fin (Dcp.nc v), pairing (kronR fun l => ellPad fs fa l (Dcp.new v c l)) (reindexMI (Dcp.perm v c) (Dcp.WSW v j)) =
      ∑ c : Fin (ncos v), ∑ a : Fin (nV v), ∑ b : Fin (nV v), ((Gflat v j a b : ℚ) : ℂ) *
        ((∏ l ∈ Finset.range 4, fsPerm (permT v c) fs l ((vb v).st.getD l 0) (digL (vb v).dims l a) (digL (vb v).dims l b)) *
          fa (vb v).ai (digL (vb v).dims 4 a) (digL (vb v).dims 4 b)) := by
  refine Finset.sum_congr rfl fun c _ => ?_
  have hnew : (fun l => newT v c (sigHat (permT v c) l)) = tupF v := funext fun l => (cos_ok v v.isLt c c.isLt).1 l
  show pairing (kronR fun l => ellPad fs fa l (newT v c l)) (reindexMI (permT v c) (Wc v * cq' (Sq v j) * (Wc v)ᵀ)) = _
  rw [pairing_reindex_ellPad (permT v c) fs fa (newT v c) (tupF v) hnew, WSW_padRC,
    pairing_flat v (bridge_all v v.isLt).box (dims_ok v v.isLt)]
  rfl

/-- `Σ_i y_i f(i) = Σ_v Σ_j y_(off v + j) f(off v + j)` over the coordinates. -/
lemma sum_vj_coord (A : MatA) (f : ℕ → ℂ) :
    ∑ v : Fin 175, ∑ j : Fin (T v).nb, yvec T A ((T v).off + j.val) * f ((T v).off + j.val) =
      ∑ i ∈ Finset.range 1331, yvec T A i * f i := by
  symm
  have e : ∀ i, yvec T A i * f i = ∑ v : Fin 175, ∑ j : Fin (T v).nb,
      if (T v).off + j.val = i then (T v).yc A j * f ((T v).off + j.val) else 0 := by
    intro i
    simp only [yvec, Finset.sum_mul]
    refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rw [h]
    · rw [zero_mul]
  rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_ite_eq, if_pos, yvec_apply T offDisj_T A v j]
  rw [Finset.mem_range]
  have h1 := off_le v v.isLt
  have h2 : j.val < (vb v).S.length := j.isLt
  have h3 : (T v).off = (vb v).off := rfl
  omega

/-- **The objective components in the coordinates.** -/
theorem obj_coords (k : Fin 3) (A : MatA) :
    (kron (Gobj k) * Yp A).trace =
      ∑ v : Fin 175, ∑ j : Fin (T v).nb, yvec T A ((T v).off + j.val) * ((cobjFlat k v j : ℚ) : ℂ) := by
  rw [obj_lift, psem_sound (PD 0) Dcp Dcp_cos Dcp_inj (fun σ i j => Yp_site_entry σ A i j) (Dcp_out (Yp A))
    (yvec T A) (Dcp_coord A) (fun l la => ellPad fsO (faO k) l la)]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [coset_flat v j fsO (faO k)]
  calc ∑ c : Fin (ncos v), ∑ a : Fin (nV v), ∑ b : Fin (nV v), ((Gflat v j a b : ℚ) : ℂ) *
        ((∏ l ∈ Finset.range 4, fsPerm (permT v c) fsO l ((vb v).st.getD l 0) (digL (vb v).dims l a)
          (digL (vb v).dims l b)) * faO k (vb v).ai (digL (vb v).dims 4 a) (digL (vb v).dims 4 b))
      = ∑ c : Fin (ncos v), ∑ a : Fin (nV v), ∑ b : Fin (nV v), ((Gflat v j a b : ℚ) : ℂ) *
        ((∏ l ∈ Finset.range 4, fsO l ((vb v).st.getD l 0) (digL (vb v).dims l a) (digL (vb v).dims l b)) *
          faO k (vb v).ai (digL (vb v).dims 4 a) (digL (vb v).dims 4 b)) :=
        Finset.sum_congr rfl fun c _ => by rw [fsPerm_fsO]
    _ = ((cobjFlat k v j : ℚ) : ℂ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        unfold cobjFlat fsO faO
        push_cast
        rfl

end NPT.CP3.Inst
