/-
NPT.CP3.D1Inst — D1 for the certificate. Given the native range check `checkRange raw 0 1331 = true`, every data
block coefficient `F_k[i]` (`Sem.Fmat k i`, `k < 302`, `i < 1331`) is `scaleK k` (`1` for cut `()`, `192⁴` for cut
`(3,)`) times the semantic coefficient `Dcp.coordSum (Xk k) i`, where `Xk k v j = V_kᵀ H_k(v, j) V_k` is the compressed
coset sum of `W_v S_j W_vᵀ` (cut `()`), resp. of its lift by `phiPad Pφ` (cut `(3,)`), at the output tuple of `k`.

The finite facts about the lists (`varOK`, `outOK`, list lengths) are kernel decisions.
-/
import NPT.CP3.D1Box
import NPT.CP3.D1Raw
import NPT.CP3.FourierD
import NPT.CP3.Orbits
import NPT.CP3.Checks
import NPT.CP3.SoundR

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem

namespace NPT.CP3.Inst

open NPT.CP3 NPT.CP3.D1 NPT.CP3.Data NPT.CP3.Chk NPT.CP3.Sem

/-! ### The output blocks -/

/-- Output block `k`. -/
def ob (k : ℕ) : OutB := outs.getD k default

/-- Its true dimensions. -/
def dimsO (k : ℕ) : Fin 5 → ℕ := fun l => (ob k).dims.getD l.val 1

/-- Its number of rows. -/
def nO (k : ℕ) : ℕ := boxN (ob k).dims

/-- Its tuple. -/
def oTup (k : ℕ) : Fin 5 → Fin 5 :=
  fun l => Fin.ofNat 5 (if l.val < 4 then (ob k).st.getD l.val 0 else (ob k).ai)

/-- Its basis `V_k` (rows in flat order). -/
noncomputable def Vqk (k : ℕ) : Matrix (Fin (nO k)) (Fin (mOf k)) ℂ := fun p u => ((lg (ob k).V p.val u.val : ℤ) : ℂ)

/-- The padded basis. -/
noncomputable def Vo (k : ℕ) : Matrix MI (Fin (mOf k)) ℂ := padR (dimsO k) (Vqk k)

/-- The scale of block `k`. -/
noncomputable def scaleK (k : ℕ) : ℂ := if (ob k).cut = 0 then 1 else 192 ^ 4

/-- The coset sum of the coordinate `(v, j)` at the output tuple of block `k` (lifted for cut `(3,)`). -/
noncomputable def Hk (k : ℕ) (v : Fin Dcp.nv) (j : Fin (Dcp.m v)) : Matrix MI MI ℂ :=
  if (ob k).cut = 0 then
    ∑ c : Fin (Dcp.nc v), (if Dcp.new v c = oTup k then reindexMI (Dcp.perm v c) (Dcp.WSW v j) else 0)
  else
    ∑ c : Fin (Dcp.nc v), reindexMI (Dcp.perm v c)
      (phiMap (F := (PD 0).fam) (F' := (PD 1).fam) (phiPad Pφ) (fun l => oTup k (sigHat (Dcp.perm v c) l))
        (Dcp.tup v) (Dcp.WSW v j))

/-- The semantic block coefficient of the coordinate `(v, j)`. -/
noncomputable def Xk (k : ℕ) (v : Fin Dcp.nv) (j : Fin (Dcp.m v)) : Matrix (Fin (mOf k)) (Fin (mOf k)) ℂ :=
  (Vo k)ᵀ * Hk k v j * Vo k

/-! ### Finite facts (kernel) -/

theorem vars_len : vars.length = 175 := by decide +kernel

theorem outs_len : outs.length = 302 := by decide +kernel

/-- The facts of a variable block, as a Boolean. -/
def varOK (v : ℕ) : Bool :=
  let b := vb v
  (b.dims.length == 5) &&
  ((List.range 5).all fun l =>
    decide (0 < b.dims.getD l 0) && decide (b.dims.getD l 0 ≤ (if l < 4 then 3 else 6))) &&
  (b.W.length == boxN b.dims) &&
  ((List.range 4).all fun q =>
    decide (b.st.getD q 0 < 4) && ((siteDims.getD 0 []).getD (b.st.getD q 0) 0 == b.dims.getD q 0)) &&
  decide (b.ai < 5) && (auxDims.getD b.ai 0 == b.dims.getD 4 0) &&
  ((List.range 4).all fun q => (List.range (sq b.dims q)).all fun x => decide (off0q raw b q + x < 23)) &&
  ((List.range (sq b.dims 4)).all fun x => (List.range (sq b.dims 4)).all fun y =>
    (auxDest.getD (auxOff.getD b.ai 0 + x) 0 != auxDest.getD (auxOff.getD b.ai 0 + y) 0) || (x == y)) &&
  ((List.range b.cosets.length).all fun c => ((b.cosets.getD c default).1.length == 4) &&
    ((List.range 4).all fun r => decide ((b.cosets.getD c default).1.getD r 0 < 4)) &&
    ((List.range 4).all fun r => decide (sOf (b.cosets.getD c default).2 r < 4)))

theorem varOK_all : (List.range 175).all varOK = true := by decide +kernel

/-- The facts of an output block, as a Boolean. -/
def outOK (k : ℕ) : Bool :=
  let o := ob k
  ((List.range 5).all fun l =>
    decide (0 < o.dims.getD l 1) && decide (o.dims.getD l 1 ≤ (if l < 4 then 3 else 6))) &&
  (o.st.length == 4) && ((List.range 4).all fun q => decide (o.st.getD q 0 < 4)) && decide (o.ai < 5) &&
  (auxDims.getD o.ai 0 == o.dims.getD 4 1) &&
  ((o.cut != 0) || (List.range 4).all fun q => (siteDims.getD 0 []).getD (o.st.getD q 0) 0 == o.dims.getD q 1) &&
  ((o.cut == 0) || ((List.range 4).all fun q => (siteDims.getD 1 []).getD (o.st.getD q 0) 0 == o.dims.getD q 1) &&
    ((List.range 4).all fun q => (List.range (o.dims.getD q 1)).all fun a =>
      (List.range (o.dims.getD q 1)).all fun b =>
        decide (coord (siteOff.getD 1 []) (siteDims.getD 1 []) (o.st.getD q 0) a b < 23)) &&
    ((List.range (o.dims.getD 4 1)).all fun a => (List.range (o.dims.getD 4 1)).all fun b =>
      decide (auxOff.getD o.ai 0 + a * o.dims.getD 4 1 + b < 70)))

theorem outOK_all : (List.range 302).all outOK = true := by decide +kernel

lemma var_facts {v : ℕ} (hv : v < 175) :
    (vb v).dims.length = 5 ∧
    (∀ l < 5, 0 < (vb v).dims.getD l 0 ∧ (vb v).dims.getD l 0 ≤ (if l < 4 then 3 else 6)) ∧
    (vb v).W.length = boxN (vb v).dims ∧
    (∀ q < 4, (vb v).st.getD q 0 < 4 ∧ (siteDims.getD 0 []).getD ((vb v).st.getD q 0) 0 = (vb v).dims.getD q 0) ∧
    ((vb v).ai < 5 ∧ auxDims.getD (vb v).ai 0 = (vb v).dims.getD 4 0) ∧
    (∀ q < 4, ∀ x < sq (vb v).dims q, off0q raw (vb v) q + x < 23) ∧
    (∀ x < sq (vb v).dims 4, ∀ y < sq (vb v).dims 4,
      ¬ auxDest.getD (auxOff.getD (vb v).ai 0 + x) 0 = auxDest.getD (auxOff.getD (vb v).ai 0 + y) 0 ∨ x = y) ∧
    (∀ c < (vb v).cosets.length, (((vb v).cosets.getD c default).1.length = 4 ∧
      (∀ r < 4, ((vb v).cosets.getD c default).1.getD r 0 < 4)) ∧
      ∀ r < 4, sOf ((vb v).cosets.getD c default).2 r < 4) := by
  have h := List.all_eq_true.1 varOK_all v (List.mem_range.2 hv)
  simp only [varOK, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, ⟨h5, h6⟩, h7, h8, h9⟩

lemma out_facts {k : ℕ} (hk : k < 302) :
    (∀ l < 5, 0 < (ob k).dims.getD l 1 ∧ (ob k).dims.getD l 1 ≤ (if l < 4 then 3 else 6)) ∧
    ((ob k).st.length = 4 ∧ (∀ q < 4, (ob k).st.getD q 0 < 4) ∧ (ob k).ai < 5 ∧
      auxDims.getD (ob k).ai 0 = (ob k).dims.getD 4 1) ∧
    (¬ (ob k).cut = 0 ∨ ∀ q < 4, (siteDims.getD 0 []).getD ((ob k).st.getD q 0) 0 = (ob k).dims.getD q 1) ∧
    ((ob k).cut = 0 ∨ ((∀ q < 4, (siteDims.getD 1 []).getD ((ob k).st.getD q 0) 0 = (ob k).dims.getD q 1) ∧
      (∀ q < 4, ∀ a < (ob k).dims.getD q 1, ∀ b < (ob k).dims.getD q 1,
        coord (siteOff.getD 1 []) (siteDims.getD 1 []) ((ob k).st.getD q 0) a b < 23)) ∧
      (∀ a < (ob k).dims.getD 4 1, ∀ b < (ob k).dims.getD 4 1,
        auxOff.getD (ob k).ai 0 + a * (ob k).dims.getD 4 1 + b < 70)) := by
  have h := List.all_eq_true.1 outOK_all k (List.mem_range.2 hk)
  simp only [outOK, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, ⟨h2, h3, h4, h5⟩, h6, h7⟩

lemma block_m {k : ℕ} (hk : k < 302) : (ob k).m = mOf k := (blockOK_spec (blocks_all k hk)).2.1.symm

/-! ### The facts of the bridges -/

lemma phiH : PhiH raw Pφ := ⟨rfl, rfl, rfl, rfl, rfl⟩

lemma tupFv {v : ℕ} (hv : v < 175) (q : Fin 5) (hq : q.val < 4) : (tupF v q).val = (vb v).st.getD q.val 0 := by
  have h := ((var_facts hv).2.2.2.1 q.val hq).1
  show (if q.val < 4 then (vb v).st.getD q.val 0 else (vb v).ai) % 5 = _
  rw [if_pos hq, Nat.mod_eq_of_lt (lt_trans h (by norm_num))]

lemma tupFv4 {v : ℕ} (hv : v < 175) : (tupF v 4).val = (vb v).ai := by
  have h := (var_facts hv).2.2.2.2.1.1
  show (if (4 : Fin 5).val < 4 then (vb v).st.getD (4 : Fin 5).val 0 else (vb v).ai) % 5 = _
  rw [if_neg (by decide), Nat.mod_eq_of_lt h]

theorem varH_of {v : ℕ} (hv : v < 175) : VarH raw Pφ (vb v) (dimsF v) (nV v) (tupF v) := by
  obtain ⟨hlen, hdim, hW, hst, hai, hoff, hinj, hcs⟩ := var_facts hv
  have hL : ∀ l : Fin 5, dimsF v l = (vb v).dims.getD l.val 1 := by
    intro l
    have hl : l.val < (vb v).dims.length := by rw [hlen]; exact l.isLt
    show (vb v).dims.getD l.val 0 = (vb v).dims.getD l.val 1
    rw [getD_lt _ _ _ hl, getD_lt _ _ _ hl]
  have hd : ∀ l : Fin 5, dimsF v l ≤ dpad l := fun l => (hdim l.val l.isLt).2
  have hpos : ∀ l : Fin 5, 0 < dimsF v l := fun l => (hdim l.val l.isLt).1
  have hn : nV v = boxN (vb v).dims := hW
  refine ⟨?_, hL, hd, hpos, hn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hn]
    exact boxOK_of (dimsF v) (vb v).dims hL hd hpos
  · intro q hq
    rw [tupFv hv q hq]
    exact hst q.val hq
  · intro q hq
    exact tupFv hv q hq
  · rw [tupFv4 hv]
    exact hai.2
  · exact tupFv4 hv
  · exact hoff
  · intro x y hx hy he
    exact (hinj x hx y hy).resolve_left (not_not.2 he)
  · intro c hc r hr
    exact (hcs c hc).2 r hr

lemma oTupv {k : ℕ} (hk : k < 302) (q : Fin 5) (hq : q.val < 4) : (oTup k q).val = (ob k).st.getD q.val 0 := by
  have h := (out_facts hk).2.1.2.1 q.val hq
  show (if q.val < 4 then (ob k).st.getD q.val 0 else (ob k).ai) % 5 = _
  rw [if_pos hq, Nat.mod_eq_of_lt (lt_trans h (by norm_num))]

lemma oTupv4 {k : ℕ} (hk : k < 302) : (oTup k 4).val = (ob k).ai := by
  have h := (out_facts hk).2.1.2.2.1
  show (if (4 : Fin 5).val < 4 then (ob k).st.getD (4 : Fin 5).val 0 else (ob k).ai) % 5 = _
  rw [if_neg (by decide), Nat.mod_eq_of_lt h]

lemma dimsO_le {k : ℕ} (hk : k < 302) : ∀ l : Fin 5, dimsO k l ≤ dpad l :=
  fun l => ((out_facts hk).1 l.val l.isLt).2

lemma dimsO_pos {k : ℕ} (hk : k < 302) : ∀ l : Fin 5, 0 < dimsO k l :=
  fun l => ((out_facts hk).1 l.val l.isLt).1

theorem outH_of {k : ℕ} (hk : k < 302) (hc : ¬ (ob k).cut = 0) : OutH raw Pφ (ob k) (dimsO k) (nO k) (oTup k) := by
  obtain ⟨-, ⟨-, hst, -, hax⟩, -, h3⟩ := out_facts hk
  obtain ⟨⟨hsd, ht⟩, he⟩ := h3.resolve_left hc
  refine ⟨boxOK_of (dimsO k) (ob k).dims (fun _ => rfl) (dimsO_le hk) (dimsO_pos hk), fun _ => rfl, rfl, ?_, ?_,
    oTupv4 hk, ?_, ?_, dimsO_pos hk⟩
  · intro m hm
    rw [oTupv hk m hm]
    exact ⟨hst m.val hm, hsd m.val hm, rfl⟩
  · rw [oTupv4 hk]
    exact hax
  · intro m hm a b ha hb
    rw [oTupv hk m hm]
    exact ht m.val hm a ha b hb
  · intro a b ha hb
    exact he a ha b hb

theorem outH0_of {k : ℕ} (hk : k < 302) (hc : (ob k).cut = 0) : OutH0 Pφ (ob k) (dimsO k) (nO k) (oTup k) := by
  obtain ⟨-, ⟨-, -, -, hax⟩, h2, -⟩ := out_facts hk
  have hsd := h2.resolve_left (not_not.2 hc)
  refine ⟨boxOK_of (dimsO k) (ob k).dims (fun _ => rfl) (dimsO_le hk) (dimsO_pos hk), fun _ => rfl, rfl, ?_, ?_⟩
  · intro m hm
    rw [oTupv hk m hm]
    exact hsd m.val hm
  · rw [oTupv4 hk]
    exact hax

/-- The coset tuples meet the output tuple exactly when the lists agree. -/
lemma hnew_of (v : Fin Dcp.nv) {k : ℕ} (hk : k < 302) (c : Fin (vb v).cosets.length) :
    Dcp.new v c = oTup k ↔ (((vb v).cosets.getD c.val default).1 = (ob k).st ∧ (vb v).ai = (ob k).ai) := by
  have hv : v.val < 175 := v.isLt
  obtain ⟨⟨hcl, hce⟩, -⟩ := (var_facts hv).2.2.2.2.2.2.2 c.val c.isLt
  obtain ⟨-, ⟨hlen, hst, hai, -⟩, -, -⟩ := out_facts hk
  exact tup_eq_iff hcl hlen (fun r hr => lt_trans (hce r hr) (by norm_num))
    (fun r hr => lt_trans (hst r hr) (by norm_num)) (var_facts hv).2.2.2.2.1.1 hai

/-! ### The coordinate matrices -/

lemma WSW_eq (v : Fin Dcp.nv) (j : Fin (Dcp.m v)) :
    Dcp.WSW v j = padRC (dimsF v) ((Wq v * Sq v j * (Wq v)ᵀ).map fun q => (q : ℂ)) := by
  show Wc v * cq' (Sq v j) * (Wc v)ᵀ = _
  unfold Wc
  rw [padR_WSW, ← cq'_transpose, ← cq'_mul, ← cq'_mul]
  rfl

lemma Gq_eq {v : ℕ} (hv : v < 175) (j : ℕ) (a b : Fin (nV v)) :
    (Wq v * Sq v j * (Wq v)ᵀ) a b = (((gArr (vb v) j).getD (a.val * nV v + b.val) 0 : ℤ) : ℚ) := by
  have hn : nV v = boxN (vb v).dims := (var_facts hv).2.2.1
  have e : a.val * nV v + b.val = a.val * boxN (vb v).dims + b.val := congrArg (fun x => a.val * x + b.val) hn
  rw [e, gArr_spec (vb v) j (a := a.val) (b := b.val) (lt_of_lt_of_eq a.isLt hn) (lt_of_lt_of_eq b.isLt hn)]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Wq, Sq]
  push_cast
  simp only [Finset.sum_range]
  rfl

/-- The coordinate sum of `Dcp` at a coordinate owned by `(v, j)`. -/
lemma coordSum_Dcp {M : Type*} [AddCommMonoid M] (X : (v : Fin Dcp.nv) → Fin (Dcp.m v) → M) (v : Fin Dcp.nv)
    (j : Fin (Dcp.m v)) {i : ℕ} (hi : Dcp.off v + j.val = i) : Dcp.coordSum X i = X v j := by
  unfold OrbitData.coordSum
  rw [Finset.sum_eq_single v]
  · rw [Finset.sum_eq_single j]
    · rw [if_pos hi]
    · intro j' _ hj'
      rw [if_neg]
      intro h
      apply hj'
      apply Fin.ext
      omega
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro v' _ hv'
    refine Finset.sum_eq_zero fun j' _ => ?_
    rw [if_neg]
    intro h
    have hj : j.val < (vb v).S.length := j.isLt
    have hj' : j'.val < (vb v').S.length := j'.isLt
    have h1 : (vb v).off + j.val = i := hi
    have h2 : (vb v').off + j'.val = i := h
    have hd := off_disjoint v v.isLt v' v'.isLt (fun e => hv' (Fin.ext e).symm)
    have m1 : i ∈ Finset.Ico (vb v).off ((vb v).off + (vb v).S.length) := Finset.mem_Ico.2 ⟨by omega, by omega⟩
    have m2 : i ∈ Finset.Ico (vb v').off ((vb v').off + (vb v').S.length) := Finset.mem_Ico.2 ⟨by omega, by omega⟩
    exact Finset.disjoint_left.mp hd m1 m2
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- An entry of the data block coefficient as an entry of the list computed by `fData`. -/
lemma Fmat_entry {k : ℕ} (hk : k < 302) (i : ℕ) (u w : Fin (mOf k)) :
    crm (Fmat k i) u w = ((lg (fData raw (raw.Fc.getD i []) k (raw.outs.getD k default)) u.val w.val : ℤ) : ℂ) := by
  have hm : (raw.outs.getD k default).m = mOf k := block_m hk
  have hu : u.val < (raw.outs.getD k default).m := by rw [hm]; exact u.isLt
  have hw : w.val < (raw.outs.getD k default).m := by rw [hm]; exact w.isLt
  have e : ∀ a b : ℤ, (((a : ℝ) * (b : ℝ) : ℝ) : ℂ) = ((a * b : ℤ) : ℂ) := by
    intro a b
    push_cast
    ring
  unfold lg
  simp only [fData]
  rw [getD_range_map _ _ hu, getD_range_map _ _ hw]
  simp only [crm, Matrix.map_apply, Fmat]
  rw [e, hm]
  rfl

/-! ### D1 -/

/-- **D1:** every data block coefficient is the scale times the semantic coefficient. -/
theorem d1_block (hnat : checkRange raw 0 1331 = true) {k : ℕ} (hk : k < 302) {i : ℕ} (hi : i < 1331) :
    crm (Fmat k i) = scaleK k • Dcp.coordSum (Xk k) i := by
  -- the variable owning the coordinate
  have hcc := checkRange_coord raw hnat (Nat.zero_le i) hi
  obtain ⟨vB, j, hvar⟩ : ∃ vB j, varOf raw i = some (vB, j) := by
    unfold checkCoord at hcc
    cases hv : varOf raw i with
    | none => rw [hv] at hcc; cases hcc
    | some p => exact ⟨p.1, p.2, rfl⟩
  obtain ⟨hmem, hlo, hhi, hj⟩ := varOf_spec hvar
  obtain ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.1 hmem
  have hidx' : idx < 175 := by
    have h1 : idx < vars.length := hidx
    rwa [vars_len] at h1
  have hvb : vb idx = vB := by
    show vars.getD idx default = vB
    rw [getD_lt vars idx default hidx]
    exact hget
  subst hvb
  subst hj
  obtain ⟨v, hv⟩ : ∃ v : Fin Dcp.nv, v.val = idx := ⟨⟨idx, hidx'⟩, rfl⟩
  subst hv
  have hjm : i - (vb v).off < Dcp.m v := by
    show i - (vb v).off < (vb v).S.length
    omega
  obtain ⟨jj, hjj⟩ : ∃ jj : Fin (Dcp.m v), jj.val = i - (vb v).off := ⟨⟨_, hjm⟩, rfl⟩
  rw [← hjj] at hvar
  have hij : Dcp.off v + jj.val = i := by
    show (vb v).off + jj.val = i
    omega
  rw [coordSum_Dcp (Xk k) v jj hij]
  ext u w
  have hkl : k < raw.outs.length := by
    have h1 : raw.outs.length = 302 := outs_len
    rw [h1]
    exact hk
  rw [Matrix.smul_apply, smul_eq_mul, Fmat_entry hk i u w, ← checkRange_sound raw hnat (Nat.zero_le i) hi hvar hkl]
  have hob : raw.outs.getD k default = ob k := rfl
  rw [hob]
  have hm : (ob k).m = mOf k := block_m hk
  have hσ : ∀ (c : Fin (vb v).cosets.length) (r : Fin 4),
      (Dcp.perm v c r).val = sOf ((vb v).cosets.getD c.val default).2 r.val := fun c r => Dcp_perm v c r
  unfold fOutVJ
  by_cases hc : (ob k).cut = 0
  · -- cut ()
    rw [if_pos hc]
    have e := fOut0_bridge' raw (vb v) jj.val (ob k) Pφ (varH_of v.isLt) (Wq v * Sq v jj * (Wq v)ᵀ)
      (Gq_eq v.isLt jj.val) (outH0_of hk hc) (fun c => Dcp.perm v c) hσ (fun c => Dcp.new v c) (hnew_of v hk)
      (fun c => Dcp_cos v c) hm (Vqk k) (fun _ _ => rfl) u w
    have eX : Xk k v jj u w = (((fOut0 (vb v) (gArr (vb v) jj.val) (ob k)).getD u.val []).getD w.val 0 : ℂ) := by
      unfold Xk Hk
      rw [if_pos hc, WSW_eq]
      exact e
    rw [eX]
    unfold scaleK
    rw [if_pos hc, one_mul]
    rfl
  · -- cut (3,)
    rw [if_neg hc]
    have e := fOut3_bridge' raw (vb v) jj.val (ob k) (P0 := PD 0) (P3 := PD 1) Pφ phiH (varH_of v.isLt)
      (Wq v * Sq v jj * (Wq v)ᵀ) (Gq_eq v.isLt jj.val) (outH_of hk hc) (fun c => Dcp.perm v c) hσ hm (Vqk k)
      (fun _ _ => rfl) u w
    have eX : Xk k v jj u w = (((fOut3 raw (vb v) (t4Arr raw (flatOf raw.phiNum 23 23) (vb v)
        (t0Arr (vb v) (gArr (vb v) jj.val))) (xInv raw (vb v)) (ob k)).getD u.val []).getD w.val 0 : ℂ) / 192 ^ 4 := by
      unfold Xk Hk
      rw [if_neg hc, WSW_eq]
      exact e
    rw [eX]
    unfold scaleK
    rw [if_neg hc, mul_div_192]
    rfl

end NPT.CP3.Inst
