import NPT.CP3.D3Lift
import NPT.CP3.D3Def

/-!
# NPT.CP3.D3Bridge — the D3 computation against the coordinate functionals of `NPT.CP3.D3Def`

From `d3OK v = true` (the integer check of `NPT.CP3.D3Core`) for every tuple `v < 175`:
* `d3_obj_of`: `cobjFlat k v j = 16 · 162⁴ · tN k (off_v + j) / cDen` for `k < 3`;
* `d3_E_of`: `Ecol[off_v + j][e] = 192⁴ · cEFlat e v j` for `e < 146`.
The flat double sums over `Fin (nV v)` are rewritten as lifts of `G = W S_j Wᵀ` in pair layout (`flat_lift`).
-/

open Matrix BigOperators Finset
open NPT.CP3.Ctr NPT.CP3.Data
open NPT.CP3.D1 (digit boxN sq gArr t0Arr lg gArr_spec digit_lt)

namespace NPT.CP3.D3

open NPT.CP3 NPT.CP3.Chk NPT.CP3.Sem NPT.CP3.Inst

set_option maxRecDepth 100000

/-! ### Data facts (kernel) -/

/-- Shape facts of tuple `v` used below. -/
def d3shape (v : Nat) : Bool :=
  (vb v).dims.length == 5 && (List.range 5).all (fun i => decide (0 < (vb v).dims.getD i 1)) &&
    (List.range 4).all (fun l => (vb v).dims.getD l 1 == sdim 0 ((vb v).st.getD l 0) &&
      decide (offL (vb v) l + (vb v).dims.getD l 1 * (vb v).dims.getD l 1 ≤ 23)) &&
    (vb v).dims.getD 4 1 == (ablk 0 (vb v).ai).length && (vb v).W.length == boxN (vb v).dims

theorem d3shape_ok : (List.range 175).all d3shape = true := by decide +kernel

/-- The word tuples of the used rows have four entries below `6`. -/
def eqWordsOK : Bool :=
  (List.range 146).all fun e => (sortedQ.getD (erows.getD e 0 / 70) []).length == 4 &&
    (List.range 4).all fun i => decide ((sortedQ.getD (erows.getD e 0 / 70) []).getD i 0 < 6)

theorem eqWords_ok : eqWordsOK = true := by decide +kernel

theorem dens_ok : ifgDen = 576 ∧ eqDen = 192 := ⟨rfl, rfl⟩

theorem zrA_get {t : ℕ} (ht : t < 23) : zrA.getD t 0 = zr2num t := by
  simp [zrA, Array.getD_eq_getD_getElem?, ht]

/-- The shape facts as propositions. -/
structure Shape (v : ℕ) : Prop where
  len : (vb v).dims.length = 5
  pos : ∀ i < 5, 0 < (vb v).dims.getD i 1
  site : ∀ l < 4, (vb v).dims.getD l 1 = sdim 0 ((vb v).st.getD l 0)
  offb : ∀ l < 4, offL (vb v) l + (vb v).dims.getD l 1 * (vb v).dims.getD l 1 ≤ 23
  aux : (vb v).dims.getD 4 1 = (ablk 0 (vb v).ai).length
  box : (vb v).W.length = boxN (vb v).dims

theorem shape_of {v : ℕ} (hv : v < 175) : Shape v := by
  have h := d3shape_ok
  simp only [List.all_eq_true, List.mem_range] at h
  have hs := h v hv
  simp only [d3shape, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hs
  exact ⟨h1, h2, fun l hl => (h3 l hl).1, fun l hl => (h3 l hl).2, h4, h5⟩

/-! ### Digits, `G`, and the local functionals -/

theorem digL_eq {d : List ℕ} (hd : d.length = 5) {l : ℕ} (hl : l < 5) (t : ℕ) : digL d l t = digit d t l := by
  match d, hd with
  | [d0, d1, d2, d3, d4], _ =>
    interval_cases l <;> simp [digL, placeValL, digit, Nat.mul_comm, Nat.mul_left_comm]

theorem nV_eq {v : ℕ} (hs : Shape v) : nV v = boxN (vb v).dims := hs.box

theorem Gflat_eq {v : ℕ} (hs : Shape v) (j : ℕ) (a b : Fin (nV v)) :
    Gflat v j a b = ((gArr (vb v) j).getD (a.val * boxN (vb v).dims + b.val) 0 : ℚ) := by
  have ha : a.val < boxN (vb v).dims := by rw [← nV_eq hs]; exact a.isLt
  have hb : b.val < boxN (vb v).dims := by rw [← nV_eq hs]; exact b.isLt
  rw [gArr_spec (vb v) j ha hb]
  simp only [Gflat, Matrix.mul_apply, Matrix.transpose_apply, Wq, Sq]
  push_cast
  rw [← Fin.sum_univ_eq_sum_range (fun u => (∑ t ∈ range ((vb v).W.getD 0 []).length,
    (lg (vb v).W a t : ℚ) * (lg ((vb v).S.getD j []) t u : ℚ)) * (lg (vb v).W b u : ℚ))]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun t => (lg (vb v).W a t : ℚ) * (lg ((vb v).S.getD j []) t u : ℚ))]
  rfl

theorem ellO_eq {v : ℕ} (hs : Shape v) {l : ℕ} (hl : l < 4) {a b : ℕ} (ha : a < (vb v).dims.getD l 1)
    (hb : b < (vb v).dims.getD l 1) :
    ellO ((vb v).st.getD l 0) a b = (objM (vb v) l 0 (a * (vb v).dims.getD l 1 + b) : ℚ) / 576 := by
  have hlt : offL (vb v) l + (a * (vb v).dims.getD l 1 + b) < 23 := by
    have h1 := hs.offb l hl
    have h2 : a * (vb v).dims.getD l 1 + b < (vb v).dims.getD l 1 * (vb v).dims.getD l 1 := by
      have := Nat.mul_le_mul_right ((vb v).dims.getD l 1) (Nat.succ_le_of_lt ha)
      rw [Nat.succ_mul] at this
      omega
    omega
  simp only [ellO, zr2, scoord, objM, zrA_get hlt, zr2num, sumRange_eq]
  rw [show (siteOff.getD 0 []).getD ((vb v).st.getD l 0) 0 + a * sdim 0 ((vb v).st.getD l 0) + b =
      offL (vb v) l + (a * (vb v).dims.getD l 1 + b) by rw [hs.site l hl, offL]; ring]
  push_cast
  rfl

theorem ellE_eq {v : ℕ} (hs : Shape v) {l : ℕ} (hl : l < 4) (q a b : ℕ) :
    ellE q ((vb v).st.getD l 0) a b = (eqM (vb v) l q (a * (vb v).dims.getD l 1 + b) : ℚ) / 192 := by
  simp only [ellE, scoord, eqM]
  rw [show (siteOff.getD 0 []).getD ((vb v).st.getD l 0) 0 + a * sdim 0 ((vb v).st.getD l 0) + b =
      offL (vb v) l + (a * (vb v).dims.getD l 1 + b) by rw [hs.site l hl, offL]; ring]
  rfl

theorem ellAO_eq (k li a b : ℕ) : ellAO k li a b = (zaKI k (aunitI li a b) : ℚ) := by
  unfold ellAO zaK zaKI
  rcases k with _ | _ | k <;> simp [aunit, aunitI, unitIdx, ablk]

theorem ellAE_eq (u li a b : ℕ) : ellAE u li a b = ((auxMst.getD u []).getD (aunitI li a b) 0 : ℚ) := by
  simp [ellAE, aunit, aunitI, unitIdx, ablk]

/-! ### The summands -/

lemma dig_lt {d : List ℕ} (hpos : ∀ i < 5, 0 < d.getD i 1) {l : ℕ} (hl : l < 5) (a : ℕ) :
    digit d a l < d.getD l 1 := by
  have h := digit_lt d (p := a) l (by rw [Nat.min_eq_left (by omega)]; exact hpos l hl)
  rwa [Nat.min_eq_left (by omega)] at h

lemma pr4_div {d : List ℕ} (hpos : ∀ i < 5, 0 < d.getD i 1) (a b : ℕ) :
    pr d 4 a b / d.getD 4 1 = digit d a 4 ∧ pr d 4 a b % d.getD 4 1 = digit d b 4 := by
  have hb := dig_lt hpos (by decide : 4 < 5) b
  have h4 := hpos 4 (by decide)
  simp only [pr]
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ h4, Nat.div_eq_of_lt hb, zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]

/-- Objective aux function of the aux pair. -/
def gO (b : VarB) (k x4 : ℕ) : ℚ := (zaKI k (aunitI b.ai (x4 / b.dims.getD 4 1) (x4 % b.dims.getD 4 1)) : ℚ)

/-- Equality aux function of the aux pair. -/
def gE (b : VarB) (u x4 : ℕ) : ℚ :=
  ((auxMst.getD u []).getD (aunitI b.ai (x4 / b.dims.getD 4 1) (x4 % b.dims.getD 4 1)) 0 : ℚ)

/-- The objective summand over flat indices. -/
def objF (b : VarB) (j k a c : ℕ) : ℚ :=
  ((gArr b j).getD (a * boxN b.dims + c) 0 : ℚ) *
    ((objM b 0 0 (pr b.dims 0 a c) : ℚ) * (objM b 1 0 (pr b.dims 1 a c) : ℚ) * (objM b 2 0 (pr b.dims 2 a c) : ℚ) *
      (objM b 3 0 (pr b.dims 3 a c) : ℚ) * gO b k (pr b.dims 4 a c)) / 576 ^ 4

/-- The equality summand over flat indices (coset `c`, word tuple `q`, unit `u`). -/
def eqF (b : VarB) (j : ℕ) (q : List ℕ) (u c a a' : ℕ) : ℚ :=
  ((gArr b j).getD (a * boxN b.dims + a') 0 : ℚ) *
    ((eqM b 0 (wq b q c 0) (pr b.dims 0 a a') : ℚ) * (eqM b 1 (wq b q c 1) (pr b.dims 1 a a') : ℚ) *
      (eqM b 2 (wq b q c 2) (pr b.dims 2 a a') : ℚ) * (eqM b 3 (wq b q c 3) (pr b.dims 3 a a') : ℚ) *
      gE b u (pr b.dims 4 a a')) / 192 ^ 4

theorem obj_summand {v : ℕ} (hs : Shape v) (j k : ℕ) (a b : Fin (nV v)) :
    Gflat v j a b * ((∏ l ∈ range 4, ellO ((vb v).st.getD l 0) (digL (vb v).dims l a) (digL (vb v).dims l b)) *
      ellAO k (vb v).ai (digL (vb v).dims 4 a) (digL (vb v).dims 4 b)) = objF (vb v) j k a b := by
  rw [Gflat_eq hs]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
    digL_eq hs.len (by decide : 0 < 5), digL_eq hs.len (by decide : 1 < 5), digL_eq hs.len (by decide : 2 < 5),
    digL_eq hs.len (by decide : 3 < 5), digL_eq hs.len (by decide : 4 < 5)]
  rw [ellO_eq hs (by decide : 0 < 4) (dig_lt hs.pos (by decide) _) (dig_lt hs.pos (by decide) _),
    ellO_eq hs (by decide : 1 < 4) (dig_lt hs.pos (by decide) _) (dig_lt hs.pos (by decide) _),
    ellO_eq hs (by decide : 2 < 4) (dig_lt hs.pos (by decide) _) (dig_lt hs.pos (by decide) _),
    ellO_eq hs (by decide : 3 < 4) (dig_lt hs.pos (by decide) _) (dig_lt hs.pos (by decide) _), ellAO_eq]
  obtain ⟨q1, q2⟩ := pr4_div hs.pos a b
  simp only [objF, gO, q1, q2]
  simp only [pr]
  ring

theorem wq_lt {e : ℕ} (he : e < 146) (b : VarB) (c m : ℕ) : wq b (eQ e) c m < 6 := by
  have h := eqWords_ok
  simp only [eqWordsOK, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨hl, hq⟩ := h e he
  unfold wq eQ
  by_cases hi : ((b.cosets.getD c default).2).getD m m < 4
  · exact hq _ hi
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simp

theorem eq_summand {v : ℕ} (hs : Shape v) (j e c : ℕ) (a b : Fin (nV v)) :
    Gflat v j a b * ((∏ m ∈ range 4, ellE ((eQ e).getD ((cosE v c).2.getD m m) 0) ((vb v).st.getD m 0)
        (digL (vb v).dims m a) (digL (vb v).dims m b)) *
      ellAE (eU e) (vb v).ai (digL (vb v).dims 4 a) (digL (vb v).dims 4 b)) =
    eqF (vb v) j (eQ e) (eU e) c a b := by
  rw [Gflat_eq hs]
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul,
    digL_eq hs.len (by decide : 0 < 5), digL_eq hs.len (by decide : 1 < 5), digL_eq hs.len (by decide : 2 < 5),
    digL_eq hs.len (by decide : 3 < 5), digL_eq hs.len (by decide : 4 < 5)]
  rw [ellE_eq hs (by decide : 0 < 4), ellE_eq hs (by decide : 1 < 4), ellE_eq hs (by decide : 2 < 4),
    ellE_eq hs (by decide : 3 < 4), ellAE_eq]
  obtain ⟨q1, q2⟩ := pr4_div hs.pos a b
  simp only [eqF, gE, q1, q2]
  simp only [pr, wq, cosE]
  ring

/-! ### The coordinate functionals -/

theorem sum_fin2 (n : ℕ) (f : ℕ → ℕ → ℚ) :
    ∑ a : Fin n, ∑ b : Fin n, f a b = ∑ a ∈ range n, ∑ b ∈ range n, f a b := by
  rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin n, f a b)]
  exact Finset.sum_congr rfl fun a _ => Fin.sum_univ_eq_sum_range (fun b => f a b) n

theorem cobj_eq {v : ℕ} (hs : Shape v) (j k : ℕ) :
    cobjFlat k v j = (ncos v : ℚ) * (objVal (vb v) (objT4 (vb v) (t0Arr (vb v) (gArr (vb v) j))) k : ℚ) / 576 ^ 4 := by
  unfold cobjFlat
  simp only [obj_summand hs]
  rw [sum_fin2 (nV v) (objF (vb v) j k), nV_eq hs]
  have hl := flat_lift (vb v) (gArr (vb v) j) hs.pos 1 1 1 1 (objM (vb v) 0) (objM (vb v) 1) (objM (vb v) 2)
    (objM (vb v) 3) (by decide : 0 < 1) (by decide : 0 < 1) (by decide : 0 < 1) (by decide : 0 < 1) (gO (vb v) k)
  have e1 : ∑ a ∈ range (boxN (vb v).dims), ∑ b ∈ range (boxN (vb v).dims), objF (vb v) j k a b =
      (∑ a ∈ range (boxN (vb v).dims), ∑ b ∈ range (boxN (vb v).dims),
        ((gArr (vb v) j).getD (a * boxN (vb v).dims + b) 0 : ℚ) *
          ((objM (vb v) 0 0 (pr (vb v).dims 0 a b) : ℚ) * (objM (vb v) 1 0 (pr (vb v).dims 1 a b) : ℚ) *
            (objM (vb v) 2 0 (pr (vb v).dims 2 a b) : ℚ) * (objM (vb v) 3 0 (pr (vb v).dims 3 a b) : ℚ) *
            gO (vb v) k (pr (vb v).dims 4 a b))) / 576 ^ 4 := by
    simp only [objF, Finset.sum_div]
  rw [e1, hl]
  unfold objVal
  rw [sumRange_eq]
  push_cast
  rw [mul_div_assoc]
  congr 1
  rw [div_left_inj' (by norm_num)]
  refine Finset.sum_congr rfl fun x4 _ => ?_
  simp only [objT4, gO, zero_mul, zero_add, mul_comm]

/-- The coset-`c` part of `cEFlat` as a lift of `t0Arr`. -/
theorem cE_c {v : ℕ} (hs : Shape v) {e : ℕ} (he : e < 146) (j c : ℕ) :
    ∑ a : Fin (nV v), ∑ b : Fin (nV v), eqF (vb v) j (eQ e) (eU e) c a b =
      (∑ x4 ∈ range (NPT.CP3.D1.sq (vb v).dims 4), gE (vb v) (eU e) x4 *
        ((eqT4 (vb v) (t0Arr (vb v) (gArr (vb v) j))).getD ((((wq (vb v) (eQ e) c 0 * 6 + wq (vb v) (eQ e) c 1) * 6 +
          wq (vb v) (eQ e) c 2) * 6 + wq (vb v) (eQ e) c 3) * NPT.CP3.D1.sq (vb v).dims 4 + x4) 0 : ℚ)) / 192 ^ 4 := by
  rw [sum_fin2 (nV v) (eqF (vb v) j (eQ e) (eU e) c), nV_eq hs]
  unfold eqT4
  rw [← flat_lift (vb v) (gArr (vb v) j) hs.pos 6 6 6 6 (eqM (vb v) 0) (eqM (vb v) 1) (eqM (vb v) 2)
    (eqM (vb v) 3) (wq_lt he (vb v) c 0) (wq_lt he (vb v) c 1) (wq_lt he (vb v) c 2) (wq_lt he (vb v) c 3)
    (gE (vb v) (eU e))]
  simp only [eqF, Finset.sum_div]

/-- `eqVal` over `ℚ`, with the word tuple and unit of the row named. -/
theorem eqVal_cast (b : VarB) (T : Array Int) (e : ℕ) :
    (eqVal b T e : ℚ) = ∑ c ∈ range b.cosets.length, ∑ x4 ∈ range (NPT.CP3.D1.sq b.dims 4), gE b (eU e) x4 *
      (T.getD ((((wq b (eQ e) c 0 * 6 + wq b (eQ e) c 1) * 6 + wq b (eQ e) c 2) * 6 + wq b (eQ e) c 3) *
        NPT.CP3.D1.sq b.dims 4 + x4) 0 : ℚ) := by
  unfold eqVal
  simp only [sumRange_eq, Int.cast_sum, Int.cast_mul, gE, eQ, eU]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun x4 _ => ?_
  ring

theorem cE_eq {v : ℕ} (hs : Shape v) {e : ℕ} (he : e < 146) (j : ℕ) :
    cEFlat e v j = (eqVal (vb v) (eqT4 (vb v) (t0Arr (vb v) (gArr (vb v) j))) e : ℚ) / 192 ^ 4 := by
  unfold cEFlat ncos
  simp only [eq_summand hs, cE_c hs he, eqVal_cast, Finset.sum_div]

/-! ### D3 from the integer check -/

theorem tNI_eq (k i : ℕ) : tNI k i = tN k i := by
  rcases k with _ | _ | k <;> rfl

theorem d3_obj_of (hchk : ∀ v < 175, d3OK v = true) :
    ∀ k < 3, ∀ v < 175, ∀ j < (vb v).S.length,
      cobjFlat k v j = 16 * 162 ^ 4 * (tN k ((vb v).off + j) : ℚ) / cDen := by
  intro k hk v hv j hj
  have hs := shape_of hv
  have h := hchk v hv
  simp only [d3OK, List.all_eq_true, List.mem_range] at h
  have hj' := h j hj
  simp only [d3OKj, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hj'
  have hok : ((vb v).cosets.length : ℤ) * objVal (vb v) (objT4 (vb v) (t0Arr (vb v) (gArr (vb v) j))) k * cDen =
      16 * 162 ^ 4 * 576 ^ 4 * tNI k ((vb v).off + j) := hj'.1 k hk
  rw [cobj_eq hs, ← tNI_eq]
  have hq := congrArg (fun z : ℤ => (z : ℚ)) hok
  push_cast at hq
  have hc : (cDen : ℚ) ≠ 0 := by norm_num [cDen]
  rw [div_eq_div_iff (by norm_num) hc]
  unfold ncos
  linear_combination hq

theorem d3_E_of (hchk : ∀ v < 175, d3OK v = true) :
    ∀ e < 146, ∀ v < 175, ∀ j < (vb v).S.length,
      (((Ecol.getD ((vb v).off + j) []).getD e 0 : ℤ) : ℚ) = 192 ^ 4 * cEFlat e v j := by
  intro e he v hv j hj
  have hs := shape_of hv
  have h := hchk v hv
  simp only [d3OK, List.all_eq_true, List.mem_range] at h
  have hj' := h j hj
  simp only [d3OKj, Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hj'
  have hok : (Ecol.getD ((vb v).off + j) []).getD e 0 = eqVal (vb v) (eqT4 (vb v) (t0Arr (vb v) (gArr (vb v) j))) e :=
    hj'.2 e he
  rw [cE_eq hs he, hok]
  field_simp

end NPT.CP3.D3
