/-
NPT.CP3.D1Spec — the entries of the D1 computation of `NPT.CP3.D1Core` as finite sums over the list data.
-/
import NPT.CP3.Contract

open NPT.CP3.Ctr NPT.CP3.Data

namespace NPT.CP3.D1

/-- Entry of a list matrix (`0` outside). -/
def lg (A : List (List Int)) (u w : ℕ) : Int := (A.getD u []).getD w 0

lemma getD_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) (d : α) {i : ℕ} (hi : i < n) :
    (Array.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [Array.size_ofFn]; exact hi), Option.getD_some,
    Array.getElem_ofFn]

lemma lt_of_rc {r c u w : ℕ} (hu : u < r) (hw : w < c) : u * c + w < r * c := by
  have : (u + 1) * c ≤ r * c := Nat.mul_le_mul_right c hu
  nlinarith

lemma rc_div {c u w : ℕ} (hw : w < c) : (u * c + w) / c = u := by
  have hc : 0 < c := by omega
  rw [add_comm, Nat.add_mul_div_right _ _ hc, Nat.div_eq_of_lt hw, zero_add]

lemma rc_mod {c u w : ℕ} (hw : w < c) : (u * c + w) % c = w := by
  rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hw]

lemma flatOf_spec (A : List (List Int)) (r c : ℕ) {u w : ℕ} (hu : u < r) (hw : w < c) :
    (flatOf A r c).getD (u * c + w) 0 = lg A u w := by
  unfold flatOf
  rw [getD_ofFn _ _ (lt_of_rc hu hw)]
  simp only [lg, rc_div hw, rc_mod hw]

lemma getD_range_map {β : Type*} (f : ℕ → β) (d : β) {m u : ℕ} (hu : u < m) :
    ((List.range m).map f).getD u d = f u := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hu]
  rfl

/-- **Entries of `G = W S Wᵀ`.** -/
theorem gArr_spec (v : VarB) (j : ℕ) {a b : ℕ} (ha : a < boxN v.dims) (hb : b < boxN v.dims) :
    (gArr v j).getD (a * boxN v.dims + b) 0 =
      ∑ u ∈ Finset.range (v.W.getD 0 []).length, (∑ t ∈ Finset.range (v.W.getD 0 []).length,
        lg v.W a t * lg (v.S.getD j []) t u) * lg v.W b u := by
  unfold gArr
  dsimp only
  rw [getD_ofFn _ _ (lt_of_rc ha hb)]
  dsimp only
  rw [sumRange_eq]
  refine Finset.sum_congr rfl fun u hu => ?_
  have hu' : u < (v.W.getD 0 []).length := Finset.mem_range.1 hu
  rw [rc_div hb, rc_mod hb, getD_ofFn _ _ (lt_of_rc ha hu')]
  dsimp only
  rw [sumRange_eq, rc_div hu', rc_mod hu', flatOf_spec _ _ _ hb hu']
  congr 1
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' : t < (v.W.getD 0 []).length := Finset.mem_range.1 ht
  rw [flatOf_spec _ _ _ ha ht', flatOf_spec _ _ _ ht' hu']

/-- Mixed-radix decoding of a five-digit index. -/
lemma decode5 {s1 s2 s3 n4 x0 x1 x2 x3 x4 : ℕ} (h1 : x1 < s1) (h2 : x2 < s2) (h3 : x3 < s3) (h4 : x4 < n4) :
    let t := (((x0 * s1 + x1) * s2 + x2) * s3 + x3) * n4 + x4
    t / (n4 * s3 * s2 * s1) = x0 ∧ t / (n4 * s3 * s2) % s1 = x1 ∧ t / (n4 * s3) % s2 = x2 ∧ t / n4 % s3 = x3 ∧
      t % n4 = x4 := by
  intro t
  have hn4 : 0 < n4 := by omega
  have hs3 : 0 < s3 := by omega
  have hs2 : 0 < s2 := by omega
  have hs1 : 0 < s1 := by omega
  have e4 : t / n4 = ((x0 * s1 + x1) * s2 + x2) * s3 + x3 := rc_div h4
  have e3 : t / (n4 * s3) = (x0 * s1 + x1) * s2 + x2 := by
    rw [← Nat.div_div_eq_div_mul, e4, rc_div h3]
  have e2 : t / (n4 * s3 * s2) = x0 * s1 + x1 := by
    rw [← Nat.div_div_eq_div_mul, e3, rc_div h2]
  refine ⟨?_, ?_, ?_, ?_, rc_mod h4⟩
  · rw [← Nat.div_div_eq_div_mul, e2, rc_div h1]
  · rw [e2, rc_mod h1]
  · rw [e3, rc_mod h2]
  · rw [e4, rc_mod h3]

lemma lt5 {s0 s1 s2 s3 n4 x0 x1 x2 x3 x4 : ℕ} (h0 : x0 < s0) (h1 : x1 < s1) (h2 : x2 < s2) (h3 : x3 < s3)
    (h4 : x4 < n4) : (((x0 * s1 + x1) * s2 + x2) * s3 + x3) * n4 + x4 < s0 * s1 * s2 * s3 * n4 :=
  lt_of_rc (lt_of_rc (lt_of_rc (lt_of_rc h0 h1) h2) h3) h4

/-- **Entries of the per-factor layout.** -/
theorem t0Arr_spec (v : VarB) (G : Array Int) {x0 x1 x2 x3 x4 : ℕ} (h0 : x0 < sq v.dims 0) (h1 : x1 < sq v.dims 1)
    (h2 : x2 < sq v.dims 2) (h3 : x3 < sq v.dims 3) (h4 : x4 < sq v.dims 4) :
    (t0Arr v G).getD ((((x0 * sq v.dims 1 + x1) * sq v.dims 2 + x2) * sq v.dims 3 + x3) * sq v.dims 4 + x4) 0 =
      G.getD (flat5 v.dims (x0 / v.dims.getD 0 1) (x1 / v.dims.getD 1 1) (x2 / v.dims.getD 2 1)
        (x3 / v.dims.getD 3 1) (x4 / v.dims.getD 4 1) * boxN v.dims +
        flat5 v.dims (x0 % v.dims.getD 0 1) (x1 % v.dims.getD 1 1) (x2 % v.dims.getD 2 1)
        (x3 % v.dims.getD 3 1) (x4 % v.dims.getD 4 1)) 0 := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := decode5 (x0 := x0) h1 h2 h3 h4
  unfold t0Arr
  dsimp only
  rw [getD_ofFn _ _ (lt5 h0 h1 h2 h3 h4)]
  dsimp only
  rw [e0, e1, e2, e3, e4]

/-- **Entries of the lifted array.** -/
theorem t4Arr_spec (R : Raw) (phA : Array Int) (v : VarB) (T0 : Array Int) {t0 t1 t2 t3 x4 : ℕ} (h0 : t0 < 23)
    (h1 : t1 < 23) (h2 : t2 < 23) (h3 : t3 < 23) (h4 : x4 < sq v.dims 4) :
    (t4Arr R phA v T0).getD ((((t0 * 23 + t1) * 23 + t2) * 23 + t3) * sq v.dims 4 + x4) 0 =
      ∑ x3 ∈ Finset.range (sq v.dims 3), phA.getD (t3 * 23 + (R.siteOff.getD 0 []).getD (v.st.getD 3 0) 0 + x3) 0 *
      ∑ x2 ∈ Finset.range (sq v.dims 2), phA.getD (t2 * 23 + (R.siteOff.getD 0 []).getD (v.st.getD 2 0) 0 + x2) 0 *
      ∑ x1 ∈ Finset.range (sq v.dims 1), phA.getD (t1 * 23 + (R.siteOff.getD 0 []).getD (v.st.getD 1 0) 0 + x1) 0 *
      ∑ x0 ∈ Finset.range (sq v.dims 0), phA.getD (t0 * 23 + (R.siteOff.getD 0 []).getD (v.st.getD 0 0) 0 + x0) 0 *
        T0.getD ((((x0 * sq v.dims 1 + x1) * sq v.dims 2 + x2) * sq v.dims 3 + x3) * sq v.dims 4 + x4) 0 := by
  unfold t4Arr
  dsimp only
  exact lift4_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 h4

/-- **Entries of `Vᵀ H V`.** -/
theorem vhv_spec (H : Array Int) (V : List (List Int)) (n' m : ℕ) {u w : ℕ} (hu : u < m) (hw : w < m) :
    ((vhv H V n' m).getD u []).getD w 0 =
      ∑ p ∈ Finset.range n', lg V p u * ∑ q ∈ Finset.range n', H.getD (p * n' + q) 0 * lg V q w := by
  unfold vhv
  dsimp only
  rw [getD_range_map _ _ hu, getD_range_map _ _ hw, sumRange_eq]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p < n' := Finset.mem_range.1 hp
  rw [flatOf_spec _ _ _ hp' hu, getD_ofFn _ _ (lt_of_rc hp' hw)]
  dsimp only
  rw [sumRange_eq, rc_div hw, rc_mod hw]
  congr 1
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [flatOf_spec _ _ _ (Finset.mem_range.1 hq) hw]

/-- `xInv` finds a preimage under `auxDest`, or reports `n4` when there is none. -/
theorem xInv_spec (R : Raw) (v : VarB) {e : ℕ} (he : e < 70) :
    ((xInv R v).getD e (sq v.dims 4) < sq v.dims 4 →
      R.auxDest.getD (R.auxOff.getD v.ai 0 + (xInv R v).getD e (sq v.dims 4)) 0 = e) ∧
    ((∀ x < sq v.dims 4, R.auxDest.getD (R.auxOff.getD v.ai 0 + x) 0 ≠ e) →
      (xInv R v).getD e (sq v.dims 4) = sq v.dims 4) := by
  unfold xInv
  dsimp only
  rw [getD_ofFn _ _ he]
  dsimp only
  constructor
  · intro hlt
    cases hf : (List.range (sq v.dims 4)).find? (fun x => R.auxDest.getD (R.auxOff.getD v.ai 0 + x) 0 == e) with
    | none => rw [hf] at hlt; simp at hlt
    | some x =>
      have := List.find?_some hf
      simp only [beq_iff_eq] at this
      simpa [hf] using this
  · intro hno
    have : (List.range (sq v.dims 4)).find? (fun x => R.auxDest.getD (R.auxOff.getD v.ai 0 + x) 0 == e) = none := by
      rw [List.find?_eq_none]
      intro x hx
      simp only [beq_iff_eq]
      exact hno x (List.mem_range.1 hx)
    rw [this]
    rfl

/-! ### The output blocks -/

lemma toArray_getD {α : Type*} (l : List α) (i : ℕ) (d : α) : l.toArray.getD i d = l.getD i d := by
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

lemma zeroM_get {m u w : ℕ} (hu : u < m) (hw : w < m) : ((zeroM m).getD u []).getD w 0 = 0 := by
  unfold zeroM
  rw [getD_range_map _ _ hu, getD_range_map _ _ hw]

/-- The cut-`(3,)` coordinate read for site `a` of the output block at the entry `(p, q)`. -/
def sCoord (R : Raw) (o : OutB) (p q a : ℕ) : ℕ :=
  (R.siteOff.getD 1 []).getD (o.st.getD a 0) 0 + digit o.dims p a * o.dims.getD a 1 + digit o.dims q a

/-- Entry `(p, q)` of `H` of a cut-`(3,)` block, before the projection by `V`. -/
def h3Entry (R : Raw) (v : VarB) (T4 : Array Int) (XI : Array Nat) (o : OutB) (p q : ℕ) : Int :=
  if XI.getD (R.auxOff.getD o.ai 0 + digit o.dims p 4 * o.dims.getD 4 1 + digit o.dims q 4) (sq v.dims 4) <
      sq v.dims 4 then
    ∑ c ∈ Finset.range v.cosets.length,
      T4.getD ((((sCoord R o p q (sOf (v.cosets.getD c default).2 0) * 23 +
        sCoord R o p q (sOf (v.cosets.getD c default).2 1)) * 23 +
        sCoord R o p q (sOf (v.cosets.getD c default).2 2)) * 23 +
        sCoord R o p q (sOf (v.cosets.getD c default).2 3)) * sq v.dims 4 +
        XI.getD (R.auxOff.getD o.ai 0 + digit o.dims p 4 * o.dims.getD 4 1 + digit o.dims q 4) (sq v.dims 4)) 0
  else 0

/-- Whether some auxiliary entry of the output block has a preimage. -/
def auxHit (R : Raw) (v : VarB) (XI : Array Nat) (o : OutB) : Bool :=
  (List.range (o.dims.getD 4 1 * o.dims.getD 4 1)).any fun t =>
    XI.getD (R.auxOff.getD o.ai 0 + t) (sq v.dims 4) < sq v.dims 4

/-- **Entries of a cut-`(3,)` block coefficient.** -/
theorem fOut3_spec (R : Raw) (v : VarB) (T4 : Array Int) (XI : Array Nat) (o : OutB)
    (hs : ∀ c < v.cosets.length, ∀ r < 4, sOf (v.cosets.getD c default).2 r < 4) {u w : ℕ} (hu : u < o.m)
    (hw : w < o.m) :
    ((fOut3 R v T4 XI o).getD u []).getD w 0 =
      if auxHit R v XI o = true then ∑ p ∈ Finset.range (boxN o.dims), lg o.V p u *
        ∑ q ∈ Finset.range (boxN o.dims), h3Entry R v T4 XI o p q * lg o.V q w else 0 := by
  unfold fOut3 auxHit
  dsimp only
  split_ifs with h
  · rw [vhv_spec _ _ _ _ hu hw]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : p < boxN o.dims := Finset.mem_range.1 hp
    congr 1
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' : q < boxN o.dims := Finset.mem_range.1 hq
    congr 1
    rw [getD_ofFn _ _ (lt_of_rc hp' hq')]
    dsimp only
    rw [rc_div hq', rc_mod hq', getD_ofFn _ _ (lt_of_rc hp' (by norm_num : 4 < 5)),
      getD_ofFn _ _ (lt_of_rc hq' (by norm_num : 4 < 5))]
    dsimp only
    rw [rc_div (by norm_num : 4 < 5), rc_mod (by norm_num : 4 < 5), rc_div (by norm_num : 4 < 5),
      rc_mod (by norm_num : 4 < 5)]
    unfold h3Entry
    split_ifs with hx
    · rw [sumRange_eq, List.size_toArray]
      refine Finset.sum_congr rfl fun c hc => ?_
      have hc' : c < v.cosets.length := Finset.mem_range.1 hc
      have hcs : c < v.cosets.toArray.size := by rw [List.size_toArray]; exact hc'
      have hax : ∀ r < 4, (Array.ofFn (n := v.cosets.length * 4) fun t =>
          sOf (v.cosets.toArray.getD (t.val / 4) default).2 (t.val % 4)).getD (c * 4 + r) 0 =
          sOf (v.cosets.getD c default).2 r := by
        intro r hr
        rw [getD_ofFn _ _ (lt_of_rc hc' hr)]
        dsimp only
        rw [rc_div hr, rc_mod hr, toArray_getD]
      have hrb : ∀ a < 4, (Array.ofFn (n := boxN o.dims * 4) fun t =>
          (R.siteOff.getD 1 []).getD (o.st.getD (t.val % 4) 0) 0 +
            digit o.dims (t.val / 4) (t.val % 4) * o.dims.getD (t.val % 4) 1).getD (p * 4 + a) 0 =
          (R.siteOff.getD 1 []).getD (o.st.getD a 0) 0 + digit o.dims p a * o.dims.getD a 1 := by
        intro a ha
        rw [getD_ofFn _ _ (lt_of_rc hp' ha)]
        dsimp only
        rw [rc_div ha, rc_mod ha]
      have hdg : ∀ a < 4, (Array.ofFn (n := boxN o.dims * 5) fun t => digit o.dims (t.val / 5) (t.val % 5)).getD
          (q * 5 + a) 0 = digit o.dims q a := by
        intro a ha
        rw [getD_ofFn _ _ (lt_of_rc hq' (by omega : a < 5))]
        dsimp only
        rw [rc_div (by omega : a < 5), rc_mod (by omega : a < 5)]
      have h0 := hs c hc' 0 (by norm_num)
      have h1 := hs c hc' 1 (by norm_num)
      have h2 := hs c hc' 2 (by norm_num)
      have h3 := hs c hc' 3 (by norm_num)
      have hax0 := hax 0 (by norm_num)
      rw [Nat.add_zero] at hax0
      rw [hax0, hax 1 (by norm_num), hax 2 (by norm_num), hax 3 (by norm_num),
        hrb _ h0, hrb _ h1, hrb _ h2, hrb _ h3, hdg _ h0, hdg _ h1, hdg _ h2, hdg _ h3]
      rfl
    · rfl
  · rw [zeroM_get hu hw]

lemma sum_map_eq_range {α : Type*} [Inhabited α] (l : List α) (f : α → ℤ) :
    (l.map f).sum = ∑ c ∈ Finset.range l.length, f (l.getD c default) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- Entry `(p, q)` of `H` of a cut-`()` block, before the projection by `V`. -/
def h0Entry (v : VarB) (G : Array Int) (o : OutB) (p q : ℕ) : Int :=
  ∑ c ∈ Finset.range v.cosets.length,
    if (v.cosets.getD c default).1 = o.st then
      G.getD (flat5 v.dims (digit o.dims p (sOf (v.cosets.getD c default).2 0))
        (digit o.dims p (sOf (v.cosets.getD c default).2 1)) (digit o.dims p (sOf (v.cosets.getD c default).2 2))
        (digit o.dims p (sOf (v.cosets.getD c default).2 3)) (digit o.dims p 4) * boxN v.dims +
        flat5 v.dims (digit o.dims q (sOf (v.cosets.getD c default).2 0))
        (digit o.dims q (sOf (v.cosets.getD c default).2 1)) (digit o.dims q (sOf (v.cosets.getD c default).2 2))
        (digit o.dims q (sOf (v.cosets.getD c default).2 3)) (digit o.dims q 4)) 0
    else 0

/-- **Entries of a cut-`()` block coefficient.** -/
theorem fOut0_spec (v : VarB) (G : Array Int) (o : OutB) {u w : ℕ} (hu : u < o.m) (hw : w < o.m) :
    ((fOut0 v G o).getD u []).getD w 0 =
      if (v.ai == o.ai && v.cosets.any (fun c => c.1 == o.st)) = true then
        ∑ p ∈ Finset.range (boxN o.dims), lg o.V p u *
          ∑ q ∈ Finset.range (boxN o.dims), h0Entry v G o p q * lg o.V q w else 0 := by
  unfold fOut0
  split_ifs with h
  · dsimp only
    rw [vhv_spec _ _ _ _ hu hw]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : p < boxN o.dims := Finset.mem_range.1 hp
    congr 1
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' : q < boxN o.dims := Finset.mem_range.1 hq
    congr 1
    rw [getD_ofFn _ _ (lt_of_rc hp' hq')]
    dsimp only
    rw [rc_div hq', rc_mod hq', sum_map_eq_range]
    unfold h0Entry
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [beq_iff_eq]
  · rw [zeroM_get hu hw]

end NPT.CP3.D1
