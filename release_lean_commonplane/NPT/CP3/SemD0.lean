import NPT.CP3.Chk.D0Defs
import NPT.CP3.Sem

/-!
# NPT.CP3.SemD0 — the variable-block data as rational matrices, and the D0 facts

For a variable block `v < 150` with `n = nV v` rows (multi-indices over `dims`, `flatMI` order) and `m = mV v` columns:
* `Wq v` is `W_v`; `Wl v` is the left inverse `rinv / rden` supported on the rows `piv`;
* `Pq v p` is the site permutation `(Π_p w)(μ) = w(μ ∘ p)` (`p` indexes `NPT.Brauer.permL`, aux slot fixed);
* `Bq v t = bsig[t] / bden` belongs to the `t`-th stabilizer element `stab[t]`;
* `Sq v j` is the basis matrix `S_j`, `Eu m a b` the symmetric unit, `coefq v a b j` the coefficient of `S_j` in the
  average of `E_ab`.

`d0_facts` derives, from the kernel check `d0OK v = true`, the statements `winv`, `bsig`, `stab`, `span`, `cosets`.
-/

open Matrix BigOperators Finset
open NPT.CP3.Data NPT.CP3.Chk

namespace NPT.CP3.Sem

/-- Number of rows of `W_v`. -/
abbrev nV (v : ℕ) : ℕ := (vb v).W.length
/-- Number of columns of `W_v`. -/
abbrev mV (v : ℕ) : ℕ := mv v

/-- `W_v`. -/
def Wq (v : ℕ) : Matrix (Fin (nV v)) (Fin (mV v)) ℚ := fun a j => (mget (vb v).W a j : ℚ)

/-- The left inverse `W⁺ = rinv / rden` on the rows `piv`. -/
def Wl (v : ℕ) : Matrix (Fin (mV v)) (Fin (nV v)) ℚ :=
  fun j a => ∑ t ∈ range (mV v), if (dv v).piv.getD t 0 = (a : ℕ) then (mget (dv v).rinv j t : ℚ) / (dv v).rden else 0

/-- The site permutation `Π_p`: row `a` has its 1 in column `permRow dims p a` (`μ ↦ μ ∘ p`). -/
def Pq (v p : ℕ) : Matrix (Fin (nV v)) (Fin (nV v)) ℚ :=
  fun a a' => if permRow (vb v).dims p a = (a' : ℕ) then 1 else 0

/-- `B_t = bsig[t] / bden`. -/
def Bq (v t : ℕ) : Matrix (Fin (mV v)) (Fin (mV v)) ℚ :=
  fun u w => (mget ((dv v).bsig.getD t []) u w : ℚ) / (dv v).bden

/-- The basis matrix `S_j`. -/
def Sq (v j : ℕ) : Matrix (Fin (mV v)) (Fin (mV v)) ℚ := fun u w => (mget ((vb v).S.getD j []) u w : ℚ)

/-- The symmetric unit `E_ab` (`e_a e_bᵀ + e_b e_aᵀ` for `a ≠ b`, `e_a e_aᵀ` for `a = b`). -/
def Eu (m a b : ℕ) : Matrix (Fin m) (Fin m) ℚ := fun x y =>
  if a = b then (if (x : ℕ) = a ∧ (y : ℕ) = a then 1 else 0)
  else (if (x : ℕ) = a ∧ (y : ℕ) = b then 1 else 0) + (if (x : ℕ) = b ∧ (y : ℕ) = a then 1 else 0)

/-- The coefficient row of the upper position `(a, b)`. -/
def coefRow (v a b : ℕ) : List Int := (dv v).coef.getD ((ups (mV v)).idxOf (a, b)) []

/-- Coefficient of `S_j` in `|stab|⁻¹ Σ_σ B_σ E_ab B_σᵀ`. -/
def coefq (v a b j : ℕ) : ℚ := ((coefRow v a b).getD j 0 : ℚ) / (dv v).cden

/-! ### From the checks -/

theorem d0OK_spec {v : ℕ} (h : d0OK v = true) :
    cosetsOK v = true ∧ stabOK v = true ∧ wshapeOK v = true ∧ winvOK v = true ∧ bsigShapeOK v = true ∧
      spanShapeOK v = true ∧ (∀ t < (dv v).stab.length, bsigOK1 v t = true) ∧
      ∀ p < (ups (mv v)).length, spanOK1 v p = true := by
  simp only [d0OK, d0LightOK, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem stab_of {v : ℕ} (h : stabOK v = true) (p : ℕ) :
    p ∈ (dv v).stab ↔ p < 24 ∧ ∀ q < 4, (vb v).st.getD ((permOf p).getD q 0) 0 = (vb v).st.getD q 0 := by
  simp only [stabOK, beq_iff_eq] at h
  rw [h, List.mem_filter, List.mem_range]
  simp [isStab, List.all_eq_true, List.mem_range]

theorem cosets_of {v : ℕ} (h : cosetsOK v = true) :
    (∀ e ∈ (vb v).cosets, e.2.length = 4 ∧ (∀ q < 4, q ∈ e.2) ∧ e.1.length = 4 ∧
        ∀ q < 4, e.1.getD (e.2.getD q 0) 0 = (vb v).st.getD q 0) ∧
      ((vb v).cosets.map Prod.fst).Nodup ∧ (vb v).cosets.length * (dv v).stab.length = 24 := by
  simp only [cosetsOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun e he => ?_, h2, h3⟩
  obtain ⟨⟨hp, hl⟩, hq⟩ := h1 e he
  simp [isPerm4] at hp
  refine ⟨hp.1, fun q hq' => hp.2 q hq', hl, fun q hq' => ?_⟩
  simpa using hq q (List.mem_range.2 hq')

/-- `Σ_{a : Fin n} [i = a] f a`. -/
theorem sum_fin_ite {n : ℕ} (i : ℕ) (f : ℕ → ℚ) :
    ∑ a : Fin n, (if i = (a : ℕ) then f a else 0) = if i < n then f i else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun a => if i = a then f a else 0) n, Finset.sum_ite_eq]
  simp [Finset.mem_range]

theorem mget_out {A : List (List Int)} {x : ℕ} (h : A.length ≤ x) (c : ℕ) : mget A x c = 0 := by
  simp [mget, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem winv_of {v : ℕ} (hs : wshapeOK v = true) (h : winvOK v = true) : Wl v * Wq v = 1 := by
  simp only [wshapeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨⟨⟨-, hW⟩, hpl⟩, hpv⟩, hR⟩, hr0⟩ := hs
  obtain ⟨-, hRr⟩ := shapeOK_spec hR
  simp only [winvOK, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  ext j c
  have hrden : ((dv v).rden : ℚ) ≠ 0 := by exact_mod_cast hr0.ne'
  simp only [Matrix.mul_apply, Wl, Wq, Finset.sum_mul]
  rw [Finset.sum_comm]
  have inner : ∀ t ∈ range (mV v), ∑ a : Fin (nV v), (if (dv v).piv.getD t 0 = (a : ℕ) then
      (mget (dv v).rinv j t : ℚ) / (dv v).rden else 0) * (mget (vb v).W a c : ℚ) =
      (mget (dv v).rinv j t : ℚ) / (dv v).rden * (mget (vb v).W ((dv v).piv.getD t 0) c : ℚ) := by
    intro t ht
    have hlt : (dv v).piv.getD t 0 < nV v := by
      have : t < (dv v).piv.length := by rw [hpl]; simpa using ht
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this, Option.getD_some]
      exact hpv _ (List.getElem_mem _)
    simp only [ite_mul, zero_mul]
    rw [sum_fin_ite ((dv v).piv.getD t 0) (fun a => (mget (dv v).rinv j t : ℚ) / (dv v).rden * (mget (vb v).W a c : ℚ)),
      if_pos hlt]
  rw [Finset.sum_congr rfl inner]
  have hdot := h j j.isLt c c.isLt
  rw [dot_eq_sum _ _ (mV v) (hRr j j.isLt) (by simp [hpl])] at hdot
  have hcol : ∀ t ∈ range (mV v), (((dv v).piv.map fun a => (vb v).W.getD a []).map fun row => row.getD c 0).getD t 0 =
      mget (vb v).W ((dv v).piv.getD t 0) c := by
    intro t ht
    have : t < (dv v).piv.length := by rw [hpl]; simpa using ht
    rw [List.map_map, getD_map_of_lt _ _ _ _ 0 this]
    rfl
  have hs2 : ∑ t ∈ range (mV v), ((dv v).rinv.getD j []).getD t 0 *
      (((dv v).piv.map fun a => (vb v).W.getD a []).map fun row => row.getD c 0).getD t 0 =
      ∑ t ∈ range (mV v), mget (dv v).rinv j t * mget (vb v).W ((dv v).piv.getD t 0) c :=
    Finset.sum_congr rfl fun t ht => by rw [hcol t ht]; rfl
  rw [hs2] at hdot
  have e : ∑ t ∈ range (mV v), (mget (dv v).rinv j t : ℚ) / (dv v).rden * (mget (vb v).W ((dv v).piv.getD t 0) c : ℚ) =
      ((∑ t ∈ range (mV v), mget (dv v).rinv j t * mget (vb v).W ((dv v).piv.getD t 0) c : ℤ) : ℚ) / (dv v).rden := by
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  rw [e, hdot]
  simp only [Matrix.one_apply, Fin.ext_iff]
  split_ifs <;> simp [hrden]

theorem wshape_rows {v : ℕ} (hs : wshapeOK v = true) : ∀ a < nV v, ((vb v).W.getD a []).length = mV v := by
  simp only [wshapeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨⟨⟨-, hW⟩, -⟩, -⟩, -⟩, -⟩ := hs
  obtain ⟨hl, hr⟩ := shapeOK_spec hW
  intro a ha
  exact hr a (by rw [← hl]; exact ha)

theorem bsig_of {v t : ℕ} (hs : wshapeOK v = true) (hbs : bsigShapeOK v = true) (ht : t < (dv v).stab.length)
    (h : bsigOK1 v t = true) : Pq v ((dv v).stab.getD t 0) * Wq v = Wq v * Bq v t := by
  simp only [bsigShapeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hbs
  obtain ⟨⟨hbl, hb0⟩, hbsh⟩ := hbs
  have hB : shapeOK ((dv v).bsig.getD t []) (mV v) (mV v) = true := by
    have : t < (dv v).bsig.length := by rw [hbl]; exact ht
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this, Option.getD_some]
    exact hbsh _ (List.getElem_mem _)
  obtain ⟨hBl, -⟩ := shapeOK_spec hB
  simp only [bsigOK1, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  have hbden : ((dv v).bden : ℚ) ≠ 0 := by exact_mod_cast hb0.ne'
  ext a c
  -- left: the permuted row
  have hl : (Pq v ((dv v).stab.getD t 0) * Wq v) a c = (mget (vb v).W (permRow (vb v).dims ((dv v).stab.getD t 0) a) c : ℚ) := by
    simp only [Matrix.mul_apply, Pq, Wq, ite_mul, one_mul, zero_mul]
    rw [sum_fin_ite (permRow (vb v).dims ((dv v).stab.getD t 0) a) (fun a' => (mget (vb v).W a' c : ℚ))]
    split_ifs with hlt
    · rfl
    · rw [mget_out (by simpa [nV] using not_lt.1 hlt)]; simp
  -- right: W B_t
  have hdot := h a a.isLt c c.isLt
  rw [dot_eq_sum _ _ (mV v) (wshape_rows hs a a.isLt) (by rw [List.length_map]; exact hBl)] at hdot
  rw [hl, Matrix.mul_apply]
  simp only [Wq, Bq]
  rw [← Fin.sum_univ_eq_sum_range (fun x => ((vb v).W.getD a []).getD x 0 *
    (((dv v).bsig.getD t []).map fun r => r.getD c 0).getD x 0) (mV v)] at hdot
  have e : ∀ x : Fin (mV v), (((dv v).bsig.getD t []).map fun r => r.getD (c : ℕ) 0).getD x 0 =
      mget ((dv v).bsig.getD t []) x c := by
    intro x
    rw [getD_map_of_lt _ _ _ _ [] (by rw [hBl]; exact x.isLt)]
    rfl
  simp only [e] at hdot
  have hq : ((mget (vb v).W (permRow (vb v).dims ((dv v).stab.getD t 0) ↑a) ↑c : ℤ) : ℚ) =
      ((∑ x : Fin (mV v), mget (vb v).W a x * mget ((dv v).bsig.getD t []) x c : ℤ) : ℚ) / (dv v).bden := by
    rw [show (∑ x : Fin (mV v), mget (vb v).W a x * mget ((dv v).bsig.getD t []) x c) =
      ∑ x : Fin (mV v), ((vb v).W.getD a []).getD x 0 * mget ((dv v).bsig.getD t []) x c from rfl, hdot]
    push_cast
    field_simp
  rw [hq]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

/-- `Σ_{x : Fin m} [x = a] f x = f a`. -/
theorem sum_fin_val_ite {m : ℕ} (a : ℕ) (ha : a < m) (f : Fin m → ℚ) :
    ∑ x : Fin m, (if (x : ℕ) = a then f x else 0) = f ⟨a, ha⟩ := by
  rw [Finset.sum_eq_single (⟨a, ha⟩ : Fin m)]
  · simp
  · intro x _ hx
    rw [if_neg]
    intro h
    exact hx (Fin.ext h)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem sum_unit {m : ℕ} (B : Matrix (Fin m) (Fin m) ℚ) (u y : Fin m) (i j : ℕ) (hi : i < m) :
    ∑ x : Fin m, B u x * (if (x : ℕ) = i ∧ (y : ℕ) = j then 1 else 0) = if (y : ℕ) = j then B u ⟨i, hi⟩ else 0 := by
  by_cases hy : (y : ℕ) = j
  · simp only [hy, and_true, if_true, mul_ite, mul_one, mul_zero]
    exact sum_fin_val_ite i hi (fun x => B u x)
  · simp [hy]

/-- Entries of `B E_ab Bᵀ`. -/
theorem bEbt_apply {m : ℕ} (B : Matrix (Fin m) (Fin m) ℚ) {a b : ℕ} (ha : a < m) (hb : b < m) (u w : Fin m) :
    (B * Eu m a b * Bᵀ) u w = if a = b then B u ⟨a, ha⟩ * B w ⟨a, ha⟩
      else B u ⟨a, ha⟩ * B w ⟨b, hb⟩ + B u ⟨b, hb⟩ * B w ⟨a, ha⟩ := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Eu]
  by_cases hab : a = b
  · subst hab
    have hu : ∀ y : Fin m, ∑ x : Fin m, B u x * (if (x : ℕ) = a ∧ (y : ℕ) = a then 1 else 0) =
        if (y : ℕ) = a then B u ⟨a, ha⟩ else 0 := fun y => sum_unit B u y a a ha
    simp only [if_true, hu, ite_mul, zero_mul]
    exact sum_fin_val_ite a ha (fun y => B u ⟨a, ha⟩ * B w y)
  · have hu1 : ∀ y : Fin m, ∑ x : Fin m, B u x * (if (x : ℕ) = a ∧ (y : ℕ) = b then 1 else 0) =
        if (y : ℕ) = b then B u ⟨a, ha⟩ else 0 := fun y => sum_unit B u y a b ha
    have hu2 : ∀ y : Fin m, ∑ x : Fin m, B u x * (if (x : ℕ) = b ∧ (y : ℕ) = a then 1 else 0) =
        if (y : ℕ) = a then B u ⟨b, hb⟩ else 0 := fun y => sum_unit B u y b a hb
    simp only [hab, if_false, mul_add, Finset.sum_add_distrib, hu1, hu2, add_mul, ite_mul, zero_mul]
    rw [sum_fin_val_ite b hb (fun y => B u ⟨a, ha⟩ * B w y), sum_fin_val_ite a ha (fun y => B u ⟨b, hb⟩ * B w y)]

theorem lsum_map_getD {α : Type*} (f : α → Int) (d : α) :
    ∀ l : List α, lsum (l.map f) = ∑ t ∈ range l.length, f (l.getD t d)
  | [] => by simp [lsum]
  | x :: xs => by
    rw [List.map_cons, lsum, lsum_map_getD f d xs, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

theorem lsum_zip {α β : Type*} (g : α × β → Int) (d1 : α) (d2 : β) :
    ∀ (l1 : List α) (l2 : List β), l1.length = l2.length →
      lsum ((l1.zip l2).map g) = ∑ j ∈ range l1.length, g (l1.getD j d1, l2.getD j d2)
  | [], [], _ => by simp [lsum]
  | x :: xs, y :: ys, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [List.zip_cons_cons, List.map_cons, lsum, lsum_zip g d1 d2 xs ys h, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem mem_ups {m a b : ℕ} : (a, b) ∈ ups m ↔ a ≤ b ∧ b < m := by
  simp only [ups, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨u, hu, t, ht, rfl, rfl⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨a, by omega, b - a, by omega, rfl, by omega⟩

theorem span_of {v a b : ℕ} (hbs : bsigShapeOK v = true) (hss : spanShapeOK v = true)
    (h : ∀ p < (ups (mv v)).length, spanOK1 v p = true) (hab : a ≤ b) (hb : b < mV v) :
    ∑ t ∈ range (dv v).stab.length, Bq v t * Eu (mV v) a b * (Bq v t)ᵀ =
      ((dv v).stab.length : ℚ) • ∑ j ∈ range (vb v).S.length, coefq v a b j • Sq v j := by
  simp only [bsigShapeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hbs
  obtain ⟨⟨hbl, hb0⟩, -⟩ := hbs
  simp only [spanShapeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hss
  obtain ⟨⟨⟨hcl, hcr⟩, hc0⟩, -⟩ := hss
  have hmem : (a, b) ∈ ups (mV v) := mem_ups.2 ⟨hab, hb⟩
  set p := (ups (mV v)).idxOf (a, b) with hp
  have hpl : p < (ups (mV v)).length := List.idxOf_lt_length_of_mem hmem
  have hpe : (ups (mV v)).getD p (0, 0) = (a, b) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpl, Option.getD_some]
    exact List.getElem_idxOf hpl
  have hrow : (coefRow v a b).length = (vb v).S.length := by
    have : p < (dv v).coef.length := by rw [hcl]; exact hpl
    show ((dv v).coef.getD p []).length = _
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem this, Option.getD_some]
    exact hcr _ (List.getElem_mem _)
  have hs := h p hpl
  simp only [spanOK1, List.all_eq_true, List.mem_range, decide_eq_true_eq, hpe] at hs
  have hbden : ((dv v).bden : ℚ) ≠ 0 := by exact_mod_cast hb0.ne'
  have hcden : ((dv v).cden : ℚ) ≠ 0 := by exact_mod_cast hc0.ne'
  have ha : a < mV v := lt_of_le_of_lt hab hb
  ext u w
  set X : ℤ := ∑ t ∈ range (dv v).stab.length, bebt ((dv v).bsig.getD t []) a b u w with hXdef
  set Y : ℤ := ∑ j ∈ range (vb v).S.length, (coefRow v a b).getD j 0 * mget ((vb v).S.getD j []) u w with hYdef
  have e : ((dv v).cden : ℤ) * X = ((dv v).stab.length : ℤ) * (((dv v).bden : ℤ) * (dv v).bden) * Y := by
    have e0 := hs u u.isLt w w.isLt
    have hrow' : ((dv v).coef.getD p []).length = (vb v).S.length := hrow
    rw [lsum_map_getD _ [] (dv v).bsig, hbl, lsum_zip _ 0 [] ((dv v).coef.getD p []) (vb v).S hrow', hrow'] at e0
    exact e0
  have hL : (∑ t ∈ range (dv v).stab.length, Bq v t * Eu (mV v) a b * (Bq v t)ᵀ) u w =
      (X : ℚ) / ((dv v).bden * (dv v).bden) := by
    rw [Matrix.sum_apply, hXdef, Int.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [bEbt_apply _ ha hb]
    simp only [Bq, bebt, Fin.val_mk]
    split_ifs <;> push_cast <;> field_simp
  have hR : (((dv v).stab.length : ℚ) • ∑ j ∈ range (vb v).S.length, coefq v a b j • Sq v j) u w =
      ((dv v).stab.length : ℚ) * ((Y : ℚ) / (dv v).cden) := by
    simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
    rw [hYdef, Int.cast_sum, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [coefq, Sq]
    push_cast
    ring
  rw [hL, hR, mul_div_assoc', div_eq_div_iff (mul_ne_zero hbden hbden) hcden]
  have e' := congrArg (fun z : ℤ => (z : ℚ)) e
  push_cast at e'
  linear_combination e'

/-- The D0 facts of variable block `v`: left inverse, stabilizer relations, the stabilizer itself, the span of the
averaged units, and the coset transversal. -/
def D0Facts (v : ℕ) : Prop :=
    Wl v * Wq v = 1 ∧
    (∀ t < (dv v).stab.length, Pq v ((dv v).stab.getD t 0) * Wq v = Wq v * Bq v t) ∧
    (∀ p, p ∈ (dv v).stab ↔ p < 24 ∧ ∀ q < 4, (vb v).st.getD ((permOf p).getD q 0) 0 = (vb v).st.getD q 0) ∧
    (∀ a b, a ≤ b → b < mV v → ∑ t ∈ range (dv v).stab.length, Bq v t * Eu (mV v) a b * (Bq v t)ᵀ =
      ((dv v).stab.length : ℚ) • ∑ j ∈ range (vb v).S.length, coefq v a b j • Sq v j) ∧
    ((∀ e ∈ (vb v).cosets, e.2.length = 4 ∧ (∀ q < 4, q ∈ e.2) ∧ e.1.length = 4 ∧
        ∀ q < 4, e.1.getD (e.2.getD q 0) 0 = (vb v).st.getD q 0) ∧
      ((vb v).cosets.map Prod.fst).Nodup ∧ (vb v).cosets.length * (dv v).stab.length = 24)

/-- **The D0 facts** of every variable block, from the kernel checks `d0OK v`. -/
theorem d0_of_checks (h : ∀ v < 175, d0OK v = true) : ∀ v < 175, D0Facts v := by
  intro v hv
  obtain ⟨hc, hst, hws, hwi, hbs, hss, hb1, hs1⟩ := d0OK_spec (h v hv)
  exact ⟨winv_of hws hwi, fun t ht => bsig_of hws hbs ht (hb1 t ht), stab_of hst,
    fun a b hab hb => span_of hbs hss hs1 hab hb, cosets_of hc⟩

end NPT.CP3.Sem
