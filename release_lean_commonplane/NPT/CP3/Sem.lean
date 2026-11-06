import NPT.CP3.Chk.Lemmas
import NPT.Cert.PsdSound

/-!
# NPT.CP3.Sem — the certificate as real matrices, and the two facts the soundness proof uses

For an active block `k < 302` with `m = mOf k`, `r = rOf k`:
* `Ymat k = Yi / 2^s + dYn / D` (`r × r`), `Nmat k` (`2m × r`), `Zmat k = Nmat k * Ymat k * (Nmat k)ᵀ`;
* `part c Z` is `Z11`, `Z22`, `Z12 + Z21ᵀ` for `c = 0, 1, ≥ 2` (blocks of size `m`);
* `Fmat k i` is `F_k[i]`: `fScale[cut k]` times the symmetric matrix read from the row of block `k` in `Fc[i]`
  (0 if there is no such row);
* `Erow e i = E[erows[e], i]`, `lam c e = lamN[c][e] / D`, `cvec c i = ca[i], cb[i], 2 cab[i]`.

`psd_of_checks` and `ident_of_checks` derive `Ymat k ⪰ 0` and the three identities from the kernel checks of
`NPT.CP3.Chk.Defs`.
-/

open Matrix BigOperators Finset
open scoped ComplexOrder
open NPT.CP3.Data NPT.CP3.Chk NPT.Cert

namespace NPT.CP3.Sem

/-- Certificate of active block `k`. -/
def cb (k : ℕ) : CertB := certs.getD k default
/-- Block size `m` of block `k`. -/
def mOf (k : ℕ) : ℕ := (cb k).m
/-- Face rank `r` of block `k`. -/
def rOf (k : ℕ) : ℕ := (cb k).r

/-- `Y_k = Yi / 2^s + dYn / D`. -/
noncomputable def Ymat (k : ℕ) : Matrix (Fin (rOf k)) (Fin (rOf k)) ℝ :=
  fun i j => (mget (cb k).Yi i j : ℝ) / 2 ^ (cb k).s + (mget (cb k).dYn i j : ℝ) / (D : ℝ)

/-- `N_k` (`2m × r`). -/
noncomputable def Nmat (k : ℕ) : Matrix (Fin (2 * mOf k)) (Fin (rOf k)) ℝ := fun u t => (mget (cb k).N u t : ℝ)

/-- `Z_k = N_k Y_k N_kᵀ`. -/
noncomputable def Zmat (k : ℕ) : Matrix (Fin (2 * mOf k)) (Fin (2 * mOf k)) ℝ := Nmat k * Ymat k * (Nmat k)ᵀ

/-- Part `c` of a `2m × 2m` matrix: `Z11` (`c = 0`), `Z22` (`c = 1`), `Z12 + Z21ᵀ` (`c ≥ 2`). -/
def part {m : ℕ} (c : ℕ) (Z : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun u v =>
    if c = 0 then Z ⟨u.val, by have := u.isLt; omega⟩ ⟨v.val, by have := v.isLt; omega⟩
    else if c = 1 then Z ⟨m + u.val, by have := u.isLt; omega⟩ ⟨m + v.val, by have := v.isLt; omega⟩
    else Z ⟨u.val, by have := u.isLt; omega⟩ ⟨m + v.val, by have := v.isLt; omega⟩ +
      Z ⟨m + v.val, by have := v.isLt; omega⟩ ⟨u.val, by have := u.isLt; omega⟩

/-- The row of block `k` at coordinate `i`: the tail of the first row of `Fc[i]` with head `k`, or `[]`. -/
def frow (k i : ℕ) : List Int :=
  (((Fc.getD i []).find? fun row => decide (row.headD (-1) = (k : Int))).map List.tail).getD []

/-- `F_k[i]` as a symmetric real matrix. -/
noncomputable def Fmat (k i : ℕ) : Matrix (Fin (mOf k)) (Fin (mOf k)) ℝ :=
  fun u v => (gk k : ℝ) * (lookupZ ((ups (mOf k)).zip (frow k i)) (min u.val v.val, max u.val v.val) : ℝ)

/-- `E[erows[e], i]`. -/
noncomputable def Erow (e i : ℕ) : ℝ := ((Ecol.getD i []).getD e 0 : ℝ)
/-- `λ_c[e] = lamN[c][e] / D`. -/
noncomputable def lam (c e : ℕ) : ℝ := ((lamN.getD c []).getD e 0 : ℝ) / (D : ℝ)
/-- `ca[i]`, `cb[i]`, `2 cab[i]` for `c = 0, 1, 2`. -/
noncomputable def cvec (c i : ℕ) : ℝ := (tN c i : ℝ) / (cDen : ℝ)

theorem Fmat_symm (k i : ℕ) (u v : Fin (mOf k)) : Fmat k i u v = Fmat k i v u := by
  simp only [Fmat, min_comm, max_comm]

/-! ### List facts -/

theorem getD_of_lt {α : Type*} (l : List α) (n : ℕ) (d : α) (h : n < l.length) : l.getD n d = l[n] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_map_of_lt {α β : Type*} (l : List α) (f : α → β) (n : ℕ) (d : β) (d' : α) (h : n < l.length) :
    (l.map f).getD n d = f (l.getD n d') := by
  rw [getD_of_lt _ _ _ (by simpa using h), getD_of_lt _ _ _ h, List.getElem_map]

/-- Shape predicate as a Prop. -/
theorem shapeOK_spec {A : List (List Int)} {r c : ℕ} (h : shapeOK A r c = true) :
    A.length = r ∧ ∀ i < r, (A.getD i []).length = c := by
  simp only [shapeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  refine ⟨h.1, fun i hi => ?_⟩
  rw [getD_of_lt _ _ _ (by omega)]
  simpa using h.2 _ (List.getElem_mem (by omega))

/-- Entries of `N X Nᵀ`. -/
theorem mget_nxnt {N X : List (List Int)} {a r : ℕ} (hN : shapeOK N a r = true) (hX : shapeOK X r r = true)
    {i j : ℕ} (hi : i < a) (hj : j < a) :
    mget (nxnt N X) i j = ∑ t ∈ range r, ∑ t' ∈ range r, mget N i t * mget X t t' * mget N j t' := by
  obtain ⟨hNl, hNr⟩ := shapeOK_spec hN
  obtain ⟨hXl, hXr⟩ := shapeOK_spec hX
  unfold mget nxnt
  simp only
  rw [getD_map_of_lt _ _ _ _ [] (by omega), getD_map_of_lt _ _ _ _ [] (by simpa using (by omega : j < N.length))]
  rw [getD_map_of_lt _ _ _ _ [] (by omega)]
  rw [dot_eq_sum _ _ r (hNr i hi) (by simp [hXl])]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [getD_map_of_lt _ _ _ _ [] (by simp at ht; omega), dot_eq_sum _ _ r (hXr t (by simpa using ht)) (hNr j hj),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun t' _ => ?_
  ring

/-- Entries of `D·Y`. -/
theorem mget_DYm {b : CertB} (hY : shapeOK b.Yi b.r b.r = true) (hd : shapeOK b.dYn b.r b.r = true) {i j : ℕ}
    (hi : i < b.r) (hj : j < b.r) :
    mget (DYm b) i j = mget b.Yi i j * Int.ofNat (D / 2 ^ b.s) + mget b.dYn i j := by
  obtain ⟨hYl, hYr⟩ := shapeOK_spec hY
  obtain ⟨hdl, hdr⟩ := shapeOK_spec hd
  have hi1 : i < b.Yi.length := by omega
  have hi2 : i < b.dYn.length := by omega
  have hj1 : j < (b.Yi.getD i []).length := by rw [hYr i hi]; exact hj
  have hj2 : j < (b.dYn.getD i []).length := by rw [hdr i hi]; exact hj
  set f : Int → Int → Int := fun y e => y * Int.ofNat (D / 2 ^ b.s) + e with hf
  have hrow : (DYm b).getD i [] = List.zipWith f (b.Yi.getD i []) (b.dYn.getD i []) := by
    have hl : i < (List.zipWith (List.zipWith f) b.Yi b.dYn).length := by
      rw [List.length_zipWith]; exact lt_min hi1 hi2
    show (List.zipWith (List.zipWith f) b.Yi b.dYn).getD i [] = _
    rw [getD_of_lt (List.zipWith (List.zipWith f) b.Yi b.dYn) i [] hl, List.getElem_zipWith,
      getD_of_lt b.Yi i [] hi1, getD_of_lt b.dYn i [] hi2]
  have hl2 : j < (List.zipWith f (b.Yi.getD i []) (b.dYn.getD i [])).length := by
    rw [List.length_zipWith]; exact lt_min hj1 hj2
  unfold mget
  rw [hrow, getD_of_lt (List.zipWith f (b.Yi.getD i []) (b.dYn.getD i [])) j 0 hl2, List.getElem_zipWith,
    getD_of_lt (b.Yi.getD i []) j 0 hj1, getD_of_lt (b.dYn.getD i []) j 0 hj2]

/-! ### Positive semidefiniteness -/

theorem blockOK_spec {k : ℕ} (h : blockOK k = true) :
    (cb k).idx = (outs.getD k default).idx ∧ (cb k).m = (outs.getD k default).m ∧ (outs.getD k default).cut < 2 ∧
      shapeOK (cb k).N (2 * mOf k) (rOf k) = true ∧ shapeOK (cb k).Yi (rOf k) (rOf k) = true ∧
      shapeOK (cb k).dYn (rOf k) (rOf k) = true ∧ D % 2 ^ (cb k).s = 0 := by
  simp only [blockOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- `D·Y_k = q_k Yi + dYn` entrywise over ℝ. -/
theorem D_mul_Ymat {k : ℕ} (hb : blockOK k = true) (i j : Fin (rOf k)) :
    (D : ℝ) * Ymat k i j = (mget (cb k).Yi i j : ℝ) * (qk k : ℝ) + (mget (cb k).dYn i j : ℝ) := by
  obtain ⟨-, -, -, -, -, -, hs⟩ := blockOK_spec hb
  have hD : (0 : ℝ) < D := by
    have : 0 < D := by decide
    exact_mod_cast this
  have hq : ((qk k : Int) : ℝ) = (D : ℝ) / 2 ^ (cb k).s := by
    simp only [qk, cb] at hs ⊢
    rw [Int.ofNat_eq_natCast, Int.cast_natCast, Nat.cast_div (Nat.dvd_of_mod_eq_zero hs) (by positivity)]
    push_cast; ring
  rw [hq]
  simp only [Ymat]
  field_simp

theorem psd_of_checks (hb : ∀ k < 302, blockOK k = true) (h : ∀ k < 302, psdOK k = true) :
    ∀ k < 302, (Ymat k).PosSemidef := by
  intro k hk
  obtain ⟨-, -, -, -, hY, hd, -⟩ := blockOK_spec (hb k hk)
  have hc := PBlock.check_sound (pblockOf k) (h k hk)
  -- the PBlock matrix is `D·Y` (no corrections), as a complex matrix
  set A : Matrix (Fin (rOf k)) (Fin (rOf k)) ℝ := fun i j => (mget (DYm (cb k)) i j : ℝ) with hA
  have hZ : (pblockOf k).Zmat 1 = A.map fun x : ℝ => (x : ℂ) := by
    ext i j
    change ((((pblockOf k).zget i j : ℚ) / 2 ^ (pblockOf k).E + (pblockOf k).uval 1 i j : ℚ) : ℂ) =
      ((A i j : ℝ) : ℂ)
    simp [PBlock.zget, PBlock.uval, PBlock.ufind, pblockOf, hA, mget, cb]
  have hApsd : A.PosSemidef := psd_of_complex A (by rw [← hZ]; exact hc)
  have hD : (0 : ℝ) < D := by
    have : 0 < D := by decide
    exact_mod_cast this
  have hY' : Ymat k = (1 / (D : ℝ)) • A := by
    ext i j
    have e := D_mul_Ymat (hb k hk) i j
    have e2 : (mget (DYm (cb k)) i j : ℝ) = (mget (cb k).Yi i j : ℝ) * (qk k : ℝ) + (mget (cb k).dYn i j : ℝ) := by
      rw [mget_DYm hY hd i.isLt j.isLt]
      simp only [qk, cb]
      push_cast
      ring
    rw [Matrix.smul_apply, smul_eq_mul]
    simp only [hA]
    rw [e2, ← e]
    field_simp
  rw [hY']
  exact hApsd.smul (by positivity)

/-! ### The identity -/

/-- Tail of the first row with head `k`, or `[]`. -/
def ftail (rows : List (List Int)) (k : ℕ) : List Int :=
  ((rows.find? fun row => decide (row.headD (-1) = (k : Int))).map List.tail).getD []

theorem frow_eq (k i : ℕ) : frow k i = ftail (Fc.getD i []) k := rfl

theorem ftail_nil (k : ℕ) : ftail [] k = [] := rfl

theorem ftail_cons (x : Int) (xs : List Int) (rest : List (List Int)) (k : ℕ) :
    ftail ((x :: xs) :: rest) k = if x = (k : Int) then xs else ftail rest k := by
  by_cases h : x = (k : Int) <;> simp [ftail, List.find?_cons, h]

/-- A row accepted by `headsOK` starts with its (nonnegative) block index. -/
theorem headsOK_cons {lo : ℕ} {row : List Int} {rest : List (List Int)} (h : headsOK lo (row :: rest) = true) :
    ∃ x xs, row = x :: xs ∧ 0 ≤ x ∧ lo ≤ x.toNat ∧ x.toNat < 302 ∧ headsOK (x.toNat + 1) rest = true := by
  simp only [headsOK, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  cases row with
  | nil => simp at h0
  | cons x xs => exact ⟨x, xs, rfl, by simpa using h0, by simpa using h1, by simpa using h2, by simpa using h3⟩

theorem ftail_lt : ∀ {lo : ℕ} {rows : List (List Int)}, headsOK lo rows = true → ∀ k < lo, ftail rows k = []
  | _, [], _, _, _ => rfl
  | lo, row :: rest, h, k, hk => by
      obtain ⟨x, xs, rfl, h0, h1, -, h3⟩ := headsOK_cons h
      rw [ftail_cons, if_neg (by omega)]
      exact ftail_lt h3 k (by omega)

theorem sum_rows (φ : ℕ → List Int → Int) (hφ : ∀ k, φ k [] = 0) :
    ∀ {lo : ℕ} {rows : List (List Int)}, headsOK lo rows = true →
      lsum (rows.map fun row => φ (row.headD 0).toNat row.tail) = ∑ k ∈ Ico lo 302, φ k (ftail rows k)
  | lo, [], _ => by simp [lsum, ftail_nil, hφ]
  | lo, row :: rest, h => by
      obtain ⟨x, xs, rfl, h0, h1, h2, h3⟩ := headsOK_cons h
      set k0 := x.toNat with hk0
      have hx : x = (k0 : Int) := by omega
      rw [List.map_cons, lsum, sum_rows φ hφ h3]
      simp only [List.headD_cons, List.tail_cons]
      rw [← Finset.sum_Ico_consecutive _ h1 h2.le, Finset.sum_eq_sum_Ico_succ_bot h2]
      have hlow : ∑ k ∈ Ico lo k0, φ k (ftail ((x :: xs) :: rest) k) = 0 := by
        refine Finset.sum_eq_zero fun k hk => ?_
        rw [Finset.mem_Ico] at hk
        rw [ftail_cons, if_neg (by omega), ftail_lt h3 k (by omega), hφ]
      have hhigh : ∑ k ∈ Ico (k0 + 1) 302, φ k (ftail ((x :: xs) :: rest) k) =
          ∑ k ∈ Ico (k0 + 1) 302, φ k (ftail rest k) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [Finset.mem_Ico] at hk
        rw [ftail_cons, if_neg (by omega)]
      rw [hlow, hhigh, ftail_cons, if_pos hx, zero_add]

/-- Sum over an upper-triangle row against weighted entries, as a full symmetric sum. -/
theorem dot_wup (f : List Int) (Z : List (List Int)) (m c : ℕ) :
    dot f (wup Z m c) = ∑ u ∈ range m, ∑ v ∈ range m,
      lookupZ ((ups m).zip f) (min u v, max u v) * pentry Z m c u v := by
  set E := (ups m).zip f with hE
  have hsub : (E.map Prod.fst).Sublist (ups m) := by
    rw [hE]
    clear hE E
    induction (ups m) generalizing f with
    | nil => simp
    | cons a l ih =>
      cases f with
      | nil => simp
      | cons b f => simpa using (ih f).cons₂ a
  have hkeys : (E.map Prod.fst).Nodup := (ups_nodup m).sublist hsub
  rw [wup, dot_map_zip, ← hE, sum_zip_lookup _ E hkeys]
  -- extend the sum over the keys to all upper positions (absent keys have value 0)
  have hext : ((E.map Prod.fst).map fun q => lookupZ E q * wentry Z m c q).sum =
      ((ups m).map fun q => lookupZ E q * wentry Z m c q).sum := by
    rw [← List.sum_toFinset _ hkeys, ← List.sum_toFinset _ (ups_nodup m)]
    refine Finset.sum_subset (fun q hq => List.mem_toFinset.2 (hsub.subset (List.mem_toFinset.1 hq))) ?_
    intro q _ hq
    have hnone : (E.find? fun e => decide (e.1 = q)) = none := by
      rw [List.find?_eq_none]
      intro e he
      simp only [decide_eq_true_eq]
      intro heq
      exact hq (List.mem_toFinset.2 (List.mem_map.2 ⟨e, he, heq⟩))
    simp [lookupZ, hnone]
  rw [hext, sum_ups]
  have := upper_sym m (fun q => lookupZ E q) (fun u v => pentry Z m c u v)
  simpa [wentry] using this

/-- `D (N Y Nᵀ)_{ab} = q (N Yi Nᵀ)_{ab} + (N dYn Nᵀ)_{ab}`. -/
theorem D_mul_Zmat {k : ℕ} (hb : blockOK k = true) (a b : Fin (2 * mOf k)) :
    (D : ℝ) * Zmat k a b = (qk k : ℝ) * (mget (nxnt (cb k).N (cb k).Yi) a b : ℝ) +
      (mget (nxnt (cb k).N (cb k).dYn) a b : ℝ) := by
  obtain ⟨-, -, -, hN, hY, hd, -⟩ := blockOK_spec hb
  rw [mget_nxnt hN hY a.isLt b.isLt, mget_nxnt hN hd a.isLt b.isLt]
  push_cast
  simp only [Finset.sum_range]
  have key : ∀ t t' : Fin (rOf k), (qk k : ℝ) * ((mget (cb k).N a t : ℝ) * (mget (cb k).Yi t t' : ℝ) *
      (mget (cb k).N b t' : ℝ)) + (mget (cb k).N a t : ℝ) * (mget (cb k).dYn t t' : ℝ) * (mget (cb k).N b t' : ℝ) =
      (D : ℝ) * ((mget (cb k).N a t : ℝ) * Ymat k t t' * (mget (cb k).N b t' : ℝ)) := by
    intro t t'
    have e := D_mul_Ymat hb t t'
    linear_combination (mget (cb k).N a t : ℝ) * (mget (cb k).N b t' : ℝ) * e.symm
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  have hz : Zmat k a b = ∑ t : Fin (rOf k), ∑ t' : Fin (rOf k),
      (mget (cb k).N a t : ℝ) * Ymat k t t' * (mget (cb k).N b t' : ℝ) := by
    simp only [Zmat, Matrix.mul_apply, Matrix.transpose_apply, Nmat, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hz, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact (Finset.sum_congr rfl fun t' _ => key t t').symm

/-- The parts of `D·Z` in terms of the stored products. -/
theorem pentry_part {k c : ℕ} (hb : blockOK k = true) (hc : c < 3) (u v : Fin (mOf k)) :
    (qk k : ℝ) * (pentry (nxnt (cb k).N (cb k).Yi) (mOf k) c u v : ℝ) +
      (pentry (nxnt (cb k).N (cb k).dYn) (mOf k) c u v : ℝ) = (D : ℝ) * part c (Zmat k) u v := by
  have hu := u.isLt
  have hv := v.isLt
  interval_cases c
  · have h := D_mul_Zmat hb ⟨u, by omega⟩ ⟨v, by omega⟩
    simp only [Fin.val_mk] at h
    simp only [pentry, part, ↓reduceIte]
    linear_combination -h
  · have h := D_mul_Zmat hb ⟨mOf k + u, by omega⟩ ⟨mOf k + v, by omega⟩
    simp only [Fin.val_mk] at h
    have hp : part 1 (Zmat k) u v = Zmat k ⟨mOf k + u, by omega⟩ ⟨mOf k + v, by omega⟩ := rfl
    rw [hp]
    simp only [pentry]
    linear_combination -h
  · have h1 := D_mul_Zmat hb ⟨u, by omega⟩ ⟨mOf k + v, by omega⟩
    have h2 := D_mul_Zmat hb ⟨mOf k + v, by omega⟩ ⟨u, by omega⟩
    simp only [Fin.val_mk] at h1 h2
    simp only [pentry, part, ↓reduceIte]
    push_cast
    linear_combination -h1 - h2

/-- The contribution of block `k` (row tail `f`) to component `c`. -/
def rterm (c k : ℕ) (f : List Int) : Int :=
  gk k * (qk k * dot f ((zwOf k).1.getD c []) + dot f ((zwOf k).2.getD c []))

theorem rterm_nil (c k : ℕ) : rterm c k [] = 0 := by simp [rterm, dot_nil_left]

theorem zw_get {k c : ℕ} (hz : zdOK k = true) (hc : c < 3) :
    (zwOf k).1.getD c [] = wup (nxnt (cb k).N (cb k).Yi) (mOf k) c ∧
      (zwOf k).2.getD c [] = wup (nxnt (cb k).N (cb k).dYn) (mOf k) c := by
  simp only [zdOK, Bool.and_eq_true, beq_iff_eq] at hz
  obtain ⟨h1, h2⟩ := hz
  rw [h1, h2]
  interval_cases c <;> simp [wparts, mOf, cb]

theorem rterm_eq {k c i : ℕ} (hb : blockOK k = true) (hz : zdOK k = true) (hc : c < 3) :
    (rterm c k (frow k i) : ℝ) = (D : ℝ) * ∑ u : Fin (mOf k), ∑ v : Fin (mOf k), Fmat k i u v * part c (Zmat k) u v := by
  obtain ⟨hS, hB⟩ := zw_get hz hc
  rw [rterm, hS, hB, dot_wup, dot_wup]
  push_cast
  simp only [Finset.sum_range, Finset.mul_sum, ← Finset.sum_add_distrib, mul_add]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  simp only [Fmat]
  linear_combination ((gk k : ℝ) * (lookupZ ((ups (mOf k)).zip (frow k i)) (min ↑u ↑v, max ↑u ↑v) : ℝ)) *
    pentry_part hb hc u v

theorem globOK_spec (h : globOK = true) :
    shapeOK Ecol 1331 146 = true ∧ shapeOK lamN 3 146 = true ∧ D % cDen = 0 ∧ 0 < D ∧ 0 < cDen := by
  simp only [globOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, h6⟩, h7⟩, _⟩, _⟩, _⟩, _⟩, h12⟩, _⟩, h14⟩, h15⟩ := h
  exact ⟨h6, h7, h12, h14, h15⟩

theorem identAt_spec {i : ℕ} (h : identAt i = true) {c : ℕ} (hc : c < 3) :
    lhsAt c i = Int.ofNat (D / cDen) * tN c i := by
  simp only [identAt, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  exact h c hc

/-- **The three identities** at every coordinate, from the kernel checks. -/
theorem ident_of_checks (hg : globOK = true) (hb : ∀ k < 302, blockOK k = true)
    (hh : ∀ i < 1331, headsOK 0 (Fc.getD i []) = true) (hz : ∀ k < 302, zdOK k = true)
    (hi : ∀ i < 1331, identAt i = true) :
    ∀ c < 3, ∀ i < 1331, cvec c i = (∑ e ∈ range 146, Erow e i * lam c e) +
      ∑ k ∈ range 302, ∑ u : Fin (mOf k), ∑ v : Fin (mOf k), Fmat k i u v * part c (Zmat k) u v := by
  intro c hc i hi'
  obtain ⟨hE, hL, hcd, hD0, hc0⟩ := globOK_spec hg
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD0
  have hDne : (D : ℝ) ≠ 0 := hDpos.ne'
  have hcpos : (0 : ℝ) < cDen := by exact_mod_cast hc0
  have hid := identAt_spec (hi i hi') hc
  have hrows : lsum ((Fc.getD i []).map (rowTerm c)) = ∑ k ∈ range 302, rterm c k (frow k i) := by
    have := sum_rows (rterm c) (fun k => rterm_nil c k) (hh i hi')
    rw [Finset.range_eq_Ico]
    exact this
  have hEp : (dot (Ecol.getD i []) (lamN.getD c []) : ℝ) = (D : ℝ) * ∑ e ∈ range 146, Erow e i * lam c e := by
    obtain ⟨-, hEr⟩ := shapeOK_spec hE
    obtain ⟨-, hLr⟩ := shapeOK_spec hL
    rw [dot_eq_sum _ _ 146 (hEr i hi') (hLr c hc)]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [Erow, lam]
    field_simp
  have h1 : (D : ℝ) * cvec c i = (lhsAt c i : ℝ) := by
    rw [hid, cvec, Int.ofNat_eq_natCast, Int.cast_mul, Int.cast_natCast,
      Nat.cast_div (Nat.dvd_of_mod_eq_zero hcd) hcpos.ne']
    field_simp
  have hmain : (D : ℝ) * cvec c i = (D : ℝ) * ((∑ e ∈ range 146, Erow e i * lam c e) +
      ∑ k ∈ range 302, ∑ u : Fin (mOf k), ∑ v : Fin (mOf k), Fmat k i u v * part c (Zmat k) u v) := by
    rw [h1, lhsAt, Int.cast_add, hEp, hrows, Int.cast_sum, mul_add, add_right_inj, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    exact rterm_eq (hb k (Finset.mem_range.1 hk)) (hz k (Finset.mem_range.1 hk)) hc
  exact mul_left_cancel₀ hDne hmain

end NPT.CP3.Sem
