/-
NPT.CP3.D1Bridge — the native D1 computation against the semantics of `NPT.CP3.Fsem` (part 1).

* `placeVal_eq`, `flatTrue_eq`, `unflat_val`: the padded flat index of `NPT.CP3.Pad` against `flat5`/`digit`;
* `sum_MI_padRC`: a double sum over `MI` against a padded Gram form is the flat double sum (`BoxOK`);
* `prod_phiPad`: the product of the Fourier coefficients over the five factors at flat input indices `t, s`.
-/
import NPT.CP3.Radix
import NPT.CP3.PhiDef
import NPT.CP3.PadB

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem NPT.CP3.Ctr NPT.CP3.Data

namespace NPT.CP3.D1

open NPT.CP3

lemma placeVal_eq (dims : Fin 5 → ℕ) (L : List ℕ) (hL : ∀ l : Fin 5, dims l = L.getD l.val 1) :
    placeVal dims 0 = L.getD 1 1 * L.getD 2 1 * L.getD 3 1 * L.getD 4 1 ∧
      placeVal dims 1 = L.getD 2 1 * L.getD 3 1 * L.getD 4 1 ∧ placeVal dims 2 = L.getD 3 1 * L.getD 4 1 ∧
      placeVal dims 3 = L.getD 4 1 ∧ placeVal dims 4 = 1 := by
  have h1 := hL 1
  have h2 := hL 2
  have h3 := hL 3
  have h4 := hL 4
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
  · simp only [placeVal, Fin.prod_univ_five, Fin.isValue]
    simp (config := { decide := true }) only [h1, h2, h3, h4, Fin.val_zero, Fin.val_one, Fin.val_two]
    norm_num

lemma flatTrue_eq (dims : Fin 5 → ℕ) (L : List ℕ) (hL : ∀ l : Fin 5, dims l = L.getD l.val 1) (μ : MI) :
    flatTrue dims μ = flat5 L (μ 0) (μ 1) (μ 2) (μ 3) (μ 4) := by
  obtain ⟨p0, p1, p2, p3, p4⟩ := placeVal_eq dims L hL
  simp only [flatTrue, Fin.sum_univ_five, p0, p1, p2, p3, p4, flat5]
  ring

lemma unflat_val (dims : Fin 5 → ℕ) (L : List ℕ) (hL : ∀ l : Fin 5, dims l = L.getD l.val 1)
    (hd : ∀ l : Fin 5, dims l ≤ dpad l) (hpos : ∀ l : Fin 5, 0 < dims l) (t : ℕ) (l : Fin 5) :
    (unflat dims t l).val = digit L t l.val := by
  have hlt : t / placeVal dims l % dims l < dpad l := lt_of_lt_of_le (Nat.mod_lt _ (hpos l)) (hd l)
  simp only [unflat, dif_pos hlt]
  obtain ⟨p0, p1, p2, p3, p4⟩ := placeVal_eq dims L hL
  fin_cases l
  · simp only [Fin.zero_eta, Fin.isValue, p0, digit, hL 0]; rfl
  · simp only [Fin.mk_one, Fin.isValue, p1, digit, hL 1]; rfl
  · simp only [Fin.reduceFinMk, Fin.isValue, p2, digit, hL 2]; rfl
  · simp only [Fin.reduceFinMk, Fin.isValue, p3, digit, hL 3]; rfl
  · simp only [Fin.reduceFinMk, Fin.isValue, p4, digit, hL 4, Nat.div_one]; rfl

lemma flatPos_some {dims : Fin 5 → ℕ} {n : ℕ} (h : BoxOK dims n) {b : MI} {s : Fin n}
    (hb : flatPos dims (n := n) b = some s) : b = unflat dims s.val := by
  unfold flatPos at hb
  split_ifs at hb with hc
  cases hb
  exact ((h.1 b hc.1).2).symm

/-- **Padded double sums.** -/
lemma sum_MI_padRC {dims : Fin 5 → ℕ} {n : ℕ} (h : BoxOK dims n) (K : MI → MI → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    ∑ a : MI, ∑ b : MI, K a b * padRC dims X a b =
      ∑ t : Fin n, ∑ s : Fin n, K (unflat dims t) (unflat dims s) * X t s := by
  have inner : ∀ a : MI, ∑ b : MI, K a b * padRC dims X a b =
      match flatPos dims (n := n) a with
      | some t => ∑ s : Fin n, K (unflat dims t) (unflat dims s) * X t s
      | none => 0 := by
    intro a
    cases ha : flatPos dims (n := n) a with
    | none => simp [padRC, ha]
    | some t =>
      have hb : ∀ b : MI, K a b * padRC dims X a b =
          match flatPos dims (n := n) b with
          | some s => K (unflat dims t) (unflat dims s) * X t s
          | none => 0 := by
        intro b
        cases hbs : flatPos dims (n := n) b with
        | none => simp [padRC, ha, hbs]
        | some s =>
          simp only [padRC, ha, hbs]
          rw [flatPos_some h ha, flatPos_some h hbs]
      rw [Finset.sum_congr rfl fun b _ => hb b]
      exact sum_MI_flat h _
  rw [Finset.sum_congr rfl fun a _ => inner a]
  exact sum_MI_flat h _

/-- Entry of the integer Fourier rows. -/
def phiE (P : PhiLists) (t' c : ℕ) : Int := (P.phiNum.getD t' []).getD c 0

/-- The site factor of the lift at one site: output coordinate `t'`, input coordinate `c`. -/
noncomputable def phiQ (P : PhiLists) (ρ τ : Fin 5 → Fin 5) (α β a b : MI) (q : Fin 5) : ℂ :=
  (phiE P (coord P.off1 P.d1 (ρ q).val (α q).val (β q).val) (coord P.off0 P.d0 (τ q).val (a q).val (b q).val) : ℂ) /
    192

/-- **The Fourier coefficients over the five factors**, at true output and input coordinates. -/
theorem prod_phiPad (P : PhiLists) (ρ τ : Fin 5 → Fin 5) (α β a b : MI)
    (ho : ∀ q : Fin 5, q.val < 4 → siteTrue P.d1 (ρ q).val (α q).val (β q).val)
    (hoa : auxTrue P.aD (ρ 4).val (α 4).val (β 4).val)
    (hi : ∀ q : Fin 5, q.val < 4 → siteTrue P.d0 (τ q).val (a q).val (b q).val) :
    ∏ l, phiPad P l (ρ l) (α l) (β l) (τ l) (a l) (b l) =
      phiQ P ρ τ α β a b 0 * phiQ P ρ τ α β a b 1 * phiQ P ρ τ α β a b 2 * phiQ P ρ τ α β a b 3 *
        (if auxTrue P.aD (τ 4).val (a 4).val (b 4).val ∧
            P.aDest.getD (coord P.aOff P.aD (τ 4).val (a 4).val (b 4).val) 0 =
              coord P.aOff P.aD (ρ 4).val (α 4).val (β 4).val then 1 else 0) := by
  rw [Fin.prod_univ_five]
  rw [phiPad_site P (by decide) _ _ _ _ _ _ (ho 0 (by decide)) (hi 0 (by decide)),
    phiPad_site P (by decide) _ _ _ _ _ _ (ho 1 (by decide)) (hi 1 (by decide)),
    phiPad_site P (by decide) _ _ _ _ _ _ (ho 2 (by decide)) (hi 2 (by decide)),
    phiPad_site P (by decide) _ _ _ _ _ _ (ho 3 (by decide)) (hi 3 (by decide)),
    phiPad_aux P (by decide) _ _ _ _ _ _ hoa]
  rfl

lemma unflat_lt (dims : Fin 5 → ℕ) (hd : ∀ l : Fin 5, dims l ≤ dpad l) (hpos : ∀ l : Fin 5, 0 < dims l) (t : ℕ)
    (l : Fin 5) : (unflat dims t l).val < dims l := by
  have hlt : t / placeVal dims l % dims l < dpad l := lt_of_lt_of_le (Nat.mod_lt _ (hpos l)) (hd l)
  simp only [unflat, dif_pos hlt]
  exact Nat.mod_lt _ (hpos l)

/-- **The lift at a true output entry as a flat double sum.** -/
theorem phiMap_flat (P : PhiLists) {P0 P3 : PadData} {dims : Fin 5 → ℕ} {n : ℕ} (hB : BoxOK dims n)
    (hd : ∀ l : Fin 5, dims l ≤ dpad l) (hpos : ∀ l : Fin 5, 0 < dims l) (ρ τ : Fin 5 → Fin 5) (α β : MI)
    (X : Matrix (Fin n) (Fin n) ℂ) (ho : ∀ q : Fin 5, q.val < 4 → siteTrue P.d1 (ρ q).val (α q).val (β q).val)
    (hoa : auxTrue P.aD (ρ 4).val (α 4).val (β 4).val)
    (hτ : ∀ q : Fin 5, q.val < 4 → (τ q).val < 4 ∧ P.d0.getD (τ q).val 0 = dims q) :
    phiMap (F := P0.fam) (F' := P3.fam) (phiPad P) ρ τ (padRC dims X) α β =
      ∑ t : Fin n, ∑ s : Fin n, phiQ P ρ τ α β (unflat dims t) (unflat dims s) 0 *
        phiQ P ρ τ α β (unflat dims t) (unflat dims s) 1 * phiQ P ρ τ α β (unflat dims t) (unflat dims s) 2 *
        phiQ P ρ τ α β (unflat dims t) (unflat dims s) 3 *
        (if auxTrue P.aD (τ 4).val (unflat dims t 4).val (unflat dims s 4).val ∧
            P.aDest.getD (coord P.aOff P.aD (τ 4).val (unflat dims t 4).val (unflat dims s 4).val) 0 =
              coord P.aOff P.aD (ρ 4).val (α 4).val (β 4).val then 1 else 0) * X t s := by
  unfold phiMap
  rw [sum_MI_padRC hB (fun a b => ∏ l, phiPad P l (ρ l) (α l) (β l) (τ l) (a l) (b l)) X]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
  have hi : ∀ q : Fin 5, q.val < 4 → siteTrue P.d0 (τ q).val (unflat dims t q).val (unflat dims s q).val := by
    intro q hq
    obtain ⟨h1, h2⟩ := hτ q hq
    refine ⟨h1, ?_, ?_⟩
    · rw [h2]; exact unflat_lt dims hd hpos t q
    · rw [h2]; exact unflat_lt dims hd hpos s q
  rw [prod_phiPad P ρ τ α β _ _ ho hoa hi]

/-- Site offset of the cut-`()` label of site `q` of `v`. -/
def off0q (R : Raw) (v : VarB) (q : ℕ) : ℕ := (R.siteOff.getD 0 []).getD (v.st.getD q 0) 0

/-- **The native lifted entry** as a nested sum of products of Fourier rows (complex form). -/
theorem t4_entry_cast (R : Raw) (v : VarB) (T0 : Array Int) {t0 t1 t2 t3 x4 : ℕ} (h0 : t0 < 23) (h1 : t1 < 23)
    (h2 : t2 < 23) (h3 : t3 < 23) (h4 : x4 < sq v.dims 4)
    (hoff : ∀ q < 4, ∀ x < sq v.dims q, off0q R v q + x < 23) :
    ((t4Arr R (flatOf R.phiNum 23 23) v T0).getD ((((t0 * 23 + t1) * 23 + t2) * 23 + t3) * sq v.dims 4 + x4) 0 : ℂ) =
      ∑ x3 ∈ Finset.range (sq v.dims 3), ∑ x2 ∈ Finset.range (sq v.dims 2), ∑ x1 ∈ Finset.range (sq v.dims 1),
        ∑ x0 ∈ Finset.range (sq v.dims 0),
          (lg R.phiNum t0 (off0q R v 0 + x0) : ℂ) * (lg R.phiNum t1 (off0q R v 1 + x1) : ℂ) *
            (lg R.phiNum t2 (off0q R v 2 + x2) : ℂ) * (lg R.phiNum t3 (off0q R v 3 + x3) : ℂ) *
            (T0.getD ((((x0 * sq v.dims 1 + x1) * sq v.dims 2 + x2) * sq v.dims 3 + x3) * sq v.dims 4 + x4) 0 : ℂ) := by
  rw [t4Arr_spec R _ v T0 h0 h1 h2 h3 h4]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x3 hx3 => Finset.sum_congr rfl fun x2 hx2 => Finset.sum_congr rfl fun x1 hx1 =>
    Finset.sum_congr rfl fun x0 hx0 => ?_
  have e : ∀ (t : ℕ), t < 23 → ∀ q < 4, ∀ x < sq v.dims q,
      (flatOf R.phiNum 23 23).getD (t * 23 + (R.siteOff.getD 0 []).getD (v.st.getD q 0) 0 + x) 0 =
        lg R.phiNum t (off0q R v q + x) := by
    intro t ht q hq x hx
    rw [Nat.add_assoc]
    exact flatOf_spec _ _ _ ht (hoff q hq x hx)
  rw [e t3 h3 3 (by norm_num) x3 (Finset.mem_range.1 hx3), e t2 h2 2 (by norm_num) x2 (Finset.mem_range.1 hx2),
    e t1 h1 1 (by norm_num) x1 (Finset.mem_range.1 hx1), e t0 h0 0 (by norm_num) x0 (Finset.mem_range.1 hx0)]
  ring

/-- A flat matrix extended by `0` to all of `ℕ × ℕ`. -/
noncomputable def ext0 {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) (t s : ℕ) : ℂ :=
  if h : t < n ∧ s < n then X ⟨t, h.1⟩ ⟨s, h.2⟩ else 0

/-- **The lift at a true output entry in the per-factor pair form of the native computation.** The auxiliary
output coordinate has the preimage `x4` (`hdest`). -/
theorem phiMap_x (P : PhiLists) {P0 P3 : PadData} {dims : Fin 5 → ℕ} {n : ℕ} (hB : BoxOK dims n) (L : List ℕ)
    (hL : ∀ l : Fin 5, dims l = L.getD l.val 1) (hd : ∀ l : Fin 5, dims l ≤ dpad l) (hpos : ∀ l : Fin 5, 0 < dims l)
    (ρ τ : Fin 5 → Fin 5) (α β : MI) (X : Matrix (Fin n) (Fin n) ℂ)
    (ho : ∀ q : Fin 5, q.val < 4 → siteTrue P.d1 (ρ q).val (α q).val (β q).val)
    (hoa : auxTrue P.aD (ρ 4).val (α 4).val (β 4).val)
    (hτ : ∀ q : Fin 5, q.val < 4 → (τ q).val < 4 ∧ P.d0.getD (τ q).val 0 = dims q)
    (hτa : P.aD.getD (τ 4).val 0 = dims 4) (hn : n = boxN L) {x4 : ℕ} (hx4 : x4 < dims 4 * dims 4)
    (hdest : ∀ x < dims 4 * dims 4, P.aDest.getD (P.aOff.getD (τ 4).val 0 + x) 0 =
      coord P.aOff P.aD (ρ 4).val (α 4).val (β 4).val ↔ x = x4) :
    phiMap (F := P0.fam) (F' := P3.fam) (phiPad P) ρ τ (padRC dims X) α β =
      ∑ x3 ∈ Finset.range (dims 3 * dims 3), ∑ x2 ∈ Finset.range (dims 2 * dims 2),
        ∑ x1 ∈ Finset.range (dims 1 * dims 1), ∑ x0 ∈ Finset.range (dims 0 * dims 0),
          (phiE P (coord P.off1 P.d1 (ρ 0).val (α 0).val (β 0).val) ((P.off0.getD (τ 0).val 0) + x0) : ℂ) / 192 *
          ((phiE P (coord P.off1 P.d1 (ρ 1).val (α 1).val (β 1).val) ((P.off0.getD (τ 1).val 0) + x1) : ℂ) / 192) *
          ((phiE P (coord P.off1 P.d1 (ρ 2).val (α 2).val (β 2).val) ((P.off0.getD (τ 2).val 0) + x2) : ℂ) / 192) *
          ((phiE P (coord P.off1 P.d1 (ρ 3).val (α 3).val (β 3).val) ((P.off0.getD (τ 3).val 0) + x3) : ℂ) / 192) *
          ext0 X (flat5 L (x0 / dims 0) (x1 / dims 1) (x2 / dims 2) (x3 / dims 3) (x4 / dims 4))
            (flat5 L (x0 % dims 0) (x1 % dims 1) (x2 % dims 2) (x3 % dims 3) (x4 % dims 4)) := by
  rw [phiMap_flat P hB hd hpos ρ τ α β X ho hoa hτ]
  have hLq : ∀ q : Fin 5, L.getD q.val 1 = dims q := fun q => (hL q).symm
  have hL0 : L.getD 0 1 = dims 0 := hLq 0
  have hL1 : L.getD 1 1 = dims 1 := hLq 1
  have hL2 : L.getD 2 1 = dims 2 := hLq 2
  have hL3 : L.getD 3 1 = dims 3 := hLq 3
  have hL4 : L.getD 4 1 = dims 4 := hLq 4
  have hLpos : ∀ i < 5, 0 < L.getD i 1 := by
    intro i hi
    have := hpos ⟨i, hi⟩
    rwa [hL ⟨i, hi⟩] at this
  -- the summand as a function of the flat indices
  set K : ℕ → ℕ → ℂ := fun t s =>
    if digit L t 4 * dims 4 + digit L s 4 = x4 then
      (phiE P (coord P.off1 P.d1 (ρ 0).val (α 0).val (β 0).val)
          (coord P.off0 P.d0 (τ 0).val (digit L t 0) (digit L s 0)) : ℂ) / 192 *
        ((phiE P (coord P.off1 P.d1 (ρ 1).val (α 1).val (β 1).val)
          (coord P.off0 P.d0 (τ 1).val (digit L t 1) (digit L s 1)) : ℂ) / 192) *
        ((phiE P (coord P.off1 P.d1 (ρ 2).val (α 2).val (β 2).val)
          (coord P.off0 P.d0 (τ 2).val (digit L t 2) (digit L s 2)) : ℂ) / 192) *
        ((phiE P (coord P.off1 P.d1 (ρ 3).val (α 3).val (β 3).val)
          (coord P.off0 P.d0 (τ 3).val (digit L t 3) (digit L s 3)) : ℂ) / 192) * ext0 X t s
    else 0 with hK
  have key : ∀ t s : Fin n, phiQ P ρ τ α β (unflat dims t) (unflat dims s) 0 *
      phiQ P ρ τ α β (unflat dims t) (unflat dims s) 1 * phiQ P ρ τ α β (unflat dims t) (unflat dims s) 2 *
      phiQ P ρ τ α β (unflat dims t) (unflat dims s) 3 *
      (if auxTrue P.aD (τ 4).val (unflat dims t 4).val (unflat dims s 4).val ∧
          P.aDest.getD (coord P.aOff P.aD (τ 4).val (unflat dims t 4).val (unflat dims s 4).val) 0 =
            coord P.aOff P.aD (ρ 4).val (α 4).val (β 4).val then 1 else 0) * X t s = K t.val s.val := by
    intro t s
    have u0 : ∀ r, (unflat dims r 0).val = digit L r 0 := fun r => unflat_val dims L hL hd hpos r 0
    have u1 : ∀ r, (unflat dims r 1).val = digit L r 1 := fun r => unflat_val dims L hL hd hpos r 1
    have u2 : ∀ r, (unflat dims r 2).val = digit L r 2 := fun r => unflat_val dims L hL hd hpos r 2
    have u3 : ∀ r, (unflat dims r 3).val = digit L r 3 := fun r => unflat_val dims L hL hd hpos r 3
    have u4 : ∀ r, (unflat dims r 4).val = digit L r 4 := fun r => unflat_val dims L hL hd hpos r 4
    have dt4 : digit L t.val 4 < dims 4 := by rw [← u4 t]; exact unflat_lt dims hd hpos t 4
    have ds4 : digit L s.val 4 < dims 4 := by rw [← u4 s]; exact unflat_lt dims hd hpos s 4
    have hcond : (auxTrue P.aD (τ 4).val (unflat dims t 4).val (unflat dims s 4).val ∧
        P.aDest.getD (coord P.aOff P.aD (τ 4).val (unflat dims t 4).val (unflat dims s 4).val) 0 =
          coord P.aOff P.aD (ρ 4).val (α 4).val (β 4).val) ↔ digit L t.val 4 * dims 4 + digit L s.val 4 = x4 := by
      rw [u4 t, u4 s]
      simp only [auxTrue, coord, hτa]
      rw [Nat.add_assoc]
      constructor
      · rintro ⟨-, h⟩
        exact (hdest _ (lt_of_rc dt4 ds4)).1 h
      · intro h
        exact ⟨⟨dt4, ds4⟩, (hdest _ (lt_of_rc dt4 ds4)).2 h⟩
    have hX : X t s = ext0 X t.val s.val := by simp [ext0, t.isLt, s.isLt]
    simp only [hK, phiQ, u0, u1, u2, u3]
    by_cases hc : digit L t.val 4 * dims 4 + digit L s.val 4 = x4
    · rw [if_pos (hcond.2 hc), if_pos hc, hX]
      ring
    · rw [if_neg (fun h => hc (hcond.1 h)), if_neg hc]
      ring
  rw [Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => key t s]
  rw [← Finset.sum_range (fun t => ∑ s : Fin n, K t s.val)]
  rw [Finset.sum_congr rfl fun t _ => (Finset.sum_range (fun s => K t s)).symm]
  rw [show Finset.range n = Finset.range (boxN L) by rw [hn]]
  set F : ℕ → ℕ → ℂ := fun t s =>
    (phiE P (coord P.off1 P.d1 (ρ 0).val (α 0).val (β 0).val)
        (coord P.off0 P.d0 (τ 0).val (digit L t 0) (digit L s 0)) : ℂ) / 192 *
      ((phiE P (coord P.off1 P.d1 (ρ 1).val (α 1).val (β 1).val)
        (coord P.off0 P.d0 (τ 1).val (digit L t 1) (digit L s 1)) : ℂ) / 192) *
      ((phiE P (coord P.off1 P.d1 (ρ 2).val (α 2).val (β 2).val)
        (coord P.off0 P.d0 (τ 2).val (digit L t 2) (digit L s 2)) : ℂ) / 192) *
      ((phiE P (coord P.off1 P.d1 (ρ 3).val (α 3).val (β 3).val)
        (coord P.off0 P.d0 (τ 3).val (digit L t 3) (digit L s 3)) : ℂ) / 192) * ext0 X t s with hF
  have hKF : ∀ t s, K t s = if digit L t 4 * L.getD 4 1 + digit L s 4 = x4 then F t s else 0 := by
    intro t s
    rw [hK, hF, hL4]
  rw [Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => hKF t s]
  rw [sum_pairs L hLpos (by rw [hL4]; exact hx4)]
  simp only [hF]
  simp only [hL0, hL1, hL2, hL3, hL4]
  refine Finset.sum_congr rfl fun x3 hx3 => Finset.sum_congr rfl fun x2 hx2 => Finset.sum_congr rfl fun x1 hx1 =>
    Finset.sum_congr rfl fun x0 hx0 => ?_
  have m3 := Finset.mem_range.1 hx3
  have m2 := Finset.mem_range.1 hx2
  have m1 := Finset.mem_range.1 hx1
  have m0 := Finset.mem_range.1 hx0
  have q0 : x0 / dims 0 < L.getD 0 1 := by rw [hL0]; exact Nat.div_lt_of_lt_mul m0
  have q1 : x1 / dims 1 < L.getD 1 1 := by rw [hL1]; exact Nat.div_lt_of_lt_mul m1
  have q2 : x2 / dims 2 < L.getD 2 1 := by rw [hL2]; exact Nat.div_lt_of_lt_mul m2
  have q3 : x3 / dims 3 < L.getD 3 1 := by rw [hL3]; exact Nat.div_lt_of_lt_mul m3
  have q4 : x4 / dims 4 < L.getD 4 1 := by rw [hL4]; exact Nat.div_lt_of_lt_mul hx4
  have r0 : x0 % dims 0 < L.getD 0 1 := by rw [hL0]; exact Nat.mod_lt _ (hpos 0)
  have r1 : x1 % dims 1 < L.getD 1 1 := by rw [hL1]; exact Nat.mod_lt _ (hpos 1)
  have r2 : x2 % dims 2 < L.getD 2 1 := by rw [hL2]; exact Nat.mod_lt _ (hpos 2)
  have r3 : x3 % dims 3 < L.getD 3 1 := by rw [hL3]; exact Nat.mod_lt _ (hpos 3)
  have r4 : x4 % dims 4 < L.getD 4 1 := by rw [hL4]; exact Nat.mod_lt _ (hpos 4)
  obtain ⟨a0, a1, a2, a3, -⟩ := digit_flat5 L q0 q1 q2 q3 q4
  obtain ⟨b0, b1, b2, b3, -⟩ := digit_flat5 L r0 r1 r2 r3 r4
  rw [a0, a1, a2, a3, b0, b1, b2, b3]
  have cq : ∀ q : Fin 5, q.val < 4 → ∀ x : ℕ,
      coord P.off0 P.d0 (τ q).val (x / dims q) (x % dims q) = P.off0.getD (τ q).val 0 + x := by
    intro q hq x
    simp only [coord, (hτ q hq).2, Nat.add_assoc, Nat.div_add_mod']
  rw [cq 0 (by decide), cq 1 (by decide), cq 2 (by decide), cq 3 (by decide)]

/-- **The lift of one coordinate equals the native lifted entry, divided by `192⁴`.** -/
theorem lift_eq (R : Raw) (v : VarB) (j : ℕ) {P0 P3 : PadData} (P : PhiLists) (hPn : P.phiNum = R.phiNum)
    (hPo : P.off0 = R.siteOff.getD 0 []) {dims : Fin 5 → ℕ} {n : ℕ} (hB : BoxOK dims n)
    (hL : ∀ l : Fin 5, dims l = v.dims.getD l.val 1) (hd : ∀ l : Fin 5, dims l ≤ dpad l)
    (hpos : ∀ l : Fin 5, 0 < dims l) (hn : n = boxN v.dims) (ρ τ : Fin 5 → Fin 5) (α β : MI)
    (Gq : Matrix (Fin n) (Fin n) ℚ) (hG : ∀ a b : Fin n, Gq a b = (((gArr v j).getD (a.val * n + b.val) 0 : ℤ) : ℚ))
    (ho : ∀ q : Fin 5, q.val < 4 → siteTrue P.d1 (ρ q).val (α q).val (β q).val)
    (hoa : auxTrue P.aD (ρ 4).val (α 4).val (β 4).val)
    (hτ : ∀ q : Fin 5, q.val < 4 → (τ q).val < 4 ∧ P.d0.getD (τ q).val 0 = dims q)
    (hτst : ∀ q : Fin 5, q.val < 4 → (τ q).val = v.st.getD q.val 0)
    (hτa : P.aD.getD (τ 4).val 0 = dims 4) {x4 : ℕ} (hx4 : x4 < dims 4 * dims 4)
    (hdest : ∀ x < dims 4 * dims 4, P.aDest.getD (P.aOff.getD (τ 4).val 0 + x) 0 =
      coord P.aOff P.aD (ρ 4).val (α 4).val (β 4).val ↔ x = x4)
    (hoff : ∀ q < 4, ∀ x < sq v.dims q, off0q R v q + x < 23)
    (ht' : ∀ q : Fin 5, q.val < 4 → coord P.off1 P.d1 (ρ q).val (α q).val (β q).val < 23) :
    phiMap (F := P0.fam) (F' := P3.fam) (phiPad P) ρ τ (padRC dims (Gq.map fun q => (q : ℂ))) α β =
      ((t4Arr R (flatOf R.phiNum 23 23) v (t0Arr v (gArr v j))).getD
        ((((coord P.off1 P.d1 (ρ 0).val (α 0).val (β 0).val * 23 + coord P.off1 P.d1 (ρ 1).val (α 1).val (β 1).val) * 23 +
          coord P.off1 P.d1 (ρ 2).val (α 2).val (β 2).val) * 23 + coord P.off1 P.d1 (ρ 3).val (α 3).val (β 3).val) *
          sq v.dims 4 + x4) 0 : ℂ) / 192 ^ 4 := by
  have hsq : ∀ q : Fin 5, sq v.dims q.val = dims q * dims q := by intro q; simp only [sq, hL q]
  have hs0 : sq v.dims 0 = dims 0 * dims 0 := hsq 0
  have hs1 : sq v.dims 1 = dims 1 * dims 1 := hsq 1
  have hs2 : sq v.dims 2 = dims 2 * dims 2 := hsq 2
  have hs3 : sq v.dims 3 = dims 3 * dims 3 := hsq 3
  have hs4 : sq v.dims 4 = dims 4 * dims 4 := hsq 4
  rw [phiMap_x P hB v.dims hL hd hpos ρ τ α β _ ho hoa hτ hτa hn hx4 hdest]
  rw [t4_entry_cast R v _ (ht' 0 (by decide)) (ht' 1 (by decide)) (ht' 2 (by decide)) (ht' 3 (by decide))
    (by rw [hs4]; exact hx4) hoff]
  rw [hs0, hs1, hs2, hs3, hs4]
  simp only [Finset.sum_div]
  refine Finset.sum_congr rfl fun x3 hx3 => Finset.sum_congr rfl fun x2 hx2 => Finset.sum_congr rfl fun x1 hx1 =>
    Finset.sum_congr rfl fun x0 hx0 => ?_
  have m0 : x0 < sq v.dims 0 := by rw [hs0]; exact Finset.mem_range.1 hx0
  have m1 : x1 < sq v.dims 1 := by rw [hs1]; exact Finset.mem_range.1 hx1
  have m2 : x2 < sq v.dims 2 := by rw [hs2]; exact Finset.mem_range.1 hx2
  have m3 : x3 < sq v.dims 3 := by rw [hs3]; exact Finset.mem_range.1 hx3
  have m4 : x4 < sq v.dims 4 := by rw [hs4]; exact hx4
  have ht0 := t0Arr_spec v (gArr v j) m0 m1 m2 m3 m4
  rw [hs1, hs2, hs3, hs4] at ht0
  rw [ht0]
  have hd0 : dims 0 = v.dims.getD 0 1 := hL 0
  have hd1 : dims 1 = v.dims.getD 1 1 := hL 1
  have hd2 : dims 2 = v.dims.getD 2 1 := hL 2
  have hd3 : dims 3 = v.dims.getD 3 1 := hL 3
  have hd4 : dims 4 = v.dims.getD 4 1 := hL 4
  have hp : ∀ i < 5, 0 < v.dims.getD i 1 := by
    intro i hi; have := hpos ⟨i, hi⟩; rwa [hL ⟨i, hi⟩] at this
  have hfa : flat5 v.dims (x0 / dims 0) (x1 / dims 1) (x2 / dims 2) (x3 / dims 3) (x4 / dims 4) < n := by
    rw [hn, hd0, hd1, hd2, hd3, hd4]
    exact flat5_lt _ (Nat.div_lt_of_lt_mul m0) (Nat.div_lt_of_lt_mul m1) (Nat.div_lt_of_lt_mul m2)
      (Nat.div_lt_of_lt_mul m3) (Nat.div_lt_of_lt_mul m4)
  have hfb : flat5 v.dims (x0 % dims 0) (x1 % dims 1) (x2 % dims 2) (x3 % dims 3) (x4 % dims 4) < n := by
    rw [hn]
    exact flat5_lt _ (by rw [← hd0]; exact Nat.mod_lt _ (hpos 0)) (by rw [← hd1]; exact Nat.mod_lt _ (hpos 1))
      (by rw [← hd2]; exact Nat.mod_lt _ (hpos 2)) (by rw [← hd3]; exact Nat.mod_lt _ (hpos 3))
      (by rw [← hd4]; exact Nat.mod_lt _ (hpos 4))
  have hext : ext0 (Gq.map fun q => (q : ℂ))
      (flat5 v.dims (x0 / dims 0) (x1 / dims 1) (x2 / dims 2) (x3 / dims 3) (x4 / dims 4))
      (flat5 v.dims (x0 % dims 0) (x1 % dims 1) (x2 % dims 2) (x3 % dims 3) (x4 % dims 4)) =
      (((gArr v j).getD (flat5 v.dims (x0 / dims 0) (x1 / dims 1) (x2 / dims 2) (x3 / dims 3) (x4 / dims 4) * n +
        flat5 v.dims (x0 % dims 0) (x1 % dims 1) (x2 % dims 2) (x3 % dims 3) (x4 % dims 4)) 0 : ℤ) : ℂ) := by
    simp only [ext0, dif_pos (And.intro hfa hfb), Matrix.map_apply, hG]
    push_cast
    rfl
  rw [hext, ← hn, ← hd0, ← hd1, ← hd2, ← hd3, ← hd4]
  have hph : ∀ q : Fin 5, q.val < 4 → ∀ (t' x : ℕ), phiE P t' (P.off0.getD (τ q).val 0 + x) =
      lg R.phiNum t' (off0q R v q.val + x) := by
    intro q hq t' x
    simp only [phiE, lg, off0q, hPn, hPo, hτst q hq]
  have hph0 : ∀ t' x, phiE P t' (P.off0.getD (τ 0).val 0 + x) = lg R.phiNum t' (off0q R v 0 + x) :=
    hph 0 (by decide)
  have hph1 : ∀ t' x, phiE P t' (P.off0.getD (τ 1).val 0 + x) = lg R.phiNum t' (off0q R v 1 + x) :=
    hph 1 (by decide)
  have hph2 : ∀ t' x, phiE P t' (P.off0.getD (τ 2).val 0 + x) = lg R.phiNum t' (off0q R v 2 + x) :=
    hph 2 (by decide)
  have hph3 : ∀ t' x, phiE P t' (P.off0.getD (τ 3).val 0 + x) = lg R.phiNum t' (off0q R v 3 + x) :=
    hph 3 (by decide)
  rw [hph0, hph1, hph2, hph3]
  ring

end NPT.CP3.D1
