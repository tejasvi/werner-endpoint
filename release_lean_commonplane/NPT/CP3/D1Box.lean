/-
NPT.CP3.D1Box — generic facts for the assembly of D1:
* `boxOK_of`: `BoxOK dims (boxN L)` for true dimensions `0 < dims l ≤ dpad l` read from a list `L`;
* `fOut3_bridge'`, `fOut0_bridge'`: the per-coordinate bridges with the block size given as any `m = o.m`;
* `checkRange_append`: native range checks compose;
* `tup_eq_iff`: tuples read from lists are equal iff the lists are.
-/
import NPT.CP3.D1Final

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem NPT.Cert.SymAvg NPT.CP3.Ctr NPT.CP3.Data

namespace NPT.CP3.D1

open NPT.CP3

/-- **Box facts from the dimensions.** -/
theorem boxOK_of (dims : Fin 5 → ℕ) (L : List ℕ) (hL : ∀ l : Fin 5, dims l = L.getD l.val 1)
    (hd : ∀ l : Fin 5, dims l ≤ dpad l) (hpos : ∀ l : Fin 5, 0 < dims l) : BoxOK dims (boxN L) := by
  have hb : ∀ μ : MI, inBox dims μ → (μ 0 : ℕ) < L.getD 0 1 ∧ (μ 1 : ℕ) < L.getD 1 1 ∧ (μ 2 : ℕ) < L.getD 2 1 ∧
      (μ 3 : ℕ) < L.getD 3 1 ∧ (μ 4 : ℕ) < L.getD 4 1 := by
    intro μ hμ
    exact ⟨lt_of_lt_of_eq (hμ 0) (hL 0), lt_of_lt_of_eq (hμ 1) (hL 1), lt_of_lt_of_eq (hμ 2) (hL 2),
      lt_of_lt_of_eq (hμ 3) (hL 3), lt_of_lt_of_eq (hμ 4) (hL 4)⟩
  refine ⟨fun μ hμ => ⟨?_, ?_⟩, fun t ht => ⟨fun l => unflat_lt dims hd hpos t l, ?_⟩⟩
  · obtain ⟨h0, h1, h2, h3, h4⟩ := hb μ hμ
    rw [flatTrue_eq dims L hL]
    exact flat5_lt L h0 h1 h2 h3 h4
  · obtain ⟨h0, h1, h2, h3, h4⟩ := hb μ hμ
    obtain ⟨d0, d1, d2, d3, d4⟩ := digit_flat5 L h0 h1 h2 h3 h4
    funext l
    apply Fin.ext
    rw [unflat_val dims L hL hd hpos, flatTrue_eq dims L hL]
    fin_cases l
    · exact d0
    · exact d1
    · exact d2
    · exact d3
    · exact d4
  · rw [flatTrue_eq dims L hL]
    have e : ∀ l : Fin 5, (unflat dims t l : ℕ) = digit L t l.val := unflat_val dims L hL hd hpos t
    rw [e 0, e 1, e 2, e 3, e 4]
    exact flat5_digit L ht

/-- `fOut3_bridge` with the block size given as any `mm = o.m`. -/
theorem fOut3_bridge' (R : Raw) (v : VarB) (j : ℕ) (o : OutB) {P0 P3 : PadData} (P : PhiLists) (hP : PhiH R P)
    {dims : Fin 5 → ℕ} {n : ℕ} {τ : Fin 5 → Fin 5} (hv : VarH R P v dims n τ) (Gq : Matrix (Fin n) (Fin n) ℚ)
    (hG : ∀ a b : Fin n, Gq a b = (((gArr v j).getD (a.val * n + b.val) 0 : ℤ) : ℚ))
    {dims' : Fin 5 → ℕ} {n' : ℕ} {τo : Fin 5 → Fin 5} (ho : OutH R P o dims' n' τo)
    (σ : Fin v.cosets.length → Equiv.Perm (Fin 4))
    (hσ : ∀ c (r : Fin 4), (σ c r).val = sOf (v.cosets.getD c.val default).2 r.val)
    {mm : ℕ} (hm : o.m = mm) (Vq : Matrix (Fin n') (Fin mm) ℂ)
    (hVq : ∀ p u, Vq p u = ((lg o.V p.val u.val : ℤ) : ℂ)) (u w : Fin mm) :
    ((padR dims' Vq)ᵀ * (∑ c : Fin v.cosets.length, reindexMI (σ c)
      (phiMap (F := P0.fam) (F' := P3.fam) (phiPad P) (fun l => τo (sigHat (σ c) l)) τ
        (padRC dims (Gq.map fun q => (q : ℂ))))) * padR dims' Vq) u w =
      (((fOut3 R v (t4Arr R (flatOf R.phiNum 23 23) v (t0Arr v (gArr v j))) (xInv R v) o).getD u.val []).getD
        w.val 0 : ℂ) / 192 ^ 4 := by
  subst hm
  exact fOut3_bridge R v j o P hP hv Gq hG ho σ hσ Vq hVq u w

/-- `fOut0_bridge` with the block size given as any `mm = o.m`. -/
theorem fOut0_bridge' (R : Raw) (v : VarB) (j : ℕ) (o : OutB) (P : PhiLists) {dims : Fin 5 → ℕ} {n : ℕ}
    {τ : Fin 5 → Fin 5} (hv : VarH R P v dims n τ) (Gq : Matrix (Fin n) (Fin n) ℚ)
    (hG : ∀ a b : Fin n, Gq a b = (((gArr v j).getD (a.val * n + b.val) 0 : ℤ) : ℚ))
    {dims' : Fin 5 → ℕ} {n' : ℕ} {τo : Fin 5 → Fin 5} (ho : OutH0 P o dims' n' τo)
    (σ : Fin v.cosets.length → Equiv.Perm (Fin 4))
    (hσ : ∀ c (r : Fin 4), (σ c r).val = sOf (v.cosets.getD c.val default).2 r.val)
    (new : Fin v.cosets.length → Fin 5 → Fin 5)
    (hnew : ∀ c, new c = τo ↔ ((v.cosets.getD c.val default).1 = o.st ∧ v.ai = o.ai))
    (hcos : ∀ c, (fun l => new c (sigHat (σ c) l)) = τ)
    {mm : ℕ} (hm : o.m = mm) (Vq : Matrix (Fin n') (Fin mm) ℂ)
    (hVq : ∀ p u, Vq p u = ((lg o.V p.val u.val : ℤ) : ℂ)) (u w : Fin mm) :
    ((padR dims' Vq)ᵀ * (∑ c : Fin v.cosets.length,
      if new c = τo then reindexMI (σ c) (padRC dims (Gq.map fun q => (q : ℂ))) else 0) * padR dims' Vq) u w =
      (((fOut0 v (gArr v j) o).getD u.val []).getD w.val 0 : ℂ) := by
  subst hm
  exact fOut0_bridge R v j o P hv Gq hG ho σ hσ new hnew hcos Vq hVq u w

/-- `getD` inside the list. -/
lemma getD_lt {α : Type*} (l : List α) (n : ℕ) (d : α) (h : n < l.length) : l.getD n d = l[n] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- Native range checks compose. -/
theorem checkRange_append (R : Raw) {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) (h1 : checkRange R a b = true)
    (h2 : checkRange R b c = true) : checkRange R a c = true := by
  simp only [checkRange] at h1 h2 ⊢
  have e : List.range' a (c - a) = List.range' a (b - a) ++ List.range' b (c - b) := by
    have h : List.range' a (b - a) ++ List.range' (a + 1 * (b - a)) (c - b) = List.range' a (b - a + (c - b)) :=
      List.range'_append
    rw [show a + 1 * (b - a) = b by omega, show b - a + (c - b) = c - a by omega] at h
    exact h.symm
  rw [e, List.all_append, h1, h2, Bool.and_self]

/-- A passed native range check passes at every coordinate of the range. -/
theorem checkRange_coord (R : Raw) {a b : ℕ} (h : checkRange R a b = true) {i : ℕ} (hi1 : a ≤ i) (hi2 : i < b) :
    checkCoord R (flatOf R.phiNum 23 23) R.outs.toArray i = true := by
  simp only [checkRange, List.all_eq_true, List.mem_range'_1] at h
  exact h i ⟨hi1, by omega⟩

/-- Tuples read from lists of length 4 (entries `< 5`) are equal iff the lists are. -/
lemma tup_eq_iff {s s' : List ℕ} {a a' : ℕ} (hs : s.length = 4) (hs' : s'.length = 4)
    (hb : ∀ r < 4, s.getD r 0 < 5) (hb' : ∀ r < 4, s'.getD r 0 < 5) (ha : a < 5) (ha' : a' < 5) :
    ((fun l : Fin 5 => (Fin.ofNat 5 (if l.val < 4 then s.getD l.val 0 else a) : Fin 5)) =
      fun l : Fin 5 => (Fin.ofNat 5 (if l.val < 4 then s'.getD l.val 0 else a') : Fin 5)) ↔ s = s' ∧ a = a' := by
  have hval : ∀ x : ℕ, (Fin.ofNat 5 x : Fin 5).val = x % 5 := fun x => rfl
  constructor
  · intro h
    have hv : ∀ l : Fin 5, (if l.val < 4 then s.getD l.val 0 else a) = (if l.val < 4 then s'.getD l.val 0 else a') := by
      intro l
      have e := congrArg Fin.val (congrFun h l)
      simp only [hval] at e
      by_cases hl : l.val < 4
      · rw [if_pos hl, if_pos hl] at e ⊢
        rwa [Nat.mod_eq_of_lt (hb _ hl), Nat.mod_eq_of_lt (hb' _ hl)] at e
      · rw [if_neg hl, if_neg hl] at e ⊢
        rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at e
    refine ⟨?_, ?_⟩
    · apply List.ext_getElem (by rw [hs, hs'])
      intro r h1 h2
      have e := hv ⟨r, by omega⟩
      have hr : r < 4 := by omega
      simp only [hr, if_true] at e
      rwa [getD_lt _ _ _ h1, getD_lt _ _ _ h2] at e
    · simpa using hv 4
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The variable found by `varOf` owns the coordinate. -/
lemma varOf_spec {R : Raw} {i : ℕ} {vB : VarB} {j : ℕ} (h : varOf R i = some (vB, j)) :
    vB ∈ R.vars ∧ vB.off ≤ i ∧ i < vB.off + vB.S.length ∧ j = i - vB.off := by
  unfold varOf at h
  cases hf : R.vars.find? (fun v => v.off ≤ i && i < v.off + v.S.length) with
  | none => rw [hf] at h; cases h
  | some vF =>
    rw [hf] at h
    cases h
    have hp := List.find?_some hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact ⟨List.mem_of_find?_eq_some hf, hp.1, hp.2, rfl⟩

/-- `192⁴ · (x / 192⁴) = x`. -/
lemma mul_div_192 (x : ℂ) : (192 : ℂ) ^ 4 * (x / 192 ^ 4) = x := by
  field_simp

end NPT.CP3.D1
