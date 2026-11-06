/-
NPT.CP3.D1Bridge4 — the native D1 computation against the semantics of `NPT.CP3.Fsem` (part 4): the projected block
coefficient of a cut-`(3,)` output block.

`PhiH`, `VarH`, `OutH` collect the finite facts about the list data used by the bridge (decided per variable, per
output block); `fOut3_bridge` states `Vᵀ H V = fOut3 / 192⁴` for the coset-summed lifted Gram form `H` of one
coordinate.
-/
import NPT.CP3.D1Bridge3

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem NPT.Cert.SymAvg NPT.CP3.Ctr NPT.CP3.Data

namespace NPT.CP3.D1

open NPT.CP3

/-- The lift data `P` are read from `R`. -/
structure PhiH (R : Raw) (P : PhiLists) : Prop where
  hPn : P.phiNum = R.phiNum
  hPo0 : P.off0 = R.siteOff.getD 0 []
  hPo1 : P.off1 = R.siteOff.getD 1 []
  hPaO : P.aOff = R.auxOff
  hPaD : P.aDest = R.auxDest

/-- Facts about a variable block. -/
structure VarH (R : Raw) (P : PhiLists) (v : VarB) (dims : Fin 5 → ℕ) (n : ℕ) (τ : Fin 5 → Fin 5) : Prop where
  hB : BoxOK dims n
  hL : ∀ l : Fin 5, dims l = v.dims.getD l.val 1
  hd : ∀ l : Fin 5, dims l ≤ dpad l
  hpos : ∀ l : Fin 5, 0 < dims l
  hn : n = boxN v.dims
  hτ : ∀ q : Fin 5, q.val < 4 → (τ q).val < 4 ∧ P.d0.getD (τ q).val 0 = dims q
  hτst : ∀ q : Fin 5, q.val < 4 → (τ q).val = v.st.getD q.val 0
  hτa : P.aD.getD (τ 4).val 0 = dims 4
  hτai : (τ 4).val = v.ai
  hoff : ∀ q < 4, ∀ x < sq v.dims q, off0q R v q + x < 23
  hinj : ∀ x y, x < sq v.dims 4 → y < sq v.dims 4 →
    R.auxDest.getD (R.auxOff.getD v.ai 0 + x) 0 = R.auxDest.getD (R.auxOff.getD v.ai 0 + y) 0 → x = y
  hs4 : ∀ c < v.cosets.length, ∀ r < 4, sOf (v.cosets.getD c default).2 r < 4

/-- Facts about a cut-`(3,)` output block. -/
structure OutH (R : Raw) (P : PhiLists) (o : OutB) (dims' : Fin 5 → ℕ) (n' : ℕ) (τo : Fin 5 → Fin 5) : Prop where
  hB' : BoxOK dims' n'
  hL' : ∀ l : Fin 5, dims' l = o.dims.getD l.val 1
  hn' : n' = boxN o.dims
  hτo : ∀ m : Fin 5, m.val < 4 → (τo m).val < 4 ∧ P.d1.getD (τo m).val 0 = dims' m ∧ (τo m).val = o.st.getD m.val 0
  hτoa : P.aD.getD (τo 4).val 0 = dims' 4
  hτoai : (τo 4).val = o.ai
  ht23 : ∀ m : Fin 5, m.val < 4 → ∀ a b, a < dims' m → b < dims' m → coord P.off1 P.d1 (τo m).val a b < 23
  he70 : ∀ a b, a < dims' 4 → b < dims' 4 → R.auxOff.getD o.ai 0 + a * dims' 4 + b < 70
  hpos' : ∀ l : Fin 5, 0 < dims' l

lemma inBox_unflat {dims : Fin 5 → ℕ} {n : ℕ} (h : BoxOK dims n) {p : ℕ} (hp : p < n) : inBox dims (unflat dims p) :=
  (h.2 p hp).1

lemma flatTrue_unflat {dims : Fin 5 → ℕ} {n : ℕ} (h : BoxOK dims n) {p : ℕ} (hp : p < n) :
    flatTrue dims (unflat dims p) = p := (h.2 p hp).2

/-- **The projected cut-`(3,)` block coefficient of one coordinate.** -/
theorem fOut3_bridge (R : Raw) (v : VarB) (j : ℕ) (o : OutB) {P0 P3 : PadData} (P : PhiLists) (hP : PhiH R P)
    {dims : Fin 5 → ℕ} {n : ℕ} {τ : Fin 5 → Fin 5} (hv : VarH R P v dims n τ) (Gq : Matrix (Fin n) (Fin n) ℚ)
    (hG : ∀ a b : Fin n, Gq a b = (((gArr v j).getD (a.val * n + b.val) 0 : ℤ) : ℚ))
    {dims' : Fin 5 → ℕ} {n' : ℕ} {τo : Fin 5 → Fin 5} (ho : OutH R P o dims' n' τo)
    (σ : Fin v.cosets.length → Equiv.Perm (Fin 4))
    (hσ : ∀ c (m : Fin 4), (σ c m).val = sOf (v.cosets.getD c.val default).2 m.val)
    (Vq : Matrix (Fin n') (Fin o.m) ℂ) (hVq : ∀ p u, Vq p u = ((lg o.V p.val u.val : ℤ) : ℂ)) (u w : Fin o.m) :
    ((padR dims' Vq)ᵀ * (∑ c : Fin v.cosets.length, reindexMI (σ c)
      (phiMap (F := P0.fam) (F' := P3.fam) (phiPad P) (fun l => τo (sigHat (σ c) l)) τ
        (padRC dims (Gq.map fun q => (q : ℂ))))) * padR dims' Vq) u w =
      (((fOut3 R v (t4Arr R (flatOf R.phiNum 23 23) v (t0Arr v (gArr v j))) (xInv R v) o).getD u.val []).getD
        w.val 0 : ℂ) / 192 ^ 4 := by
  rw [vtv_padR ho.hB' Vq _ u w]
  have hH : ∀ p q : Fin n', (∑ c : Fin v.cosets.length, reindexMI (σ c)
      (phiMap (F := P0.fam) (F' := P3.fam) (phiPad P) (fun l => τo (sigHat (σ c) l)) τ
        (padRC dims (Gq.map fun q => (q : ℂ))))) (unflat dims' p) (unflat dims' q) =
      (h3Entry R v (t4Arr R (flatOf R.phiNum 23 23) v (t0Arr v (gArr v j))) (xInv R v) o p.val q.val : ℂ) / 192 ^ 4 := by
    intro p q
    rw [Matrix.sum_apply]
    have e := H3_bridge R v j o P hP.hPn hP.hPo0 hP.hPo1 hP.hPaO hP.hPaD hv.hB hv.hL hv.hd hv.hpos hv.hn τ hv.hτ hv.hτst
      hv.hτa hv.hτai Gq hG hv.hoff ho.hL' τo ho.hτo ho.hτoa ho.hτoai ho.ht23 σ hσ hv.hinj ho.he70
      (unflat dims' p) (unflat dims' q) (inBox_unflat ho.hB' p.isLt) (inBox_unflat ho.hB' q.isLt)
      (P0 := P0) (P3 := P3)
    rw [flatTrue_unflat ho.hB' p.isLt, flatTrue_unflat ho.hB' q.isLt] at e
    rw [← e]
  simp only [hH, hVq]
  rw [fOut3_spec R v _ _ o hv.hs4 u.isLt w.isLt]
  split_ifs with hhit
  · push_cast
    rw [show Finset.range (boxN o.dims) = Finset.range n' by rw [ho.hn']]
    simp only [Finset.sum_range, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  · -- no auxiliary entry of the block is hit: every entry of `H` vanishes
    have L4pos : 0 < o.dims.getD 4 1 := by
      have := ho.hpos' 4
      rwa [ho.hL' 4] at this
    have hz : ∀ p q : Fin n', h3Entry R v (t4Arr R (flatOf R.phiNum 23 23) v (t0Arr v (gArr v j))) (xInv R v) o
        p.val q.val = 0 := by
      intro p q
      unfold h3Entry
      rw [if_neg]
      intro hx
      apply hhit
      simp only [auxHit, List.any_eq_true, List.mem_range, decide_eq_true_eq]
      have hp4 : digit o.dims p.val 4 < o.dims.getD 4 1 := Nat.mod_lt _ L4pos
      have hq4 : digit o.dims q.val 4 < o.dims.getD 4 1 := Nat.mod_lt _ L4pos
      exact ⟨_, lt_of_rc hp4 hq4, by rw [← Nat.add_assoc]; exact hx⟩
    simp only [hz]
    simp

end NPT.CP3.D1
