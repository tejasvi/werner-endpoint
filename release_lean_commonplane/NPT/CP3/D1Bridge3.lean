/-
NPT.CP3.D1Bridge3 — the native D1 computation against the semantics of `NPT.CP3.Fsem` (part 3): the coset sum of the
lifted Gram form of one coordinate, at a true output entry, is the native `h3Entry` divided by `192⁴`.
-/
import NPT.CP3.D1Bridge2

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem NPT.Cert.SymAvg NPT.CP3.Ctr NPT.CP3.Data

namespace NPT.CP3.D1

open NPT.CP3

lemma sigHat_val_lt (σ : Equiv.Perm (Fin 4)) {q : Fin 5} (hq : q.val < 4) : (sigHat σ q).val = (σ ⟨q.val, hq⟩).val := by
  simp [sigHat, hq]

lemma sigHat_four (σ : Equiv.Perm (Fin 4)) : sigHat σ 4 = 4 := by
  simp [sigHat]

lemma permMI_val (σ : Equiv.Perm (Fin 4)) (μ : MI) (q : Fin 5) : ((permMI σ μ) q).val = (μ (sigHat σ q)).val := by
  simp [permMI]

set_option maxHeartbeats 1600000 in
/-- **Coset sum at a true output entry.** -/
theorem H3_bridge (R : Raw) (v : VarB) (j : ℕ) (o : OutB) {P0 P3 : PadData} (P : PhiLists)
    (hPn : P.phiNum = R.phiNum) (hPo0 : P.off0 = R.siteOff.getD 0 []) (hPo1 : P.off1 = R.siteOff.getD 1 [])
    (hPaO : P.aOff = R.auxOff) (hPaD : P.aDest = R.auxDest)
    {dims : Fin 5 → ℕ} {n : ℕ} (hB : BoxOK dims n) (hL : ∀ l : Fin 5, dims l = v.dims.getD l.val 1)
    (hd : ∀ l : Fin 5, dims l ≤ dpad l) (hpos : ∀ l : Fin 5, 0 < dims l) (hn : n = boxN v.dims)
    (τ : Fin 5 → Fin 5) (hτ : ∀ q : Fin 5, q.val < 4 → (τ q).val < 4 ∧ P.d0.getD (τ q).val 0 = dims q)
    (hτst : ∀ q : Fin 5, q.val < 4 → (τ q).val = v.st.getD q.val 0) (hτa : P.aD.getD (τ 4).val 0 = dims 4)
    (hτai : (τ 4).val = v.ai) (Gq : Matrix (Fin n) (Fin n) ℚ)
    (hG : ∀ a b : Fin n, Gq a b = (((gArr v j).getD (a.val * n + b.val) 0 : ℤ) : ℚ))
    (hoff : ∀ q < 4, ∀ x < sq v.dims q, off0q R v q + x < 23)
    {dims' : Fin 5 → ℕ} (hL' : ∀ l : Fin 5, dims' l = o.dims.getD l.val 1) (τo : Fin 5 → Fin 5)
    (hτo : ∀ m : Fin 5, m.val < 4 → (τo m).val < 4 ∧ P.d1.getD (τo m).val 0 = dims' m ∧
      (τo m).val = o.st.getD m.val 0)
    (hτoa : P.aD.getD (τo 4).val 0 = dims' 4) (hτoai : (τo 4).val = o.ai)
    (ht23 : ∀ m : Fin 5, m.val < 4 → ∀ a b, a < dims' m → b < dims' m → coord P.off1 P.d1 (τo m).val a b < 23)
    (σ : Fin v.cosets.length → Equiv.Perm (Fin 4))
    (hσ : ∀ c (m : Fin 4), (σ c m).val = sOf (v.cosets.getD c.val default).2 m.val)
    (hinj : ∀ x y, x < sq v.dims 4 → y < sq v.dims 4 →
      R.auxDest.getD (R.auxOff.getD v.ai 0 + x) 0 = R.auxDest.getD (R.auxOff.getD v.ai 0 + y) 0 → x = y)
    (he70 : ∀ a b, a < dims' 4 → b < dims' 4 → R.auxOff.getD o.ai 0 + a * dims' 4 + b < 70)
    (μ ν : MI) (hμ : inBox dims' μ) (hν : inBox dims' ν) :
    (∑ c : Fin v.cosets.length, reindexMI (σ c)
      (phiMap (F := P0.fam) (F' := P3.fam) (phiPad P) (fun l => τo (sigHat (σ c) l)) τ
        (padRC dims (Gq.map fun q => (q : ℂ)))) μ ν) =
      (h3Entry R v (t4Arr R (flatOf R.phiNum 23 23) v (t0Arr v (gArr v j))) (xInv R v) o
        (flatTrue dims' μ) (flatTrue dims' ν) : ℂ) / 192 ^ 4 := by
  set p := flatTrue dims' μ with hp
  set q' := flatTrue dims' ν with hq'
  have dμ : ∀ l : Fin 5, digit o.dims p l.val = (μ l).val := digit_flatTrue dims' o.dims hL' μ hμ
  have dν : ∀ l : Fin 5, digit o.dims q' l.val = (ν l).val := digit_flatTrue dims' o.dims hL' ν hν
  have dμ4 : digit o.dims p 4 = (μ 4).val := dμ 4
  have dν4 : digit o.dims q' 4 = (ν 4).val := dν 4
  have hL'4 : dims' 4 = o.dims.getD 4 1 := hL' 4
  have hsq4 : sq v.dims 4 = dims 4 * dims 4 := by simp only [sq, hL 4]; rfl
  -- the auxiliary output coordinate
  set e := R.auxOff.getD o.ai 0 + digit o.dims p 4 * o.dims.getD 4 1 + digit o.dims q' 4 with he
  have heq : e = coord P.aOff P.aD (τo 4).val (μ 4).val (ν 4).val := by
    simp only [coord]
    rw [hτoa, hPaO, hτoai, he, dμ4, dν4, hL'4]
  have he70' : e < 70 := by
    rw [he, dμ4, dν4, ← hL'4]
    exact he70 _ _ (hμ 4) (hν 4)
  unfold h3Entry
  rw [← he]
  -- coordinates of the lifted entry for coset `c`
  have hco : ∀ (c : Fin v.cosets.length) (r : Fin 5) (hr : r.val < 4),
      coord P.off1 P.d1 ((fun l => τo (sigHat (σ c) l)) r).val ((permMI (σ c) μ) r).val ((permMI (σ c) ν) r).val =
        sCoord R o p q' (sOf (v.cosets.getD c.val default).2 r.val) := by
    intro c r hr
    have hs : (sigHat (σ c) r).val = sOf (v.cosets.getD c.val default).2 r.val := by
      rw [sigHat_val_lt _ hr, hσ]
    have hm : (sigHat (σ c) r).val < 4 := by rw [sigHat_val_lt _ hr]; exact (σ c _).isLt
    obtain ⟨-, h2, h3⟩ := hτo (sigHat (σ c) r) hm
    simp only [coord, sCoord, permMI_val]
    rw [h2, hL', h3, hPo1, ← hs, dμ, dν]
  -- per coset: the output coordinates are true, and the auxiliary output coordinate is `e`
  have hho : ∀ (c : Fin v.cosets.length) (r : Fin 5), r.val < 4 →
      siteTrue P.d1 ((fun l => τo (sigHat (σ c) l)) r).val ((permMI (σ c) μ) r).val ((permMI (σ c) ν) r).val := by
    intro c r hr
    have hm : (sigHat (σ c) r).val < 4 := by rw [sigHat_val_lt _ hr]; exact (σ c _).isLt
    obtain ⟨h1, h2, -⟩ := hτo (sigHat (σ c) r) hm
    refine ⟨h1, ?_, ?_⟩
    · rw [h2, permMI_val]; exact hμ _
    · rw [h2, permMI_val]; exact hν _
  have hhoa : ∀ c : Fin v.cosets.length,
      auxTrue P.aD ((fun l => τo (sigHat (σ c) l)) 4).val ((permMI (σ c) μ) 4).val ((permMI (σ c) ν) 4).val := by
    intro c
    simp only [permMI_val, sigHat_four, auxTrue, hτoa]
    exact ⟨hμ 4, hν 4⟩
  have hce : ∀ c : Fin v.cosets.length,
      coord P.aOff P.aD ((fun l => τo (sigHat (σ c) l)) 4).val ((permMI (σ c) μ) 4).val ((permMI (σ c) ν) 4).val = e := by
    intro c
    rw [heq]
    simp only [permMI_val, sigHat_four]
    rw [MI_val_congr μ (sigHat_four (σ c)), MI_val_congr ν (sigHat_four (σ c))]
  have ht' : ∀ (c : Fin v.cosets.length) (r : Fin 5), r.val < 4 →
      coord P.off1 P.d1 ((fun l => τo (sigHat (σ c) l)) r).val ((permMI (σ c) μ) r).val ((permMI (σ c) ν) r).val < 23 := by
    intro c r hr
    have hm : (sigHat (σ c) r).val < 4 := by rw [sigHat_val_lt _ hr]; exact (σ c _).isLt
    simp only [permMI_val]
    exact ht23 _ hm _ _ (hμ _) (hν _)
  have hbase : P.aOff.getD (τ 4).val 0 = R.auxOff.getD v.ai 0 := by rw [hPaO, hτai]
  by_cases hx : (xInv R v).getD e (sq v.dims 4) < sq v.dims 4
  · rw [if_pos hx]
    set x4 := (xInv R v).getD e (sq v.dims 4) with hx4
    have hpre : R.auxDest.getD (R.auxOff.getD v.ai 0 + x4) 0 = e := (xInv_spec R v he70').1 hx
    have hx4' : x4 < dims 4 * dims 4 := by rw [← hsq4]; exact hx
    have hdest0 : ∀ x < dims 4 * dims 4, P.aDest.getD (P.aOff.getD (τ 4).val 0 + x) 0 = e ↔ x = x4 := by
      intro x hxl
      rw [hPaD, hbase]
      constructor
      · intro h
        exact hinj x x4 (by rw [hsq4]; exact hxl) hx (h.trans hpre.symm)
      · intro h
        rw [h]
        exact hpre
    have hterm : ∀ c : Fin v.cosets.length, reindexMI (σ c)
        (phiMap (F := P0.fam) (F' := P3.fam) (phiPad P) (fun l => τo (sigHat (σ c) l)) τ
          (padRC dims (Gq.map fun q => (q : ℂ)))) μ ν =
        ((t4Arr R (flatOf R.phiNum 23 23) v (t0Arr v (gArr v j))).getD
          ((((sCoord R o p q' (sOf (v.cosets.getD c.val default).2 0) * 23 +
            sCoord R o p q' (sOf (v.cosets.getD c.val default).2 1)) * 23 +
            sCoord R o p q' (sOf (v.cosets.getD c.val default).2 2)) * 23 +
            sCoord R o p q' (sOf (v.cosets.getD c.val default).2 3)) * sq v.dims 4 + x4) 0 : ℂ) / 192 ^ 4 := by
      intro c
      have hr : reindexMI (σ c) (phiMap (F := P0.fam) (F' := P3.fam) (phiPad P) (fun l => τo (sigHat (σ c) l)) τ
          (padRC dims (Gq.map fun q => (q : ℂ)))) μ ν =
          phiMap (F := P0.fam) (F' := P3.fam) (phiPad P) (fun l => τo (sigHat (σ c) l)) τ
            (padRC dims (Gq.map fun q => (q : ℂ))) (permMI (σ c) μ) (permMI (σ c) ν) := rfl
      rw [hr, lift_eq R v j P hPn hPo0 hB hL hd hpos hn (fun l => τo (sigHat (σ c) l)) τ (permMI (σ c) μ)
        (permMI (σ c) ν) Gq hG (hho c) (hhoa c) hτ hτst hτa hx4'
        (fun x hxl => by rw [hce c]; exact hdest0 x hxl) hoff (ht' c)]
      rw [hco c 0 (by decide), hco c 1 (by decide), hco c 2 (by decide), hco c 3 (by decide)]
      rfl
    rw [Finset.sum_congr rfl fun c _ => hterm c, ← Finset.sum_div]
    refine congrArg (fun z : ℂ => z / 192 ^ 4) ?_
    push_cast
    rw [Finset.sum_range]
  · rw [if_neg hx]
    have hnone0 := xInv_none R v he70' hx
    have hterm : ∀ c : Fin v.cosets.length, reindexMI (σ c)
        (phiMap (F := P0.fam) (F' := P3.fam) (phiPad P) (fun l => τo (sigHat (σ c) l)) τ
          (padRC dims (Gq.map fun q => (q : ℂ)))) μ ν = 0 := by
      intro c
      show phiMap (F := P0.fam) (F' := P3.fam) (phiPad P) (fun l => τo (sigHat (σ c) l)) τ
          (padRC dims (Gq.map fun q => (q : ℂ))) (permMI (σ c) μ) (permMI (σ c) ν) = 0
      refine lift_eq_none P hB hd hpos _ τ _ _ _ (hho c) (hhoa c) hτ hτa fun x hxl => ?_
      rw [hce c, hPaD, hbase]
      exact hnone0 x (by rw [hsq4]; exact hxl)
    rw [Finset.sum_congr rfl fun c _ => hterm c, Finset.sum_const_zero]
    simp

end NPT.CP3.D1
