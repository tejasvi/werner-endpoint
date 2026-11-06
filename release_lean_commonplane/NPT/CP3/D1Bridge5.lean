/-
NPT.CP3.D1Bridge5 — the native D1 computation against the semantics of `NPT.CP3.Fsem` (part 5): the projected block
coefficient of a cut-`()` output block.
-/
import NPT.CP3.D1Bridge4

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem NPT.Cert.SymAvg NPT.CP3.Ctr NPT.CP3.Data

namespace NPT.CP3.D1

open NPT.CP3

/-- Facts about a cut-`()` output block. -/
structure OutH0 (P : PhiLists) (o : OutB) (dims' : Fin 5 → ℕ) (n' : ℕ) (τo : Fin 5 → Fin 5) : Prop where
  hB' : BoxOK dims' n'
  hL' : ∀ l : Fin 5, dims' l = o.dims.getD l.val 1
  hn' : n' = boxN o.dims
  hτo : ∀ m : Fin 5, m.val < 4 → P.d0.getD (τo m).val 0 = dims' m
  hτoa : P.aD.getD (τo 4).val 0 = dims' 4

/-- The coset term of a cut-`()` block at a true output entry. -/
theorem H0_term (P : PhiLists) (R : Raw) (v : VarB) (j : ℕ) (o : OutB) {dims : Fin 5 → ℕ} {n : ℕ}
    {τ : Fin 5 → Fin 5} (hv : VarH R P v dims n τ) (Gq : Matrix (Fin n) (Fin n) ℚ)
    (hG : ∀ a b : Fin n, Gq a b = (((gArr v j).getD (a.val * n + b.val) 0 : ℤ) : ℚ))
    {dims' : Fin 5 → ℕ} {n' : ℕ} {τo : Fin 5 → Fin 5} (ho : OutH0 P o dims' n' τo)
    (σ : Equiv.Perm (Fin 4)) (s : List ℕ) (hσ : ∀ m : Fin 4, (σ m).val = sOf s m.val)
    (hτσ : (fun l => τo (sigHat σ l)) = τ) (μ ν : MI) (hμ : inBox dims' μ) (hν : inBox dims' ν) :
    reindexMI σ (padRC dims (Gq.map fun q => (q : ℂ))) μ ν =
      (((gArr v j).getD (flat5 v.dims (digit o.dims (flatTrue dims' μ) (sOf s 0))
        (digit o.dims (flatTrue dims' μ) (sOf s 1)) (digit o.dims (flatTrue dims' μ) (sOf s 2))
        (digit o.dims (flatTrue dims' μ) (sOf s 3)) (digit o.dims (flatTrue dims' μ) 4) * boxN v.dims +
        flat5 v.dims (digit o.dims (flatTrue dims' ν) (sOf s 0)) (digit o.dims (flatTrue dims' ν) (sOf s 1))
        (digit o.dims (flatTrue dims' ν) (sOf s 2)) (digit o.dims (flatTrue dims' ν) (sOf s 3))
        (digit o.dims (flatTrue dims' ν) 4)) 0 : ℤ) : ℂ) := by
  -- the reindexed entry lies in the box of the variable
  have hdim : ∀ l : Fin 5, dims l = dims' (sigHat σ l) := by
    intro l
    by_cases hl : l.val < 4
    · have hm : (sigHat σ l).val < 4 := (sigHat_lt σ l).2 hl
      rw [← ho.hτo _ hm, ← (hv.hτ l hl).2, ← congrFun hτσ l]
    · obtain rfl := fin5_eq4 l hl
      rw [sigHat_four, ← ho.hτoa, ← hv.hτa, ← congrFun hτσ 4, sigHat_four]
  have hbox : ∀ ξ : MI, inBox dims' ξ → inBox dims (permMI σ ξ) := by
    intro ξ hξ
    unfold inBox at hξ ⊢
    intro l
    rw [permMI_val, hdim l]
    exact hξ _
  have hpos : ∀ (ξ : MI) (hξ : inBox dims' ξ), flatPos dims (n := n) (permMI σ ξ) =
      some ⟨flatTrue dims (permMI σ ξ), (hv.hB.1 _ (hbox ξ hξ)).1⟩ := by
    intro ξ hξ
    unfold flatPos
    rw [dif_pos ⟨hbox ξ hξ, (hv.hB.1 _ (hbox ξ hξ)).1⟩]
  -- the flat index of the reindexed entry
  have hfl : ∀ ξ : MI, inBox dims' ξ → flatTrue dims (permMI σ ξ) =
      flat5 v.dims (digit o.dims (flatTrue dims' ξ) (sOf s 0)) (digit o.dims (flatTrue dims' ξ) (sOf s 1))
        (digit o.dims (flatTrue dims' ξ) (sOf s 2)) (digit o.dims (flatTrue dims' ξ) (sOf s 3))
        (digit o.dims (flatTrue dims' ξ) 4) := by
    intro ξ hξ
    rw [flatTrue_eq dims v.dims hv.hL]
    have dξ : ∀ l : Fin 5, digit o.dims (flatTrue dims' ξ) l.val = (ξ l).val :=
      digit_flatTrue dims' o.dims ho.hL' ξ hξ
    have hs : ∀ q : Fin 5, q.val < 4 → (sigHat σ q).val = sOf s q.val := by
      intro q hq; rw [sigHat_val_lt σ hq, hσ]
    have e : ∀ q : Fin 5, q.val < 4 → ((permMI σ ξ) q).val = digit o.dims (flatTrue dims' ξ) (sOf s q.val) := by
      intro q hq; rw [permMI_val, ← hs q hq, dξ]
    have e4 : ((permMI σ ξ) 4).val = digit o.dims (flatTrue dims' ξ) 4 := by
      rw [permMI_val, MI_val_congr ξ (sigHat_four σ)]; exact (dξ 4).symm
    rw [e 0 (by decide), e 1 (by decide), e 2 (by decide), e 3 (by decide), e4]
    rfl
  show padRC dims (Gq.map fun q => (q : ℂ)) (permMI σ μ) (permMI σ ν) = _
  unfold padRC
  rw [hpos μ hμ, hpos ν hν]
  simp only [Matrix.map_apply, hG]
  push_cast
  rw [hfl μ hμ, hfl ν hν, hv.hn]

/-- **The projected cut-`()` block coefficient of one coordinate.** -/
theorem fOut0_bridge (R : Raw) (v : VarB) (j : ℕ) (o : OutB) (P : PhiLists) {dims : Fin 5 → ℕ} {n : ℕ}
    {τ : Fin 5 → Fin 5} (hv : VarH R P v dims n τ) (Gq : Matrix (Fin n) (Fin n) ℚ)
    (hG : ∀ a b : Fin n, Gq a b = (((gArr v j).getD (a.val * n + b.val) 0 : ℤ) : ℚ))
    {dims' : Fin 5 → ℕ} {n' : ℕ} {τo : Fin 5 → Fin 5} (ho : OutH0 P o dims' n' τo)
    (σ : Fin v.cosets.length → Equiv.Perm (Fin 4))
    (hσ : ∀ c (m : Fin 4), (σ c m).val = sOf (v.cosets.getD c.val default).2 m.val)
    (new : Fin v.cosets.length → Fin 5 → Fin 5)
    (hnew : ∀ c, new c = τo ↔ ((v.cosets.getD c.val default).1 = o.st ∧ v.ai = o.ai))
    (hcos : ∀ c, (fun l => new c (sigHat (σ c) l)) = τ)
    (Vq : Matrix (Fin n') (Fin o.m) ℂ) (hVq : ∀ p u, Vq p u = ((lg o.V p.val u.val : ℤ) : ℂ)) (u w : Fin o.m) :
    ((padR dims' Vq)ᵀ * (∑ c : Fin v.cosets.length,
      if new c = τo then reindexMI (σ c) (padRC dims (Gq.map fun q => (q : ℂ))) else 0) * padR dims' Vq) u w =
      (((fOut0 v (gArr v j) o).getD u.val []).getD w.val 0 : ℂ) := by
  rw [vtv_padR ho.hB' Vq _ u w]
  have hH : ∀ p q : Fin n', (∑ c : Fin v.cosets.length,
      if new c = τo then reindexMI (σ c) (padRC dims (Gq.map fun q => (q : ℂ))) else 0) (unflat dims' p)
        (unflat dims' q) =
      if v.ai = o.ai then (h0Entry v (gArr v j) o p.val q.val : ℂ) else 0 := by
    intro p q
    rw [Matrix.sum_apply]
    have hμ := inBox_unflat ho.hB' p.isLt
    have hν := inBox_unflat ho.hB' q.isLt
    by_cases hai : v.ai = o.ai
    · rw [if_pos hai]
      unfold h0Entry
      push_cast
      rw [Finset.sum_range]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hc : (v.cosets.getD c.val default).1 = o.st
      · have hnc : new c = τo := (hnew c).2 ⟨hc, hai⟩
        rw [if_pos hnc, if_pos hc]
        have hτσ : (fun l => τo (sigHat (σ c) l)) = τ := by rw [← hnc]; exact hcos c
        have e := H0_term P R v j o hv Gq hG ho (σ c) (v.cosets.getD c.val default).2 (hσ c) hτσ
          (unflat dims' p) (unflat dims' q) hμ hν
        rw [flatTrue_unflat ho.hB' p.isLt, flatTrue_unflat ho.hB' q.isLt] at e
        exact e
      · have hnc : new c ≠ τo := fun h => hc ((hnew c).1 h).1
        rw [if_neg hnc, if_neg hc]
        rfl
    · rw [if_neg hai]
      refine Finset.sum_eq_zero fun c _ => ?_
      have hnc : new c ≠ τo := fun h => hai ((hnew c).1 h).2
      rw [if_neg hnc]
      rfl
  simp only [hH, hVq]
  rw [fOut0_spec v _ o u.isLt w.isLt]
  by_cases hg : (v.ai == o.ai && v.cosets.any (fun c => c.1 == o.st)) = true
  · rw [if_pos hg]
    have hai : v.ai = o.ai := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hg; exact hg.1
    simp only [if_pos hai]
    push_cast
    rw [show Finset.range (boxN o.dims) = Finset.range n' by rw [ho.hn']]
    simp only [Finset.sum_range, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  · rw [if_neg hg]
    by_cases hai : v.ai = o.ai
    · -- no coset reaches the output tuple: every `h0Entry` vanishes
      have hnone : ∀ c : Fin v.cosets.length, (v.cosets.getD c.val default).1 ≠ o.st := by
        intro c hc
        apply hg
        simp only [Bool.and_eq_true, beq_iff_eq, List.any_eq_true]
        refine ⟨hai, v.cosets.getD c.val default, ?_, by rw [hc]⟩
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem c.isLt, Option.getD_some]
        exact List.getElem_mem c.isLt
      have hz : ∀ p q : ℕ, h0Entry v (gArr v j) o p q = 0 := by
        intro p q
        unfold h0Entry
        refine Finset.sum_eq_zero fun c hc => ?_
        rw [if_neg (hnone ⟨c, Finset.mem_range.1 hc⟩)]
      simp only [if_pos hai, hz]
      simp
    · simp only [if_neg hai]
      simp

end NPT.CP3.D1
