/-
NPT.CP3.PD — the intertwining of the padded cut-() modules, `Intertw (PD 0) πp`.

It follows from the kernel row checks `interSite_sum`, `interAux_sum` and the decided relation between `flatPerm` and
composition with `pf g` (`PDdef`).
-/
import NPT.CP3.PDdef
import NPT.CP3.ChecksD2

open Matrix BigOperators Finset NPT.Brauer NPT.Cert

namespace NPT.CP3.Inst

open NPT.CP3 NPT.CP3.Data NPT.CP3.Chk

/-- Site intertwining, non-dependent form. -/
lemma site_intertw (k : Fin 5) (g : Fin 24) (x : Dig 3 4) (a : Fin 3) :
    MsC 0 k (x ∘ pf g) a = ∑ b : Fin 3, MsC 0 k x b * πsite k g b a := by
  by_cases ha : a.val < sdim 0 k
  · have hk : k.val < 4 := by
      by_contra hk
      have hk4 : k.val = 4 := by omega
      rw [hk4, sdim4] at ha; omega
    let F : ℕ → ℂ := fun b => ((mget ((siteJ.getD 0 []).getD k []) (Sem.flat x) b : ℤ) : ℂ) *
      ((mget ((piSite.getD k []).getD g []) b a : ℤ) : ℂ)
    have e1 : ∀ b : Fin 3, MsC 0 k x b * πsite k g b a = if b.val < sdim 0 k then F b.val else 0 := by
      intro b
      unfold MsC πsite
      by_cases hb : b.val < sdim 0 k
      · simp [hb, ha, F]
      · simp [hb]
    have hR : ∑ b : Fin 3, MsC 0 k x b * πsite k g b a = ∑ b ∈ Finset.range (sdim 0 k), F b :=
      (Finset.sum_congr rfl fun b _ => e1 b).trans (sum_fin_range (sdim_le k) F)
    have h := interSite_sum k hk g g.isLt (Sem.flat x) (flat3_lt x) a ha
    rw [flatPerm3 g x] at h
    have hL : MsC 0 k (x ∘ pf g) a =
        ((mget ((siteJ.getD 0 []).getD k []) (Sem.flat (x ∘ pf g)) a : ℤ) : ℂ) := by
      simp only [MsC, if_pos ha]
    refine hL.trans (Eq.trans ?_ hR.symm)
    have h' := congrArg (fun q : ℤ => (q : ℂ)) h
    simp only [Int.cast_sum, Int.cast_mul] at h'
    exact h'
  · unfold MsC
    rw [if_neg ha]
    symm
    refine Finset.sum_eq_zero fun b _ => ?_
    unfold πsite
    simp [ha]

/-- Auxiliary intertwining, non-dependent form. -/
lemma aux_intertw (li : Fin 5) (g : Fin 24) (z : Dig 2 4) (j : Fin 6) :
    MaC 0 li (z ∘ pf g) j = ∑ j' : Fin 6, MaC 0 li z j' * πaux li g j' j := by
  by_cases hj : j.val < (ablk 0 li).length
  · let F : ℕ → ℂ := fun j' => (((if (ablk 0 li).getD j' 0 = Sem.flat z then (1 : ℤ) else 0) : ℤ) : ℂ) *
      ((mget (((auxM.getD 0 []).getD li []).getD g []) j' j : ℤ) : ℂ)
    have e1 : ∀ j' : Fin 6, MaC 0 li z j' * πaux li g j' j =
        if j'.val < (ablk 0 li).length then F j'.val else 0 := by
      intro j'
      unfold MaC πaux
      by_cases hj' : j'.val < (ablk 0 li).length
      · by_cases he : (ablk 0 li).getD j' 0 = Sem.flat z <;> simp [hj', hj, he, F]
      · simp [hj']
    have hR : ∑ j' : Fin 6, MaC 0 li z j' * πaux li g j' j = ∑ j' ∈ Finset.range (ablk 0 li).length, F j' :=
      (Finset.sum_congr rfl fun j' _ => e1 j').trans (sum_fin_range (ablk_le li) F)
    have h := interAux_sum li li.isLt g g.isLt (Sem.flat z) (flat2_lt z) j hj
    rw [flatPerm2 g z] at h
    have hL : MaC 0 li (z ∘ pf g) j =
        (((if (ablk 0 li).getD j 0 = Sem.flat (z ∘ pf g) then (1 : ℤ) else 0) : ℤ) : ℂ) := by
      by_cases he : (ablk 0 li).getD j 0 = Sem.flat (z ∘ pf g) <;> simp [MaC, hj, he]
    refine hL.trans (Eq.trans ?_ hR.symm)
    have h' := congrArg (fun q : ℤ => (q : ℂ)) h
    simp only [Int.cast_sum, Int.cast_mul] at h'
    exact h'
  · unfold MaC
    rw [if_neg hj]
    symm
    refine Finset.sum_eq_zero fun j' _ => ?_
    unfold πaux
    simp [hj]

/-- **Intertwining** of the padded cut-() modules: `V_g M_l^k = M_l^k πp_l^k(g)` for every factor, label and `g`. -/
theorem PD_intertw : Intertw (PD 0) πp := by
  intro l k g
  ext x a
  rw [VG_mul_apply_row, Matrix.mul_apply]
  by_cases h : l.val < 4
  · have hM : ∀ y b, (PD 0).M l k y b = MsC 0 k (Fin.cast (nfC_site h) ∘ y) (Fin.cast (dpad_site h) b) :=
      fun y b => dif_pos h
    have hπ : ∀ b c, πp l k g b c = πsite k g (Fin.cast (dpad_site h) b) (Fin.cast (dpad_site h) c) := by
      intro b c; unfold πp; rw [dif_pos h]
    calc (PD 0).M l k (x ∘ pf g) a
        = MsC 0 k ((Fin.cast (nfC_site h) ∘ x) ∘ pf g) (Fin.cast (dpad_site h) a) := hM _ _
      _ = ∑ b : Fin 3, MsC 0 k (Fin.cast (nfC_site h) ∘ x) b * πsite k g b (Fin.cast (dpad_site h) a) :=
          site_intertw k g _ _
      _ = ∑ j : Fin (dpad l), MsC 0 k (Fin.cast (nfC_site h) ∘ x) (Fin.cast (dpad_site h) j) *
            πsite k g (Fin.cast (dpad_site h) j) (Fin.cast (dpad_site h) a) :=
          (Fin.sum_congr' (fun b => MsC 0 k (Fin.cast (nfC_site h) ∘ x) b *
            πsite k g b (Fin.cast (dpad_site h) a)) (dpad_site h)).symm
      _ = ∑ j, (PD 0).M l k x j * πp l k g j a := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hM, hπ]
  · have hM : ∀ y b, (PD 0).M l k y b = MaC 0 k (Fin.cast (nfC_aux h) ∘ y) (Fin.cast (dpad_aux h) b) :=
      fun y b => dif_neg h
    have hπ : ∀ b c, πp l k g b c = πaux k g (Fin.cast (dpad_aux h) b) (Fin.cast (dpad_aux h) c) := by
      intro b c; unfold πp; rw [dif_neg h]
    calc (PD 0).M l k (x ∘ pf g) a
        = MaC 0 k ((Fin.cast (nfC_aux h) ∘ x) ∘ pf g) (Fin.cast (dpad_aux h) a) := hM _ _
      _ = ∑ b : Fin 6, MaC 0 k (Fin.cast (nfC_aux h) ∘ x) b * πaux k g b (Fin.cast (dpad_aux h) a) :=
          aux_intertw k g _ _
      _ = ∑ j : Fin (dpad l), MaC 0 k (Fin.cast (nfC_aux h) ∘ x) (Fin.cast (dpad_aux h) j) *
            πaux k g (Fin.cast (dpad_aux h) j) (Fin.cast (dpad_aux h) a) :=
          (Fin.sum_congr' (fun b => MaC 0 k (Fin.cast (nfC_aux h) ∘ x) b *
            πaux k g b (Fin.cast (dpad_aux h) a)) (dpad_aux h)).symm
      _ = ∑ j, (PD 0).M l k x j * πp l k g j a := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hM, hπ]

end NPT.CP3.Inst
