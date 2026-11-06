/-
NPT.CP3.FourierAux — the auxiliary Fourier facts of the lift (`FourierAt` on the factor `4`, at every matrix) for
padded module families whose auxiliary modules select the strings listed in blocks (`MaC`), reduced to finite checks:
* every true input coordinate that `aDest` sends to a true output coordinate `(κ, a', b')` carries the partially
  transposed pair of strings of `(κ, a', b')` (`hstr`), and
* exactly one true input coordinate is sent to each true output coordinate (`hcnt`).
-/
import NPT.CP3.PhiDef
import NPT.CP3.Fourier

open Matrix BigOperators Finset NPT.Cert NPT.Cert.Sem NPT.Brauer

namespace NPT.CP3

/-- A string of the auxiliary factor is determined by its flat index. -/
lemma ind_flat {l : Fin 5} (hl : ¬ l.val < 4) {n : ℕ} (hn : n < 16) (z : Dig (nfC l) 4) :
    n = Sem.flat (Fin.cast (nfC_aux hl) ∘ z) ↔ z = Fin.cast (nfC_aux hl).symm ∘ NPT.Cert.Ident.unflat 2 4 n := by
  constructor
  · intro h
    have e : NPT.Cert.Ident.unflat 2 4 n = Fin.cast (nfC_aux hl) ∘ z := by
      rw [h, NPT.Cert.Ident.unflat_flat]
    funext s
    apply Fin.ext
    have h2 := congrFun e s
    simp only [Function.comp_apply, Fin.coe_cast, h2]
  · intro h
    rw [h]
    have e : Fin.cast (nfC_aux hl) ∘ (Fin.cast (nfC_aux hl).symm ∘ NPT.Cert.Ident.unflat 2 4 n) =
        NPT.Cert.Ident.unflat 2 4 n := by
      funext s
      apply Fin.ext
      simp only [Function.comp_apply, Fin.coe_cast]
    rw [e, NPT.Cert.Ident.flat_unflat n (lt_of_lt_of_eq hn (by norm_num))]

/-- **Gram forms on padded auxiliary modules selecting the strings of lists.** -/
lemma gramLoc_aux (P : PadData) (B : Fin 5 → List ℕ)
    (hM : ∀ k z j, P.Ma k z j =
      if j.val < (B k).length then (if (B k).getD j.val 0 = Sem.flat z then 1 else 0) else 0)
    (h16 : ∀ k : Fin 5, ∀ j < (B k).length, (B k).getD j 0 < 16)
    {l : Fin 5} (hl : ¬ l.val < 4) (k : Fin 5) (X : Matrix (Dig (nfC l) 4) (Dig (nfC l) 4) ℂ) (a b : Fin (dpad l)) :
    gramLoc P.fam l k X a b =
      if a.val < (B k).length ∧ b.val < (B k).length then
        X (Fin.cast (nfC_aux hl).symm ∘ NPT.Cert.Ident.unflat 2 4 ((B k).getD a.val 0))
          (Fin.cast (nfC_aux hl).symm ∘ NPT.Cert.Ident.unflat 2 4 ((B k).getD b.val 0))
      else 0 := by
  have hMz : ∀ (z : Dig (nfC l) 4) (j : Fin (dpad l)), P.M l k z j =
      if j.val < (B k).length then
        (if (B k).getD j.val 0 = Sem.flat (Fin.cast (nfC_aux hl) ∘ z) then 1 else 0) else 0 := by
    intro z j
    simp only [PadData.M, dif_neg hl]
    rw [hM, Fin.coe_cast]
  unfold gramLoc
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hMz]
  by_cases ha : a.val < (B k).length
  · by_cases hb : b.val < (B k).length
    · have ea := ind_flat hl (h16 k _ ha)
      have eb := ind_flat hl (h16 k _ hb)
      simp only [if_pos ha, if_pos hb, if_pos (And.intro ha hb), ea, eb, ite_mul, one_mul, zero_mul, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    · rw [if_neg (fun h => hb h.2)]
      simp only [if_neg hb, mul_zero, Finset.sum_const_zero]
  · rw [if_neg (fun h => ha h.1)]
    simp only [if_neg ha, zero_mul, Finset.sum_const_zero]

/-- **The auxiliary Fourier facts** from the finite checks on the block lists. -/
theorem fourierAt_aux (P : PhiLists) (P0 P1 : PadData) (B0 B1 : Fin 5 → List ℕ)
    (hM0 : ∀ k z j, P0.Ma k z j =
      if j.val < (B0 k).length then (if (B0 k).getD j.val 0 = Sem.flat z then 1 else 0) else 0)
    (hM1 : ∀ k z j, P1.Ma k z j =
      if j.val < (B1 k).length then (if (B1 k).getD j.val 0 = Sem.flat z then 1 else 0) else 0)
    (h16a : ∀ k : Fin 5, ∀ j < (B0 k).length, (B0 k).getD j 0 < 16)
    (h16b : ∀ k : Fin 5, ∀ j < (B1 k).length, (B1 k).getD j 0 < 16)
    (hl0 : ∀ k : Fin 5, (B0 k).length = P.aD.getD k.val 0) (hl1 : ∀ k : Fin 5, (B1 k).length = P.aD.getD k.val 0)
    (hstr : ∀ κ : Fin 5, ∀ a' < P.aD.getD κ.val 0, ∀ b' < P.aD.getD κ.val 0, ∀ la : Fin 5,
      ∀ a < P.aD.getD la.val 0, ∀ b < P.aD.getD la.val 0,
      P.aDest.getD (coord P.aOff P.aD la.val a b) 0 = coord P.aOff P.aD κ.val a' b' →
      (∀ s : Fin 4, NPT.Cert.Ident.unflat 2 4 ((B0 la).getD a 0) s =
          Function.update (NPT.Cert.Ident.unflat 2 4 ((B1 κ).getD a' 0)) 3
            (NPT.Cert.Ident.unflat 2 4 ((B1 κ).getD b' 0) 3) s) ∧
        (∀ s : Fin 4, NPT.Cert.Ident.unflat 2 4 ((B0 la).getD b 0) s =
          Function.update (NPT.Cert.Ident.unflat 2 4 ((B1 κ).getD b' 0)) 3
            (NPT.Cert.Ident.unflat 2 4 ((B1 κ).getD a' 0) 3) s))
    (hcnt : ∀ κ : Fin 5, ∀ a' < P.aD.getD κ.val 0, ∀ b' < P.aD.getD κ.val 0,
      (∑ la : Fin 5, ∑ a : Fin (dpad 4), ∑ b : Fin (dpad 4),
        if auxTrue P.aD la.val a.val b.val ∧
          P.aDest.getD (coord P.aOff P.aD la.val a.val b.val) 0 = coord P.aOff P.aD κ.val a' b' then 1 else 0 : ℕ) = 1) :
    ∀ X, FourierAt (F := P0.fam) (F' := P1.fam) (phiPad P) 4 X := by
  intro X
  have hl : ¬ (4 : Fin 5).val < 4 := by decide
  have key : ∀ (κ : Fin 5) (a' b' : Fin (dpad 4)), gramLoc P1.fam 4 κ (ptLoc X) a' b' =
      ∑ la : Fin 5, ∑ a : Fin (dpad 4), ∑ b : Fin (dpad 4),
        phiPad P 4 κ a' b' la a b * gramLoc P0.fam 4 la X a b := by
    intro κ a' b'
    rw [gramLoc_aux P1 B1 hM1 h16b hl κ (ptLoc X) a' b']
    simp only [gramLoc_aux P0 B0 hM0 h16a hl]
    by_cases ht : auxTrue P.aD κ.val a'.val b'.val
    · obtain ⟨ha', hb'⟩ := ht
      have ha1 : a'.val < (B1 κ).length := by rw [hl1]; exact ha'
      have hb1 : b'.val < (B1 κ).length := by rw [hl1]; exact hb'
      rw [if_pos ⟨ha1, hb1⟩]
      have term : ∀ (la : Fin 5) (a b : Fin (dpad 4)), phiPad P 4 κ a' b' la a b *
          (if a.val < (B0 la).length ∧ b.val < (B0 la).length then
            X (Fin.cast (nfC_aux hl).symm ∘ NPT.Cert.Ident.unflat 2 4 ((B0 la).getD a.val 0))
              (Fin.cast (nfC_aux hl).symm ∘ NPT.Cert.Ident.unflat 2 4 ((B0 la).getD b.val 0)) else 0) =
          (if auxTrue P.aD la.val a.val b.val ∧
            P.aDest.getD (coord P.aOff P.aD la.val a.val b.val) 0 = coord P.aOff P.aD κ.val a'.val b'.val then (1 : ℂ)
            else 0) *
          ptLoc X (Fin.cast (nfC_aux hl).symm ∘ NPT.Cert.Ident.unflat 2 4 ((B1 κ).getD a'.val 0))
            (Fin.cast (nfC_aux hl).symm ∘ NPT.Cert.Ident.unflat 2 4 ((B1 κ).getD b'.val 0)) := by
        intro la a b
        rw [phiPad_aux P hl κ a' b' la a b ⟨ha', hb'⟩]
        by_cases hC : auxTrue P.aD la.val a.val b.val ∧
            P.aDest.getD (coord P.aOff P.aD la.val a.val b.val) 0 = coord P.aOff P.aD κ.val a'.val b'.val
        · simp only [if_pos hC, one_mul]
          obtain ⟨⟨ha, hb⟩, hd⟩ := hC
          have ha0 : a.val < (B0 la).length := by rw [hl0]; exact ha
          have hb0 : b.val < (B0 la).length := by rw [hl0]; exact hb
          rw [if_pos ⟨ha0, hb0⟩]
          obtain ⟨s1, s2⟩ := hstr κ a'.val ha' b'.val hb' la a.val ha b.val hb hd
          have s1f : NPT.Cert.Ident.unflat 2 4 ((B0 la).getD a.val 0) =
              Function.update (NPT.Cert.Ident.unflat 2 4 ((B1 κ).getD a'.val 0)) 3
                (NPT.Cert.Ident.unflat 2 4 ((B1 κ).getD b'.val 0) 3) := funext s1
          have s2f : NPT.Cert.Ident.unflat 2 4 ((B0 la).getD b.val 0) =
              Function.update (NPT.Cert.Ident.unflat 2 4 ((B1 κ).getD b'.val 0)) 3
                (NPT.Cert.Ident.unflat 2 4 ((B1 κ).getD a'.val 0) 3) := funext s2
          have e1 : (Fin.cast (nfC_aux hl).symm ∘ NPT.Cert.Ident.unflat 2 4 ((B0 la).getD a.val 0)) =
              Function.update (Fin.cast (nfC_aux hl).symm ∘ NPT.Cert.Ident.unflat 2 4 ((B1 κ).getD a'.val 0)) 3
                ((Fin.cast (nfC_aux hl).symm ∘ NPT.Cert.Ident.unflat 2 4 ((B1 κ).getD b'.val 0)) 3) := by
            simp only [s1f, Function.comp_update, Function.comp_apply]
          have e2 : (Fin.cast (nfC_aux hl).symm ∘ NPT.Cert.Ident.unflat 2 4 ((B0 la).getD b.val 0)) =
              Function.update (Fin.cast (nfC_aux hl).symm ∘ NPT.Cert.Ident.unflat 2 4 ((B1 κ).getD b'.val 0)) 3
                ((Fin.cast (nfC_aux hl).symm ∘ NPT.Cert.Ident.unflat 2 4 ((B1 κ).getD a'.val 0)) 3) := by
            simp only [s2f, Function.comp_update, Function.comp_apply]
          rw [e1, e2]
          rfl
        · simp only [if_neg hC, zero_mul]
      simp only [term]
      simp only [← Finset.sum_mul]
      have hc := congrArg (fun n : ℕ => (n : ℂ)) (hcnt κ a'.val ha' b'.val hb')
      push_cast at hc
      rw [hc, one_mul]
    · rw [if_neg (fun h => ht ⟨by rw [← hl1]; exact h.1, by rw [← hl1]; exact h.2⟩)]
      symm
      refine Finset.sum_eq_zero fun la _ => Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
      rw [show phiPad P 4 κ a' b' la a b = 0 by
        simp only [phiPad, if_neg hl]
        rw [if_neg]
        exact fun h => ht h.1, zero_mul]
  unfold FourierAt
  intro κ
  ext a' b'
  exact key κ a' b'

end NPT.CP3
