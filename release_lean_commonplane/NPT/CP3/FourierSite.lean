/-
NPT.CP3.FourierSite — the site Fourier facts of the lift (`FourierAt` at the operators `VG 0 p` of a site factor) for
padded module families whose site modules come from integer lists, reduced to two finite checks on the data:
* the site Gram forms `siteM[c][k][p] = Σ_z J[z ∘ α][·] J[z ∘ β][·]` (`sgN`), and
* the Fourier relation `192 · siteM[1][κ][p] = Σ_λ phiNum[κ, λ] · siteM[0][λ][p]`.
-/
import NPT.CP3.Fourier
import NPT.CP3.PhiDef
import NPT.CP3.D1Spec
import NPT.CP3.D1Bridge

open Matrix BigOperators Finset NPT.Cert NPT.Cert.Sem NPT.Cert.Ident NPT.Brauer

namespace NPT.CP3

/-- The integer site Gram form of the module `J` at the operator `VG S p`: `Σ_z J[z ∘ α][a] J[z ∘ β][b]`. -/
def sgN (J : List (List Int)) (S : ℕ) (p : Fin 24) (a b : ℕ) : ℤ :=
  ∑ t ∈ Finset.range 81, D1.lg J (Sem.flat (NPT.Cert.Ident.unflat 3 4 t ∘ aSel S p)) a *
    D1.lg J (Sem.flat (NPT.Cert.Ident.unflat 3 4 t ∘ bSel S p)) b

/-- **Gram forms of the operators `VG S p` on padded site modules from lists.** -/
lemma gramLoc_site (P : PadData) (J : Fin 5 → List (List Int)) (sd : Fin 5 → ℕ)
    (hM : ∀ k x a, P.Ms k x a = if a.val < sd k then ((D1.lg (J k) (Sem.flat x) a.val : ℤ) : ℂ) else 0)
    {l : Fin 5} (hl : l.val < 4) (k : Fin 5) (S : ℕ) (p : Fin 24) (a b : Fin (dpad l)) :
    gramLoc P.fam l k (VG ℂ (nfC l) S p) a b =
      if a.val < sd k ∧ b.val < sd k then ((sgN (J k) S p a.val b.val : ℤ) : ℂ) else 0 := by
  unfold gramLoc
  rw [VG, compress_SelOp]
  have e : ∀ z : Dig (nfC l) 4, P.fam.M l k (z ∘ aSel S p) a * P.fam.M l k (z ∘ bSel S p) b =
      P.Ms k ((Fin.cast (nfC_site hl) ∘ z) ∘ aSel S p) (Fin.cast (dpad_site hl) a) *
        P.Ms k ((Fin.cast (nfC_site hl) ∘ z) ∘ bSel S p) (Fin.cast (dpad_site hl) b) := by
    intro z
    simp only [PadData.fam, PadData.M, dif_pos hl]
    rfl
  rw [Finset.sum_congr rfl fun z _ => e z]
  rw [show (∑ z : Dig (nfC l) 4, P.Ms k ((Fin.cast (nfC_site hl) ∘ z) ∘ aSel S p) (Fin.cast (dpad_site hl) a) *
        P.Ms k ((Fin.cast (nfC_site hl) ∘ z) ∘ bSel S p) (Fin.cast (dpad_site hl) b)) =
      ∑ z : Dig 3 4, P.Ms k (z ∘ aSel S p) (Fin.cast (dpad_site hl) a) *
        P.Ms k (z ∘ bSel S p) (Fin.cast (dpad_site hl) b) from
    Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl _) (finCongr (nfC_site hl))) _ _ fun z => rfl]
  rw [sum_dig_range]
  simp only [hM, Fin.coe_cast]
  by_cases ha : a.val < sd k
  · by_cases hb : b.val < sd k
    · rw [if_pos ⟨ha, hb⟩, sgN]
      push_cast
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [if_pos ha, if_pos hb]
    · rw [if_neg (fun h => hb h.2)]
      exact Finset.sum_eq_zero fun t _ => by rw [if_neg hb, mul_zero]
  · rw [if_neg (fun h => ha h.1)]
    exact Finset.sum_eq_zero fun t _ => by rw [if_neg ha, zero_mul]

/-- A sum over `Fin N` of terms vanishing at and beyond `d ≤ N` is the sum over `range d`. -/
lemma sum_fin_trunc {M : Type*} [AddCommMonoid M] {N d : ℕ} (hd : d ≤ N) (f : ℕ → M) :
    ∑ a : Fin N, (if a.val < d then f a.val else 0) = ∑ a ∈ Finset.range d, f a := by
  rw [Fin.sum_univ_eq_sum_range (fun a => if a < d then f a else 0) N]
  rw [← Finset.sum_range_add_sum_Ico _ hd]
  rw [Finset.sum_eq_zero (s := Finset.Ico d N) fun a ha => by
    rw [if_neg (by simp only [Finset.mem_Ico] at ha; omega)], add_zero]
  exact Finset.sum_congr rfl fun a ha => by rw [if_pos (Finset.mem_range.1 ha)]

/-- A sum over `Fin 5 × Fin N × Fin N` of terms vanishing off `λ < 4`, `a, b < D λ ≤ N` as nested range sums. -/
lemma sum_trunc3 {M : Type*} [AddCommMonoid M] {N : ℕ} (D : ℕ → ℕ) (hD : ∀ la < 4, D la ≤ N)
    (g : ℕ → ℕ → ℕ → M) :
    ∑ la : Fin 5, ∑ a : Fin N, ∑ b : Fin N,
      (if la.val < 4 ∧ a.val < D la.val ∧ b.val < D la.val then g la.val a.val b.val else 0) =
    ∑ la ∈ Finset.range 4, ∑ a ∈ Finset.range (D la), ∑ b ∈ Finset.range (D la), g la a b := by
  have inner : ∀ la : ℕ, ∑ a : Fin N, ∑ b : Fin N,
      (if la < 4 ∧ a.val < D la ∧ b.val < D la then g la a.val b.val else 0) =
      if la < 4 then ∑ a ∈ Finset.range (D la), ∑ b ∈ Finset.range (D la), g la a b else 0 := by
    intro la
    by_cases hla : la < 4
    · rw [if_pos hla]
      have e1 : ∀ a b : Fin N, (if la < 4 ∧ a.val < D la ∧ b.val < D la then g la a.val b.val else 0) =
          if a.val < D la then (if b.val < D la then g la a.val b.val else 0) else 0 := by
        intro a b
        by_cases ha : a.val < D la
        · by_cases hb : b.val < D la
          · rw [if_pos ⟨hla, ha, hb⟩, if_pos ha, if_pos hb]
          · rw [if_neg (fun h => hb h.2.2), if_pos ha, if_neg hb]
        · rw [if_neg (fun h => ha h.2.1), if_neg ha]
      have e2 : ∀ a : Fin N, (∑ b : Fin N, if a.val < D la then (if b.val < D la then g la a.val b.val else 0)
          else 0) = if a.val < D la then ∑ b ∈ Finset.range (D la), g la a.val b else 0 := by
        intro a
        by_cases ha : a.val < D la
        · simp only [if_pos ha]
          exact sum_fin_trunc (hD la hla) (fun b => g la a.val b)
        · simp only [if_neg ha]
          exact Finset.sum_const_zero
      simp only [e1, e2]
      exact sum_fin_trunc (hD la hla) (fun a => ∑ b ∈ Finset.range (D la), g la a b)
    · rw [if_neg hla]
      exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => if_neg (fun h => hla h.1)
  calc ∑ la : Fin 5, ∑ a : Fin N, ∑ b : Fin N,
        (if la.val < 4 ∧ a.val < D la.val ∧ b.val < D la.val then g la.val a.val b.val else 0)
      = ∑ la : Fin 5, (if la.val < 4 then
          ∑ a ∈ Finset.range (D la.val), ∑ b ∈ Finset.range (D la.val), g la.val a b else 0) :=
        Finset.sum_congr rfl fun la _ => inner la.val
    _ = ∑ la ∈ Finset.range 4, ∑ a ∈ Finset.range (D la), ∑ b ∈ Finset.range (D la), g la a b :=
        sum_fin_trunc (by norm_num) (fun la => ∑ a ∈ Finset.range (D la), ∑ b ∈ Finset.range (D la), g la a b)

/-- **The site Fourier facts** from the two finite checks. -/
theorem fourierAt_site (P : PhiLists) (P0 P1 : PadData) (J0 J1 : Fin 5 → List (List Int)) (sd0 sd1 : Fin 5 → ℕ)
    (hM0 : ∀ k x a, P0.Ms k x a = if a.val < sd0 k then ((D1.lg (J0 k) (Sem.flat x) a.val : ℤ) : ℂ) else 0)
    (hM1 : ∀ k x a, P1.Ms k x a = if a.val < sd1 k then ((D1.lg (J1 k) (Sem.flat x) a.val : ℤ) : ℂ) else 0)
    (hsd0 : ∀ k : Fin 5, sd0 k = P.d0.getD k.val 0) (hsd1 : ∀ k : Fin 5, sd1 k = P.d1.getD k.val 0)
    (hle0 : ∀ k : Fin 5, sd0 k ≤ 3) (h14 : P.d1.getD 4 0 = 0)
    (sM : ℕ → ℕ → Fin 24 → ℕ → ℕ → ℤ)
    (hA0 : ∀ k : Fin 5, k.val < 4 → ∀ p a b, a < sd0 k → b < sd0 k → sgN (J0 k) 0 p a b = sM 0 k p a b)
    (hA1 : ∀ k : Fin 5, k.val < 4 → ∀ p a b, a < sd1 k → b < sd1 k → sgN (J1 k) 8 p a b = sM 1 k p a b)
    (hB : ∀ p (κ : Fin 5), κ.val < 4 → ∀ a' b', a' < sd1 κ → b' < sd1 κ →
      192 * sM 1 κ p a' b' = ∑ la ∈ Finset.range 4, ∑ a ∈ Finset.range (P.d0.getD la 0),
        ∑ b ∈ Finset.range (P.d0.getD la 0),
          D1.phiE P (coord P.off1 P.d1 κ a' b') (coord P.off0 P.d0 la a b) * sM 0 la p a b) :
    ∀ l : Fin 5, l.val < 4 → ∀ p : Fin 24, FourierAt (F := P0.fam) (F' := P1.fam) (phiPad P) l (VG ℂ (nfC l) 0 p) := by
  intro l hl p
  have hdl : dpad l = 3 := dpad_site hl
  have key : ∀ (κ : Fin 5) (a' b' : Fin (dpad l)), gramLoc P1.fam l κ (VG ℂ (nfC l) 8 p) a' b' =
      ∑ la : Fin 5, ∑ a : Fin (dpad l), ∑ b : Fin (dpad l),
        phiPad P l κ a' b' la a b * gramLoc P0.fam l la (VG ℂ (nfC l) 0 p) a b := by
    intro κ a' b'
    rw [gramLoc_site P1 J1 sd1 hM1 hl κ 8 p a' b']
    simp only [gramLoc_site P0 J0 sd0 hM0 hl]
    by_cases ht : siteTrue P.d1 κ.val a'.val b'.val
    · obtain ⟨hκ, ha', hb'⟩ := ht
      have ha1 : a'.val < sd1 κ := by rw [hsd1]; exact ha'
      have hb1 : b'.val < sd1 κ := by rw [hsd1]; exact hb'
      rw [if_pos ⟨ha1, hb1⟩, hA1 κ hκ p _ _ ha1 hb1]
      -- the right side as a truncated sum
      have e : ∀ (la : Fin 5) (a b : Fin (dpad l)), phiPad P l κ a' b' la a b *
          (if a.val < sd0 la ∧ b.val < sd0 la then ((sgN (J0 la) 0 p a.val b.val : ℤ) : ℂ) else 0) =
          if la.val < 4 ∧ a.val < P.d0.getD la.val 0 ∧ b.val < P.d0.getD la.val 0 then
            (D1.phiE P (coord P.off1 P.d1 κ a' b') (coord P.off0 P.d0 la.val a.val b.val) : ℂ) / 192 *
              (sM 0 la.val p a.val b.val : ℂ) else 0 := by
        intro la a b
        by_cases hla : la.val < 4
        · by_cases ha : a.val < sd0 la
          · by_cases hb : b.val < sd0 la
            · have ha0 : a.val < P.d0.getD la.val 0 := by rw [← hsd0]; exact ha
              have hb0 : b.val < P.d0.getD la.val 0 := by rw [← hsd0]; exact hb
              rw [if_pos ⟨ha, hb⟩, if_pos ⟨hla, ha0, hb0⟩, phiPad_site P hl κ a' b' la a b ⟨hκ, ha', hb'⟩
                ⟨hla, ha0, hb0⟩, hA0 la hla p _ _ ha hb]
              rfl
            · rw [if_neg (fun h => hb h.2), if_neg (fun h => hb (by rw [hsd0]; exact h.2.2)), mul_zero]
          · rw [if_neg (fun h => ha h.1), if_neg (fun h => ha (by rw [hsd0]; exact h.2.1)), mul_zero]
        · rw [phiPad_site_zero P hl κ a' b' la a b (fun h => hla h.1), zero_mul, if_neg (fun h => hla h.1)]
      simp only [e]
      have hD : ∀ la < 4, P.d0.getD la 0 ≤ dpad l := by
        intro la hla
        have h := hle0 ⟨la, by omega⟩
        rw [hsd0] at h
        rw [hdl]
        exact h
      rw [sum_trunc3 (fun la => P.d0.getD la 0) hD (fun la a b =>
        (D1.phiE P (coord P.off1 P.d1 κ a' b') (coord P.off0 P.d0 la a b) : ℂ) / 192 * (sM 0 la p a b : ℂ))]
      have h192 : (192 : ℂ) ≠ 0 := by norm_num
      have hc : (192 : ℂ) * (sM 1 κ p a'.val b'.val : ℂ) = ∑ la ∈ Finset.range 4,
          ∑ a ∈ Finset.range (P.d0.getD la 0), ∑ b ∈ Finset.range (P.d0.getD la 0),
            (D1.phiE P (coord P.off1 P.d1 κ a' b') (coord P.off0 P.d0 la a b) : ℂ) * (sM 0 la p a b : ℂ) := by
        exact_mod_cast hB p κ hκ _ _ ha1 hb1
      apply mul_left_cancel₀ h192
      rw [hc]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun la _ => Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    · -- the output coordinate is not true: both sides vanish
      have h0 : ¬ (a'.val < sd1 κ ∧ b'.val < sd1 κ) := by
        intro h
        apply ht
        by_cases hκ : κ.val < 4
        · exact ⟨hκ, by rw [← hsd1]; exact h.1, by rw [← hsd1]; exact h.2⟩
        · have h4v : κ.val = 4 := by have := κ.isLt; omega
          have h1 := h.1
          rw [hsd1, h4v, h14] at h1
          exact absurd h1 (Nat.not_lt_zero _)
      rw [if_neg h0]
      symm
      refine Finset.sum_eq_zero fun la _ => Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
      rw [show phiPad P l κ a' b' la a b = 0 by
        simp only [phiPad, if_pos hl]
        rw [if_neg]
        exact fun h => ht h.1, zero_mul]
  refine (fourierAt_VG _ l p).2 fun κ => ?_
  ext a' b'
  exact key κ a' b'

end NPT.CP3
