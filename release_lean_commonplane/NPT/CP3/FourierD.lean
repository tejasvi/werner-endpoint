/-
NPT.CP3.FourierD — the site Fourier facts of the certificate's lift `phiPad Pφ` between the padded module families
`PD 0` (cut `()`) and `PD 1` (cut `(3,)`), from two kernel checks on the site tables:
* `chkA`: `siteM[c][k][p]` is the site Gram form `Σ_z siteJ[c][k][z ∘ α][a] siteJ[c][k][z ∘ β][b]` at `VG 0 p`
  (`c = 0`) and `VG 8 p` (`c = 1`);
* `chkB`: `192 · siteM[1][κ][p] = Σ_λ phiNum[κ a' b', λ a b] · siteM[0][λ][p]`.
-/
import NPT.CP3.FourierSite
import NPT.CP3.FourierAux
import NPT.CP3.PDdef

open Matrix BigOperators Finset NPT.Cert NPT.Cert.Sem NPT.Brauer

namespace NPT.CP3.Inst

open NPT.CP3 NPT.CP3.Data NPT.CP3.Chk

/-- The lift data of the certificate. -/
def Pφ : PhiLists where
  phiNum := phiNum
  off0 := siteOff.getD 0 []
  off1 := siteOff.getD 1 []
  d0 := siteDims.getD 0 []
  d1 := siteDims.getD 1 []
  aOff := auxOff
  aD := auxDims
  aDest := auxDest

/-- Entry `(a, b)` of `siteM[c][k][p]`. -/
def sMd (c k : ℕ) (p : Fin 24) (a b : ℕ) : ℤ := mget (((siteM.getD c []).getD k []).getD p.val []) a b

/-- `sgN` as a structurally recursive sum (for the kernel). -/
def sgL (J : List (List Int)) (S : ℕ) (p : Fin 24) (a b : ℕ) : ℤ :=
  Ctr.sumRange 81 fun t => D1.lg J (Sem.flat (NPT.Cert.Ident.unflat 3 4 t ∘ aSel S p)) a *
    D1.lg J (Sem.flat (NPT.Cert.Ident.unflat 3 4 t ∘ bSel S p)) b

lemma sgN_eq_sgL (J : List (List Int)) (S : ℕ) (p : Fin 24) (a b : ℕ) : sgN J S p a b = sgL J S p a b := by
  rw [sgL, Ctr.sumRange_eq]
  rfl

/-- Check A: on the true entries of the labels `k < 4`, `siteM[c][k][p]` is the site Gram form of `siteJ[c][k]` at
`VG S p`. -/
def chkA (c S : ℕ) : Bool :=
  (List.range 4).all fun k => (List.finRange 24).all fun p =>
    (List.range (sdim c k)).all fun a => (List.range (sdim c k)).all fun b =>
      sgL ((siteJ.getD c []).getD k []) S p a b == sMd c k p a b

theorem chkA0 : chkA 0 0 = true := by decide +kernel

theorem chkA1 : chkA 1 8 = true := by decide +kernel

lemma chkA_sound {c S : ℕ} (h : chkA c S = true) (k : Fin 5) (hk : k.val < 4) (p : Fin 24) (a b : ℕ)
    (ha : a < sdim c k) (hb : b < sdim c k) :
    sgN ((siteJ.getD c []).getD k []) S p a b = sMd c k p a b := by
  have h1 := List.all_eq_true.1 h k.val (List.mem_range.2 hk)
  have h2 := List.all_eq_true.1 h1 p (List.mem_finRange p)
  have h3 := List.all_eq_true.1 h2 a (List.mem_range.2 ha)
  have h4 := List.all_eq_true.1 h3 b (List.mem_range.2 hb)
  rw [sgN_eq_sgL]
  exact beq_iff_eq.1 h4

/-- Check B: `192 · siteM[1][κ][p] = Σ_λ phiNum[κ a' b', λ a b] · siteM[0][λ][p]` on the true entries. -/
def chkB : Bool :=
  (List.finRange 24).all fun p => (List.range 4).all fun κ =>
    (List.range (sdim 1 κ)).all fun a' => (List.range (sdim 1 κ)).all fun b' =>
      192 * sMd 1 κ p a' b' == Ctr.sumRange 4 fun la => Ctr.sumRange (Pφ.d0.getD la 0) fun a =>
        Ctr.sumRange (Pφ.d0.getD la 0) fun b =>
          D1.phiE Pφ (coord Pφ.off1 Pφ.d1 κ a' b') (coord Pφ.off0 Pφ.d0 la a b) * sMd 0 la p a b

theorem chkB_ok : chkB = true := by decide +kernel

lemma chkB_sound (h : chkB = true) (p : Fin 24) (κ : Fin 5) (hκ : κ.val < 4) (a' b' : ℕ) (ha : a' < sdim 1 κ)
    (hb : b' < sdim 1 κ) :
    192 * sMd 1 κ p a' b' = ∑ la ∈ Finset.range 4, ∑ a ∈ Finset.range (Pφ.d0.getD la 0),
      ∑ b ∈ Finset.range (Pφ.d0.getD la 0),
        D1.phiE Pφ (coord Pφ.off1 Pφ.d1 κ a' b') (coord Pφ.off0 Pφ.d0 la a b) * sMd 0 la p a b := by
  have h1 := List.all_eq_true.1 h p (List.mem_finRange p)
  have h2 := List.all_eq_true.1 h1 κ.val (List.mem_range.2 hκ)
  have h3 := List.all_eq_true.1 h2 a' (List.mem_range.2 ha)
  have h4 := List.all_eq_true.1 h3 b' (List.mem_range.2 hb)
  rw [beq_iff_eq.1 h4]
  simp only [Ctr.sumRange_eq]

/-- **The site Fourier facts of the certificate's lift.** -/
theorem fourier_site : ∀ l : Fin 5, l.val < 4 → ∀ p : Fin 24,
    FourierAt (F := (PD 0).fam) (F' := (PD 1).fam) (phiPad Pφ) l (VG ℂ (nfC l) 0 p) :=
  fourierAt_site Pφ (PD 0) (PD 1) (fun k => (siteJ.getD 0 []).getD k.val [])
    (fun k => (siteJ.getD 1 []).getD k.val []) (fun k => sdim 0 k.val) (fun k => sdim 1 k.val)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) (fun _ => rfl) sdim_le (by decide) sMd
    (fun k hk p a b ha hb => chkA_sound chkA0 k hk p a b ha hb)
    (fun k hk p a b ha hb => chkA_sound chkA1 k hk p a b ha hb)
    (fun p κ hκ a' b' ha hb => chkB_sound chkB_ok p κ hκ a' b' ha hb)

/-! ### The auxiliary factor -/

theorem aux16_0 : ∀ k : Fin 5, ∀ j < (ablk 0 k.val).length, (ablk 0 k.val).getD j 0 < 16 := by decide +kernel

theorem aux16_1 : ∀ k : Fin 5, ∀ j < (ablk 1 k.val).length, (ablk 1 k.val).getD j 0 < 16 := by decide +kernel

theorem auxLen0 : ∀ k : Fin 5, (ablk 0 k.val).length = auxDims.getD k.val 0 := by decide +kernel

theorem auxLen1 : ∀ k : Fin 5, (ablk 1 k.val).length = auxDims.getD k.val 0 := by decide +kernel
/-- Every true cut-`()` coordinate sent to a true cut-`(3,)` coordinate carries its partially transposed strings
(Boolean check). -/
def auxStrB : Bool :=
  (List.range 5).all fun κ => (List.range (auxDims.getD κ 0)).all fun a' =>
    (List.range (auxDims.getD κ 0)).all fun b' => (List.range 5).all fun la =>
      (List.range (auxDims.getD la 0)).all fun a => (List.range (auxDims.getD la 0)).all fun b =>
        (auxDest.getD (coord auxOff auxDims la a b) 0 != coord auxOff auxDims κ a' b') ||
          (List.finRange 4).all fun s =>
            (NPT.Cert.Ident.unflat 2 4 ((ablk 0 la).getD a 0) s ==
              Function.update (NPT.Cert.Ident.unflat 2 4 ((ablk 1 κ).getD a' 0)) 3
                (NPT.Cert.Ident.unflat 2 4 ((ablk 1 κ).getD b' 0) 3) s) &&
            (NPT.Cert.Ident.unflat 2 4 ((ablk 0 la).getD b 0) s ==
              Function.update (NPT.Cert.Ident.unflat 2 4 ((ablk 1 κ).getD b' 0)) 3
                (NPT.Cert.Ident.unflat 2 4 ((ablk 1 κ).getD a' 0) 3) s)

theorem auxStrB_ok : auxStrB = true := by decide +kernel

theorem auxStr : ∀ κ : Fin 5, ∀ a' < auxDims.getD κ.val 0, ∀ b' < auxDims.getD κ.val 0, ∀ la : Fin 5,
    ∀ a < auxDims.getD la.val 0, ∀ b < auxDims.getD la.val 0,
    auxDest.getD (coord auxOff auxDims la.val a b) 0 = coord auxOff auxDims κ.val a' b' →
    (∀ s : Fin 4, NPT.Cert.Ident.unflat 2 4 ((ablk 0 la.val).getD a 0) s =
        Function.update (NPT.Cert.Ident.unflat 2 4 ((ablk 1 κ.val).getD a' 0)) 3
          (NPT.Cert.Ident.unflat 2 4 ((ablk 1 κ.val).getD b' 0) 3) s) ∧
      (∀ s : Fin 4, NPT.Cert.Ident.unflat 2 4 ((ablk 0 la.val).getD b 0) s =
        Function.update (NPT.Cert.Ident.unflat 2 4 ((ablk 1 κ.val).getD b' 0)) 3
          (NPT.Cert.Ident.unflat 2 4 ((ablk 1 κ.val).getD a' 0) 3) s) := by
  intro κ a' ha' b' hb' la a ha b hb hd
  have h1 := List.all_eq_true.1 auxStrB_ok κ.val (List.mem_range.2 κ.isLt)
  have h2 := List.all_eq_true.1 h1 a' (List.mem_range.2 ha')
  have h3 := List.all_eq_true.1 h2 b' (List.mem_range.2 hb')
  have h4 := List.all_eq_true.1 h3 la.val (List.mem_range.2 la.isLt)
  have h5 := List.all_eq_true.1 h4 a (List.mem_range.2 ha)
  have h6 := List.all_eq_true.1 h5 b (List.mem_range.2 hb)
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at h6
  rcases h6 with h | h
  · exact absurd hd h
  · have h7 := List.all_eq_true.1 h
    refine ⟨fun s => ?_, fun s => ?_⟩
    · have h8 := h7 s (List.mem_finRange s)
      simp only [Bool.and_eq_true, beq_iff_eq] at h8
      exact h8.1
    · have h8 := h7 s (List.mem_finRange s)
      simp only [Bool.and_eq_true, beq_iff_eq] at h8
      exact h8.2

/-- Exactly one true cut-`()` coordinate is sent to each true cut-`(3,)` coordinate. -/
theorem auxCnt : ∀ κ : Fin 5, ∀ a' < auxDims.getD κ.val 0, ∀ b' < auxDims.getD κ.val 0,
    (∑ la : Fin 5, ∑ a : Fin (dpad 4), ∑ b : Fin (dpad 4),
      if auxTrue auxDims la.val a.val b.val ∧
        auxDest.getD (coord auxOff auxDims la.val a.val b.val) 0 = coord auxOff auxDims κ.val a' b' then 1 else 0 : ℕ)
      = 1 := by decide +kernel

/-- **The auxiliary Fourier facts of the certificate's lift.** -/
theorem fourier_aux : ∀ X, FourierAt (F := (PD 0).fam) (F' := (PD 1).fam) (phiPad Pφ) 4 X :=
  fourierAt_aux Pφ (PD 0) (PD 1) (fun k => ablk 0 k.val) (fun k => ablk 1 k.val) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) aux16_0 aux16_1 auxLen0 auxLen1 auxStr auxCnt

end NPT.CP3.Inst
