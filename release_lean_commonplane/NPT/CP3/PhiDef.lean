/-
NPT.CP3.PhiDef — the padded Fourier data `Φ` of the lift from list data, and its site uniformity.

On a site factor, `Φ` at the cut-`(3,)` Gram coordinate `(κ, a', b')` and the cut-`()` coordinate `(λ, a, b)` is
`phiNum[off₁(κ) + a' d₁(κ) + b'][off₀(λ) + a d₀(λ) + b] / 192` when both coordinates are true (labels `< 4`, entries
within the module dimensions), and `0` otherwise. On the auxiliary factor it is `1` exactly when `auxDest` sends the
cut-`()` coordinate to the cut-`(3,)` one (both true), and `0` otherwise.
-/
import NPT.CP3.Orbit

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem NPT.Cert.SymAvg

namespace NPT.CP3

/-- The list data of the lift. -/
structure PhiLists where
  phiNum : List (List Int)
  off0 : List ℕ
  off1 : List ℕ
  d0 : List ℕ
  d1 : List ℕ
  aOff : List ℕ
  aD : List ℕ
  aDest : List ℕ

/-- True site coordinate `(κ, a, b)` of a cut with dimensions `d` (label `< 4`, entries `< d κ`). -/
def siteTrue (d : List ℕ) (κ a b : ℕ) : Prop := κ < 4 ∧ a < d.getD κ 0 ∧ b < d.getD κ 0

instance (d : List ℕ) (κ a b : ℕ) : Decidable (siteTrue d κ a b) := by unfold siteTrue; infer_instance

/-- True auxiliary coordinate `(κ, a, b)` (entries `< aD κ`). -/
def auxTrue (d : List ℕ) (κ a b : ℕ) : Prop := a < d.getD κ 0 ∧ b < d.getD κ 0

instance (d : List ℕ) (κ a b : ℕ) : Decidable (auxTrue d κ a b) := by unfold auxTrue; infer_instance

/-- Flat Gram coordinate `off κ + a d κ + b`. -/
def coord (off d : List ℕ) (κ a b : ℕ) : ℕ := off.getD κ 0 + a * d.getD κ 0 + b

/-- The padded Fourier data. -/
noncomputable def phiPad (P : PhiLists) :
    (l : Fin 5) → Fin 5 → Fin (dpad l) → Fin (dpad l) → Fin 5 → Fin (dpad l) → Fin (dpad l) → ℂ :=
  fun l κ a' b' la a b =>
    if l.val < 4 then
      if siteTrue P.d1 κ.val a'.val b'.val ∧ siteTrue P.d0 la.val a.val b.val then
        ((P.phiNum.getD (coord P.off1 P.d1 κ.val a'.val b'.val) []).getD (coord P.off0 P.d0 la.val a.val b.val) 0 : ℂ) /
          192
      else 0
    else
      if auxTrue P.aD κ.val a'.val b'.val ∧ auxTrue P.aD la.val a.val b.val ∧
          P.aDest.getD (coord P.aOff P.aD la.val a.val b.val) 0 = coord P.aOff P.aD κ.val a'.val b'.val then 1
      else 0

/-- **Site uniformity** of the padded Fourier data. -/
theorem phiPad_uniform (P : PhiLists) {P0 P3 : PadData} : PhiUniform (P0 := P0) (P3 := P3) (phiPad P) := by
  intro σ m κ a' b' la a b
  simp only [phiPad, Fin.coe_cast, sigHat_lt]

/-- `Φ` on a site at true coordinates. -/
lemma phiPad_site (P : PhiLists) {l : Fin 5} (hl : l.val < 4) (κ : Fin 5) (a' b' : Fin (dpad l)) (la : Fin 5)
    (a b : Fin (dpad l)) (h1 : siteTrue P.d1 κ.val a'.val b'.val) (h0 : siteTrue P.d0 la.val a.val b.val) :
    phiPad P l κ a' b' la a b =
      ((P.phiNum.getD (coord P.off1 P.d1 κ.val a'.val b'.val) []).getD (coord P.off0 P.d0 la.val a.val b.val) 0 : ℂ) /
        192 := by
  simp only [phiPad, if_pos hl, if_pos (And.intro h1 h0)]

/-- `Φ` on a site vanishes off the true input coordinates. -/
lemma phiPad_site_zero (P : PhiLists) {l : Fin 5} (hl : l.val < 4) (κ : Fin 5) (a' b' : Fin (dpad l)) (la : Fin 5)
    (a b : Fin (dpad l)) (h0 : ¬ siteTrue P.d0 la.val a.val b.val) : phiPad P l κ a' b' la a b = 0 := by
  simp only [phiPad, if_pos hl]
  rw [if_neg]
  exact fun h => h0 h.2

/-- `Φ` on the auxiliary factor at a true output coordinate. -/
lemma phiPad_aux (P : PhiLists) {l : Fin 5} (hl : ¬ l.val < 4) (κ : Fin 5) (a' b' : Fin (dpad l)) (la : Fin 5)
    (a b : Fin (dpad l)) (h1 : auxTrue P.aD κ.val a'.val b'.val) :
    phiPad P l κ a' b' la a b =
      if auxTrue P.aD la.val a.val b.val ∧
          P.aDest.getD (coord P.aOff P.aD la.val a.val b.val) 0 = coord P.aOff P.aD κ.val a'.val b'.val then 1
      else 0 := by
  simp only [phiPad, if_neg hl, h1, true_and]

end NPT.CP3
