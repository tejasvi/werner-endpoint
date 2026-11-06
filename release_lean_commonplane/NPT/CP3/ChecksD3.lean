import NPT.CP3.D3Bridge
import NPT.CP3.Chk.D3N

/-!
# NPT.CP3.ChecksD3 — check D3: the objective coordinates and the used equality rows in the coordinate functionals

`d3_all` is the integer check of `NPT.CP3.D3Core` for every tuple (from the native run `d3_native` and
`d3Range_eq`); `d3_obj` and `d3_E` are the statements of `NPT.CP3.D3Def` (via `d3_obj_of`, `d3_E_of`).
-/

open NPT.CP3.Data

namespace NPT.CP3.D3

theorem d3_all : ∀ v < 175, d3OK v = true := by
  have h := NPT.CP3.D3F.d3_native
  rw [NPT.CP3.D3F.d3Range_eq] at h
  exact NPT.CP3.Chk.forall_of_range' h

end NPT.CP3.D3

namespace NPT.CP3.Inst

open NPT.CP3 NPT.CP3.Chk NPT.CP3.Sem

/-- **D3, objective**: the coordinate functionals of the objective are the certificate's `(ca, cb, 2 cab)`. -/
theorem d3_obj : ∀ k < 3, ∀ v < 175, ∀ j < (vb v).S.length,
    cobjFlat k v j = 16 * 162 ^ 4 * (tN k ((vb v).off + j) : ℚ) / cDen :=
  NPT.CP3.D3.d3_obj_of NPT.CP3.D3.d3_all

/-- **D3, equality rows**: the coordinate functionals of the 146 used rows are the certificate's `E` columns. -/
theorem d3_E : ∀ e < 146, ∀ v < 175, ∀ j < (vb v).S.length,
    (((Ecol.getD ((vb v).off + j) []).getD e 0 : ℤ) : ℚ) = 192 ^ 4 * cEFlat e v j :=
  NPT.CP3.D3.d3_E_of NPT.CP3.D3.d3_all

end NPT.CP3.Inst
