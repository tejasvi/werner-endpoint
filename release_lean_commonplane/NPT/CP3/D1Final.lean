/-
NPT.CP3.D1Final — the D1 statements: the native check gives `F_k[i] = scale_k · Fsem_k[i]` for the block
coefficients recomputed from the module data.

* `fOutVJ`: the integer block coefficient of block `o` at the coordinate `(v, j)` (`fOut0` / `fOut3`);
* `scaleOf`: `1` for cut `()`, `192⁴` for cut `(3,)`;
* `fsemE`: the entry `(u, w)` of `Fsem_k[i] = fOutVJ / scale` at the coordinate `i` (variable found by `varOf`);
* `checkRange_sound`: a passed native range check gives `fData = fOutVJ` for every block and coordinate in the range.
-/
import NPT.CP3.D1Glue

open Matrix BigOperators Finset NPT.CP3.Ctr NPT.CP3.Data

namespace NPT.CP3.D1

/-- The integer block coefficient of block `o` at the coordinate `(v, j)`. -/
def fOutVJ (R : Raw) (v : VarB) (j : ℕ) (o : OutB) : List (List Int) :=
  if o.cut = 0 then fOut0 v (gArr v j) o
  else fOut3 R v (t4Arr R (flatOf R.phiNum 23 23) v (t0Arr v (gArr v j))) (xInv R v) o

/-- The scale of a block: `1` for cut `()`, `192⁴` for cut `(3,)`. -/
def scaleOf (o : OutB) : ℚ := if o.cut = 0 then 1 else 192 ^ 4

/-- Entry `(u, w)` of `Fsem_k[i]` (the variable of `i` found by `varOf`). -/
def fsemE (R : Raw) (k i u w : ℕ) : ℚ :=
  match varOf R i with
  | some (v, j) => (lg (fOutVJ R v j (R.outs.getD k default)) u w : ℚ) / scaleOf (R.outs.getD k default)
  | none => 0

lemma scaleOf_pos (o : OutB) : 0 < scaleOf o := by
  unfold scaleOf; split_ifs <;> norm_num

/-- **A passed native check at coordinate `i`.** -/
theorem checkCoord_sound (R : Raw) {i : ℕ} (h : checkCoord R (flatOf R.phiNum 23 23) R.outs.toArray i = true)
    {v : VarB} {j : ℕ} (hv : varOf R i = some (v, j)) {k : ℕ} (hk : k < R.outs.length) :
    fOutVJ R v j (R.outs.getD k default) = fData R (R.Fc.getD i []) k (R.outs.getD k default) := by
  unfold checkCoord at h
  rw [hv] at h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have h' := h k (by rw [List.size_toArray]; exact hk)
  rw [toArray_getD] at h'
  unfold fOutVJ
  exact h'

/-- **A passed native range check.** -/
theorem checkRange_sound (R : Raw) {a b : ℕ} (h : checkRange R a b = true) {i : ℕ} (hi1 : a ≤ i) (hi2 : i < b)
    {v : VarB} {j : ℕ} (hv : varOf R i = some (v, j)) {k : ℕ} (hk : k < R.outs.length) :
    fOutVJ R v j (R.outs.getD k default) = fData R (R.Fc.getD i []) k (R.outs.getD k default) := by
  unfold checkRange at h
  simp only [List.all_eq_true, List.mem_range'_1] at h
  exact checkCoord_sound R (h i ⟨hi1, by omega⟩) hv hk

/-- **D1, entrywise:** the data coefficient is the scale times `Fsem`. -/
theorem d1_entry (R : Raw) {a b : ℕ} (h : checkRange R a b = true) {i : ℕ} (hi1 : a ≤ i) (hi2 : i < b)
    {v : VarB} {j : ℕ} (hv : varOf R i = some (v, j)) {k : ℕ} (hk : k < R.outs.length) (u w : ℕ) :
    (lg (fData R (R.Fc.getD i []) k (R.outs.getD k default)) u w : ℚ) =
      scaleOf (R.outs.getD k default) * fsemE R k i u w := by
  rw [← checkRange_sound R h hi1 hi2 hv hk]
  unfold fsemE
  rw [hv]
  dsimp only
  field_simp [(scaleOf_pos _).ne']

end NPT.CP3.D1
