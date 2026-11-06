import NPT.CP3.Chk.D0Defs
import Mathlib.Order.Interval.Finset.Nat

/-!
# NPT.CP3.Chk.Off — the coordinate ranges of the tuples

The 150 variable blocks own the consecutive coordinate ranges `[off v, off v + #S_v)`, from `0` to `1331`; the 25
skipped tuples (`v = 150..174`) have no basis matrices and `off = 1331`. `off_le` and `off_disjoint` state that the
ranges lie in `[0, 1331)` and are pairwise disjoint (kernel check `offOK`).
-/

namespace NPT.CP3.Chk

open NPT.CP3.Data

/-- The offsets are contiguous from `0` to `1331` over the variable blocks; the skipped tuples are empty at `1331`. -/
def offOK : Bool :=
  (List.range 149).all (fun v => (vb v).off + (vb v).S.length == (vb (v + 1)).off) && (vb 0).off == 0 &&
    (vb 149).off + (vb 149).S.length == 1331 &&
    (List.range' 150 25).all (fun v => (vb v).S.length == 0 && (vb v).off == 1331)

theorem offOK_true : offOK = true := by decide +kernel

theorem off_spec :
    (∀ v < 149, (vb v).off + (vb v).S.length = (vb (v + 1)).off) ∧ (vb 149).off + (vb 149).S.length = 1331 ∧
      ∀ v, 150 ≤ v → v < 175 → (vb v).S.length = 0 ∧ (vb v).off = 1331 := by
  have h := offOK_true
  simp only [offOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, List.mem_range', beq_iff_eq] at h
  obtain ⟨⟨⟨h1, -⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h3, fun v hv1 hv2 => ?_⟩
  exact h4 v ⟨v - 150, by omega, by omega⟩

theorem off_mono {v w : ℕ} (hvw : v < w) (hw : w ≤ 149) : (vb v).off + (vb v).S.length ≤ (vb w).off := by
  obtain ⟨h1, -, -⟩ := off_spec
  induction w with
  | zero => omega
  | succ w ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hvw with h | h
    · have := ih h (by omega)
      have e := h1 w (by omega)
      omega
    · subst h
      exact (h1 v (by omega)).le

theorem off_le : ∀ v < 175, (vb v).off + (vb v).S.length ≤ 1331 := by
  obtain ⟨-, h2, h3⟩ := off_spec
  intro v hv
  by_cases h : v < 150
  · rcases Nat.lt_or_ge v 149 with h' | h'
    · have := off_mono h' (le_refl 149)
      omega
    · have : v = 149 := by omega
      subst this
      omega
  · obtain ⟨e1, e2⟩ := h3 v (by omega) hv
    omega

theorem off_disjoint : ∀ v < 175, ∀ w < 175, v ≠ w →
    Disjoint (Finset.Ico (vb v).off ((vb v).off + (vb v).S.length))
      (Finset.Ico (vb w).off ((vb w).off + (vb w).S.length)) := by
  obtain ⟨-, -, h3⟩ := off_spec
  have key : ∀ v w, v < w → w < 175 → Disjoint (Finset.Ico (vb v).off ((vb v).off + (vb v).S.length))
      (Finset.Ico (vb w).off ((vb w).off + (vb w).S.length)) := by
    intro v w hvw hw
    by_cases hw' : w < 150
    · have := off_mono hvw (by omega)
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_Ico] at hx hx'
      omega
    · have := (h3 w (by omega) hw).1
      rw [this, Nat.add_zero, Finset.Ico_self]
      exact Finset.disjoint_empty_right _
  intro v hv w hw hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact key v w h hw
  · exact (key w v h hv).symm

end NPT.CP3.Chk
