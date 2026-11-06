/-
NPT.CP3.D2B — the averaged representation `Pav` of a tuple (padded, `Bos.lean`) is the padding of the flat averaged
representation `Sem.Pflat` of the data, given the box facts and the consistency of the tuple's dimensions with its
module labels (`DimsOK`, decided per tuple). With `d2_ok` this gives the bosonic-range hypothesis of `TupleData`.
-/
import NPT.CP3.PDdef
import NPT.CP3.PadB
import NPT.CP3.Inst
import Mathlib.Data.List.GetD

open Matrix BigOperators Finset NPT.Brauer NPT.Cert

namespace NPT.CP3.Inst

open NPT.CP3 NPT.CP3.Data NPT.CP3.Chk NPT.CP3.Sem

/-- Consistency of the dimensions of tuple `v` with its labels (decided per tuple). -/
def DimsOK (v : ℕ) : Prop :=
  (vb v).dims.length = 5 ∧ (∀ l < 4, (vb v).st.getD l 0 < 4) ∧ (vb v).ai < 5 ∧
  (∀ l < 4, (vb v).dims.getD l 0 = sdim 0 ((vb v).st.getD l 0)) ∧
  (vb v).dims.getD 4 0 = (ablk 0 (vb v).ai).length ∧
  (∀ l : Fin 5, placeValL (vb v).dims l = placeVal (dimsF v) l)

instance (v : ℕ) : Decidable (DimsOK v) := by unfold DimsOK; infer_instance

lemma dimsF_le (v : ℕ) (hd : DimsOK v) (l : Fin 5) : dimsF v l ≤ dpad l := by
  unfold dimsF dpad
  by_cases h : l.val < 4
  · rw [if_pos h, hd.2.2.2.1 l h]; exact sdim_le ⟨(vb v).st.getD l 0, by have := hd.2.1 l h; omega⟩
  · have hl : l.val = 4 := by omega
    rw [if_neg h, hl, hd.2.2.2.2.1]; exact ablk_le ⟨(vb v).ai, hd.2.2.1⟩

/-- Digits of a flat index of the box. -/
lemma digL_flat (v : ℕ) (hb : BoxOK (dimsF v) (nV v)) (hd : DimsOK v) {μ : MI} (hμ : inBox (dimsF v) μ) (l : Fin 5) :
    digL (vb v).dims l (flatTrue (dimsF v) μ) = (μ l : ℕ) := by
  have hu := (hb.1 μ hμ).2
  have hpos : 0 < dimsF v l := lt_of_le_of_lt (Nat.zero_le _) (hμ l)
  have hlt : flatTrue (dimsF v) μ / placeVal (dimsF v) l % dimsF v l < dpad l :=
    lt_of_lt_of_le (Nat.mod_lt _ hpos) (dimsF_le v hd l)
  have hcomp := congrArg (fun ν : MI => (ν l : ℕ)) hu
  simp only [unflat, dif_pos hlt] at hcomp
  unfold digL
  rw [hd.2.2.2.2.2 l]
  have hget : (vb v).dims.getD l.val 1 = dimsF v l := by
    unfold dimsF
    have hlen : l.val < (vb v).dims.length := by rw [hd.1]; exact l.isLt
    rw [List.getD_eq_getElem _ _ hlen, List.getD_eq_getElem _ _ hlen]
  rw [hget]
  exact hcomp

lemma tupF_val (v : ℕ) (hd : DimsOK v) (l : Fin 5) : (tupF v l).val = tauV v l := by
  unfold tupF tauV
  by_cases h : l.val < 4
  · simp only [if_pos h]
    exact Nat.mod_eq_of_lt (lt_trans (hd.2.1 l h) (by norm_num))
  · simp only [if_neg h]
    exact Nat.mod_eq_of_lt hd.2.2.1

/-- The padded intertwiner inside the true dimensions is the data entry. -/
lemma πp_in (v : ℕ) (hd : DimsOK v) (l : Fin 5) (g : Fin 24) (a b : Fin (dpad l)) (ha : a.val < dimsF v l)
    (hb' : b.val < dimsF v l) : πp l (tupF v l) g a b = ((piflI l (tauV v l) g a b : ℤ) : ℂ) := by
  unfold πp
  by_cases h : l.val < 4
  · rw [dif_pos h]
    unfold πsite
    have hk : sdim 0 (tupF v l) = dimsF v l := by
      unfold dimsF; rw [hd.2.2.2.1 l h, tupF_val v hd l]; unfold tauV; rw [if_pos h]
    rw [hk, if_pos ⟨by simpa using ha, by simpa using hb'⟩]
    unfold piflI
    rw [if_pos h, tupF_val v hd l]
    rfl
  · rw [dif_neg h]
    unfold πaux
    have hl : l.val = 4 := by omega
    have hk : (ablk 0 (tupF v l)).length = dimsF v l := by
      unfold dimsF; rw [hl, hd.2.2.2.2.1, tupF_val v hd l]; unfold tauV; rw [if_neg (by omega)]
    rw [hk, if_pos ⟨by simpa using ha, by simpa using hb'⟩]
    unfold piflI
    rw [if_neg h, tupF_val v hd l]
    rfl

/-- The padded intertwiner vanishes in rows beyond the true dimension. -/
lemma πp_out (v : ℕ) (hd : DimsOK v) (l : Fin 5) (g : Fin 24) (a b : Fin (dpad l)) (ha : ¬ a.val < dimsF v l) :
    πp l (tupF v l) g a b = 0 := by
  unfold πp
  by_cases h : l.val < 4
  · rw [dif_pos h]
    unfold πsite
    have hk : sdim 0 (tupF v l) = dimsF v l := by
      unfold dimsF; rw [hd.2.2.2.1 l h, tupF_val v hd l]; unfold tauV; rw [if_pos h]
    rw [hk, if_neg (fun h' => ha (by simpa using h'.1))]
  · rw [dif_neg h]
    unfold πaux
    have hl : l.val = 4 := by omega
    have hk : (ablk 0 (tupF v l)).length = dimsF v l := by
      unfold dimsF; rw [hl, hd.2.2.2.2.1, tupF_val v hd l]; unfold tauV; rw [if_neg (by omega)]
    rw [hk, if_neg (fun h' => ha (by simpa using h'.1))]

/-- The padded intertwiner vanishes in columns beyond the true dimension. -/
lemma πp_out' (v : ℕ) (hd : DimsOK v) (l : Fin 5) (g : Fin 24) (a b : Fin (dpad l)) (hb' : ¬ b.val < dimsF v l) :
    πp l (tupF v l) g a b = 0 := by
  unfold πp
  by_cases h : l.val < 4
  · rw [dif_pos h]
    unfold πsite
    have hk : sdim 0 (tupF v l) = dimsF v l := by
      unfold dimsF; rw [hd.2.2.2.1 l h, tupF_val v hd l]; unfold tauV; rw [if_pos h]
    rw [hk, if_neg (fun h' => hb' (by simpa using h'.2))]
  · rw [dif_neg h]
    unfold πaux
    have hl : l.val = 4 := by omega
    have hk : (ablk 0 (tupF v l)).length = dimsF v l := by
      unfold dimsF; rw [hl, hd.2.2.2.2.1, tupF_val v hd l]; unfold tauV; rw [if_neg (by omega)]
    rw [hk, if_neg (fun h' => hb' (by simpa using h'.2))]

/-- **`Pav` is the padded `Pflat`.** -/
theorem Pav_eq_padRC (v : ℕ) (hb : BoxOK (dimsF v) (nV v)) (hd : DimsOK v) :
    Pav πp (tupF v) = padRC (dimsF v) (n := nV v) (cq' (Pflat v)) := by
  ext μ ν
  simp only [Pav, Rep, Matrix.smul_apply, Matrix.sum_apply, kronR, smul_eq_mul]
  unfold padRC flatPos
  by_cases hμ : inBox (dimsF v) μ
  · by_cases hν : inBox (dimsF v) ν
    · have htμ := (hb.1 μ hμ).1
      have htν := (hb.1 ν hν).1
      rw [dif_pos ⟨hμ, htμ⟩, dif_pos ⟨hν, htν⟩]
      simp only [cq', Matrix.map_apply, Pflat]
      have e : ∀ g : Fin 24, ∏ l : Fin 5, πp l (tupF v l) g (μ l) (ν l) =
          ((∏ l ∈ range 5, (piflI l (tauV v l) g (digL (vb v).dims l (flatTrue (dimsF v) μ))
            (digL (vb v).dims l (flatTrue (dimsF v) ν)) : ℚ) : ℚ) : ℂ) := by
        intro g
        rw [← Fin.prod_univ_eq_prod_range]
        push_cast
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [πp_in v hd l g (μ l) (ν l) (hμ l) (hν l), digL_flat v hb hd hμ l, digL_flat v hb hd hν l]
      simp only [e]
      rw [← Fin.sum_univ_eq_sum_range]
      push_cast
      ring
    · rw [dif_pos ⟨hμ, (hb.1 μ hμ).1⟩, dif_neg (fun h => hν h.1)]
      simp only
      obtain ⟨l, hl⟩ : ∃ l, ¬ (ν l).val < dimsF v l := by
        by_contra h; push_neg at h; exact hν h
      refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun g _ => Finset.prod_eq_zero (Finset.mem_univ l) ?_)
      exact πp_out' v hd l g (μ l) (ν l) hl
  · rw [dif_neg (fun h => hμ h.1)]
    simp only
    obtain ⟨l, hl⟩ : ∃ l, ¬ (μ l).val < dimsF v l := by
      by_contra h; push_neg at h; exact hμ h
    refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun g _ => Finset.prod_eq_zero (Finset.mem_univ l) ?_)
    exact πp_out v hd l g (μ l) (ν l) hl

end NPT.CP3.Inst
