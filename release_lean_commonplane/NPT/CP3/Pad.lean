/-
NPT.CP3.Pad — padded matrices from flat list data, and the bridge between sums over the padded Gram index `MI` and sums
over flat true-dimension indices.

The data (lists) index Gram coordinates of a tuple flatly over its TRUE dimensions `dims` (`Sem.flatMI` order: factor 0
most significant, the auxiliary factor last). The semantics uses the padded index `MI` (3 per site, 6 for the auxiliary
factor). `flatTrue`/`unflat` convert, `inBox dims μ` says that `μ` lies within the true dimensions, and `sum_box`
reindexes a padded sum as a flat sum, given the two finite facts `box_ok` (decided per `dims`).
-/
import NPT.CP3.Site

open Matrix BigOperators Finset

namespace NPT.CP3

/-- Place value of factor `l` in the mixed radix `dims`. -/
def placeVal (dims : Fin 5 → ℕ) (l : Fin 5) : ℕ := ∏ l' : Fin 5, (if l.val < l'.val then dims l' else 1)

/-- Flat index over the true dimensions (as `Sem.flatMI`). -/
def flatTrue (dims : Fin 5 → ℕ) (μ : MI) : ℕ := ∑ l : Fin 5, (μ l : ℕ) * placeVal dims l

/-- `μ` lies within the true dimensions. -/
def inBox (dims : Fin 5 → ℕ) (μ : MI) : Prop := ∀ l, (μ l : ℕ) < dims l

instance (dims : Fin 5 → ℕ) : DecidablePred (inBox dims) := fun μ => by unfold inBox; infer_instance

lemma dpad_pos (l : Fin 5) : 0 < dpad l := by unfold dpad; split_ifs <;> omega

/-- Digits of a flat index (clamped to `0` where a digit does not fit `dpad`). -/
def unflat (dims : Fin 5 → ℕ) (t : ℕ) : MI := fun l =>
  if h : t / placeVal dims l % dims l < dpad l then ⟨t / placeVal dims l % dims l, h⟩ else ⟨0, dpad_pos l⟩

/-- The two finite facts that make `flatTrue` a bijection from the box onto `range N` (decided per `dims`). -/
def BoxOK (dims : Fin 5 → ℕ) (N : ℕ) : Prop :=
  (∀ μ : MI, inBox dims μ → flatTrue dims μ < N ∧ unflat dims (flatTrue dims μ) = μ) ∧
    (∀ t < N, inBox dims (unflat dims t) ∧ flatTrue dims (unflat dims t) = t)

instance (dims : Fin 5 → ℕ) (N : ℕ) : Decidable (BoxOK dims N) := by unfold BoxOK; infer_instance

/-- **Box reindexing.** -/
lemma sum_box {dims : Fin 5 → ℕ} {N : ℕ} (h : BoxOK dims N) (f : ℕ → ℂ) :
    ∑ μ : MI, (if inBox dims μ then f (flatTrue dims μ) else 0) = ∑ t ∈ Finset.range N, f t := by
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (flatTrue dims) (unflat dims) (fun μ hμ => ?_) (fun t ht => ?_) (fun μ hμ => ?_)
    (fun t ht => ?_) (fun _ _ => rfl)
  · exact Finset.mem_range.2 (h.1 μ (Finset.mem_filter.1 hμ).2).1
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (h.2 t (Finset.mem_range.1 ht)).1⟩
  · exact (h.1 μ (Finset.mem_filter.1 hμ).2).2
  · exact (h.2 t (Finset.mem_range.1 ht)).2

/-- Integer list entry as a complex number. -/
def lget (rows : List (List ℤ)) (t j : ℕ) : ℂ := (((rows.getD t []).getD j 0 : ℤ) : ℂ)

/-- Padded matrix whose rows are given flatly (row `μ` = list row `flatTrue μ` inside the box, `0` outside),
divided by `den`. -/
noncomputable def padRows (dims : Fin 5 → ℕ) (rows : List (List ℤ)) (den : ℕ) (m : ℕ) : Matrix MI (Fin m) ℂ :=
  fun μ j => if inBox dims μ then lget rows (flatTrue dims μ) j.val / den else 0

/-- Padded matrix whose columns are given flatly (`(m × n)` list, column `μ` = list column `flatTrue μ`). -/
noncomputable def padCols (dims : Fin 5 → ℕ) (rows : List (List ℤ)) (den : ℕ) (m : ℕ) : Matrix (Fin m) MI ℂ :=
  fun j μ => if inBox dims μ then lget rows j.val (flatTrue dims μ) / den else 0

/-- Product of a padded-columns and a padded-rows matrix is the flat list product. -/
lemma padCols_mul_padRows {dims : Fin 5 → ℕ} {N : ℕ} (h : BoxOK dims N) (L R : List (List ℤ)) (dL dR : ℕ)
    {m m' : ℕ} (j : Fin m) (k : Fin m') :
    (padCols dims L dL m * padRows dims R dR m') j k =
      ∑ t ∈ Finset.range N, lget L j.val t / dL * (lget R t k.val / dR) := by
  rw [Matrix.mul_apply, ← sum_box h]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [padCols, padRows]
  split_ifs <;> simp

end NPT.CP3
