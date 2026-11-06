/-
NPT.CP3.D1Bridge2 — the native D1 computation against the semantics of `NPT.CP3.Fsem` (part 2).

* `lift_eq_none`: without an auxiliary preimage the lift vanishes;
* `vtv_padR`: `Vᵀ H V` for a padded `V` as a flat double sum;
* `permE_pidx`: the coset permutations given as lists, as `Equiv.Perm (Fin 4)`.
-/
import NPT.CP3.D1Bridge

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem NPT.CP3.Ctr NPT.CP3.Data

namespace NPT.CP3.D1

open NPT.CP3

/-- **No auxiliary preimage: the lift vanishes.** -/
theorem lift_eq_none (P : PhiLists) {P0 P3 : PadData} {dims : Fin 5 → ℕ} {n : ℕ} (hB : BoxOK dims n)
    (hd : ∀ l : Fin 5, dims l ≤ dpad l) (hpos : ∀ l : Fin 5, 0 < dims l) (ρ τ : Fin 5 → Fin 5) (α β : MI)
    (X : Matrix (Fin n) (Fin n) ℂ) (ho : ∀ q : Fin 5, q.val < 4 → siteTrue P.d1 (ρ q).val (α q).val (β q).val)
    (hoa : auxTrue P.aD (ρ 4).val (α 4).val (β 4).val)
    (hτ : ∀ q : Fin 5, q.val < 4 → (τ q).val < 4 ∧ P.d0.getD (τ q).val 0 = dims q)
    (hτa : P.aD.getD (τ 4).val 0 = dims 4)
    (hnone : ∀ x < dims 4 * dims 4, P.aDest.getD (P.aOff.getD (τ 4).val 0 + x) 0 ≠
      coord P.aOff P.aD (ρ 4).val (α 4).val (β 4).val) :
    phiMap (F := P0.fam) (F' := P3.fam) (phiPad P) ρ τ (padRC dims X) α β = 0 := by
  rw [phiMap_flat P hB hd hpos ρ τ α β X ho hoa hτ]
  refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun s _ => ?_
  rw [if_neg]
  · ring
  · rintro ⟨-, h⟩
    have ht := unflat_lt dims hd hpos t 4
    have hs := unflat_lt dims hd hpos s 4
    have hn' := hnone _ (lt_of_rc ht hs)
    simp only [coord, hτa, Nat.add_assoc] at h hn'
    exact hn' h

/-- **`Vᵀ H V` for a padded `V`.** -/
lemma vtv_padR {dims : Fin 5 → ℕ} {n m : ℕ} (h : BoxOK dims n) (X : Matrix (Fin n) (Fin m) ℂ) (H : Matrix MI MI ℂ)
    (u w : Fin m) :
    ((padR dims X)ᵀ * H * padR dims X) u w =
      ∑ p : Fin n, ∑ q : Fin n, X p u * H (unflat dims p) (unflat dims q) * X q w := by
  rw [Matrix.mul_apply]
  have e1 : ∀ ν : MI, ((padR dims X)ᵀ * H) u ν * padR dims X ν w =
      match flatPos dims (n := n) ν with
      | some q => (∑ p : Fin n, X p u * H (unflat dims p) (unflat dims q)) * X q w
      | none => 0 := by
    intro ν
    cases hν : flatPos dims (n := n) ν with
    | none => simp [padR, hν]
    | some q =>
      have hq := flatPos_some h hν
      simp only [padR, hν]
      congr 1
      rw [Matrix.mul_apply]
      have e2 : ∀ μ : MI, (padR dims X)ᵀ u μ * H μ ν =
          match flatPos dims (n := n) μ with
          | some p => X p u * H (unflat dims p) (unflat dims q)
          | none => 0 := by
        intro μ
        cases hμ : flatPos dims (n := n) μ with
        | none => simp [padR, hμ, Matrix.transpose_apply]
        | some p =>
          simp only [Matrix.transpose_apply, padR, hμ]
          rw [flatPos_some h hμ, hq]
      rw [Finset.sum_congr rfl fun μ _ => e2 μ]
      exact sum_MI_flat h _
  rw [Finset.sum_congr rfl fun ν _ => e1 ν]
  refine (sum_MI_flat h _).trans ?_
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]

/-- `xInv` reports `n4` only when there is no preimage. -/
theorem xInv_none (R : Raw) (v : VarB) {e : ℕ} (he : e < 70) (hx : ¬ (xInv R v).getD e (sq v.dims 4) < sq v.dims 4) :
    ∀ x < sq v.dims 4, R.auxDest.getD (R.auxOff.getD v.ai 0 + x) 0 ≠ e := by
  intro x hx' h
  apply hx
  unfold xInv
  dsimp only
  rw [getD_ofFn _ _ he]
  dsimp only
  cases hf : (List.range (sq v.dims 4)).find? (fun y => R.auxDest.getD (R.auxOff.getD v.ai 0 + y) 0 == e) with
  | none =>
    rw [List.find?_eq_none] at hf
    exact absurd (by simpa using h) (hf x (List.mem_range.2 hx'))
  | some y =>
    have := List.mem_of_find?_eq_some hf
    simpa using List.mem_range.1 this

/-- Index of a permutation list in `permL`. -/
def pidx (s : List ℕ) : Fin 24 := Fin.ofNat 24 (permL.idxOf s)

lemma permE_pidx_tab : ∀ i : Fin 24, ∀ q : Fin 4,
    (permE (pidx (permL.getD i.val [])) q).val = (permL.getD i.val []).getD q.val 0 := by decide

lemma permE_pidx {s : List ℕ} (hs : s ∈ permL) (q : Fin 4) : (permE (pidx s) q).val = s.getD q.val 0 := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem.1 hs
  have hi' : i < 24 := by
    have h := hi.1
    have hl : permL.length = 24 := by decide
    omega
  obtain ⟨hlt, rfl⟩ := hi
  have e : permL[i] = permL.getD i [] := by simp [List.getD_eq_getElem?_getD, hlt]
  rw [e]
  exact permE_pidx_tab ⟨i, hi'⟩ q

/-- Digits of the padded flat index of an index in the box. -/
lemma digit_flatTrue (dims : Fin 5 → ℕ) (L : List ℕ) (hL : ∀ l : Fin 5, dims l = L.getD l.val 1) (μ : MI)
    (hμ : inBox dims μ) (l : Fin 5) : digit L (flatTrue dims μ) l.val = (μ l).val := by
  rw [flatTrue_eq dims L hL μ]
  have b : ∀ k : Fin 5, (μ k).val < L.getD k.val 1 := fun k => by rw [← hL k]; exact hμ k
  obtain ⟨e0, e1, e2, e3, e4⟩ := digit_flat5 L (b 0) (b 1) (b 2) (b 3) (b 4)
  fin_cases l
  · exact e0
  · exact e1
  · exact e2
  · exact e3
  · exact e4

end NPT.CP3.D1
