import NPT.CP3.Chk.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.List.Nodup

/-!
# NPT.CP3.Chk.Lemmas — generic facts about the list checkers

* `dot_eq_sum`: `dot` is the finite sum of products over the common length;
* `dot_map_zip`: `dot f (L.map h)` is the sum over `zip L f`;
* `sum_zip_lookup`: for distinct keys, a sum over a key–value list is a sum over its keys with the looked-up values;
* `ups_nodup`, `sum_ups`: the upper-triangle positions are distinct and enumerate `{(u, v) : u ≤ v < m}`;
* `upper_sym`: the weighted upper-triangle sum equals the full Frobenius sum of the symmetric matrix;
* `psd_of_complex`: a real matrix whose complexification is positive semidefinite is positive semidefinite.
-/

open Finset BigOperators Matrix
open scoped ComplexOrder

namespace NPT.CP3.Chk

theorem dot_nil_left (b : List Int) : dot [] b = 0 := by cases b <;> rfl

theorem dot_eq_sum : ∀ (a b : List Int) (n : ℕ), a.length = n → b.length = n →
    dot a b = ∑ t ∈ range n, a.getD t 0 * b.getD t 0
  | [], _, n, ha, _ => by
      subst ha; simp [dot_nil_left]
  | _ :: _, [], n, ha, hb => by
      simp at hb; subst hb; simp at ha
  | x :: xs, y :: ys, n, ha, hb => by
      cases n with
      | zero => simp at ha
      | succ n =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at ha hb
        rw [Finset.sum_range_succ', dot, dot_eq_sum xs ys n ha hb]
        simp [add_comm]

theorem lsum_eq_sum (l : List Int) : lsum l = l.sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [lsum, ih]

theorem dot_map_zip {α : Type*} (h : α → Int) : ∀ (f : List Int) (L : List α),
    dot f (L.map h) = ((L.zip f).map fun e => e.2 * h e.1).sum
  | [], L => by simp [dot_nil_left]
  | _ :: _, [] => by simp [dot]
  | x :: xs, a :: L => by
      simp [dot, dot_map_zip h xs L]

/-- Value of the first entry with key `q` (0 if none). -/
def lookupZ {α : Type*} [DecidableEq α] (E : List (α × Int)) (q : α) : Int :=
  ((E.find? fun e => decide (e.1 = q)).map Prod.snd).getD 0

theorem sum_zip_lookup {α : Type*} [DecidableEq α] (w : α → Int) : ∀ (E : List (α × Int)), (E.map Prod.fst).Nodup →
    (E.map fun e => e.2 * w e.1).sum = ((E.map Prod.fst).map fun q => lookupZ E q * w q).sum
  | [], _ => rfl
  | e :: E, hn => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn ⊢
      obtain ⟨hnot, hn⟩ := hn
      rw [List.sum_cons, List.sum_cons, sum_zip_lookup w E hn]
      congr 1
      · simp [lookupZ]
      · refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
        have hne : e.1 ≠ q := by
          intro h; apply hnot
          obtain ⟨e', he', rfl⟩ := List.mem_map.1 hq
          exact ⟨e', he', h.symm⟩
        simp [lookupZ, List.find?_cons, hne]

theorem ups_nodup (m : ℕ) : (ups m).Nodup := by
  unfold ups
  rw [List.nodup_flatMap]
  refine ⟨fun u _ => ?_, ?_⟩
  · exact (List.nodup_range).map fun a b h => by simpa using h
  · refine (List.nodup_range).imp fun {a b} hab => ?_
    simp only [Function.onFun]
    rw [List.disjoint_left]
    intro q hqa hqb
    simp only [List.mem_map, List.mem_range] at hqa hqb
    obtain ⟨_, _, rfl⟩ := hqa
    obtain ⟨_, _, h⟩ := hqb
    exact hab (congrArg Prod.fst h).symm

theorem sum_map_range_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ j ∈ range n, f j := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem sum_flatMap_range {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → List M) :
    ((List.range n).flatMap g).sum = ∑ u ∈ range n, (g u).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.flatMap_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem sum_ups {M : Type*} [AddCommMonoid M] (m : ℕ) (G : ℕ × ℕ → M) :
    ((ups m).map G).sum = ∑ u ∈ range m, ∑ v ∈ Ico u m, G (u, v) := by
  unfold ups
  rw [List.map_flatMap, sum_flatMap_range]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [List.map_map, sum_map_range_eq, Finset.sum_Ico_eq_sum_range]
  rfl

/-- The symmetric reading `S u v = L (min u v, max u v)` of an upper-triangle function `L`, against any `P`:
`Σ_{u ≤ v} L(u,v) W(u,v) = Σ_{u,v} S(u,v) P(u,v)` with `W(u,u) = P(u,u)`, `W(u,v) = P(u,v) + P(v,u)` for `u < v`. -/
theorem upper_sym {R : Type*} [CommRing R] (m : ℕ) (L : ℕ × ℕ → R) (P : ℕ → ℕ → R) :
    ∑ u ∈ range m, ∑ v ∈ Ico u m, L (u, v) * (if u = v then P u u else P u v + P v u) =
      ∑ u ∈ range m, ∑ v ∈ range m, L (min u v, max u v) * P u v := by
  have split : ∀ u v : ℕ, L (min u v, max u v) * P u v =
      (if u ≤ v then L (u, v) * P u v else 0) + (if v < u then L (v, u) * P u v else 0) := by
    intro u v
    rcases lt_trichotomy u v with h | h | h
    · simp [h, h.le, not_lt.2 h.le, min_eq_left h.le, max_eq_right h.le]
    · subst h; simp
    · simp [h, not_le.2 h, min_eq_right h.le, max_eq_left h.le]
  simp_rw [split, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun u v => if v < u then L (v, u) * P u v else 0)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [← Finset.sum_add_distrib]
  have hI : Ico u m = (range m).filter (fun v => u ≤ v) := by
    ext v; simp [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]; omega
  rw [hI, Finset.sum_filter]
  refine Finset.sum_congr rfl fun v _ => ?_
  rcases lt_trichotomy u v with h | h | h
  · have h1 : ¬ v < u := not_lt.2 h.le
    simp [h, h.le, h.ne, h1]; ring
  · subst h; simp
  · have h1 : ¬ u ≤ v := not_le.2 h
    have h2 : ¬ u < v := fun h' => lt_asymm h h'
    simp [h1, h2]

/-- A real matrix whose complexification is positive semidefinite is positive semidefinite. -/
theorem psd_of_complex {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℝ)
    (h : (A.map fun x : ℝ => (x : ℂ)).PosSemidef) : A.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    have := congrFun (congrFun h.isHermitian i) j
    simp only [conjTranspose_apply, map_apply, Complex.star_def, Complex.conj_ofReal] at this
    simpa [conjTranspose_apply] using (Complex.ofReal_injective this)
  · have hx := h.dotProduct_mulVec_nonneg (fun i => (x i : ℂ))
    have e : star (fun i => (x i : ℂ)) ⬝ᵥ ((A.map fun x : ℝ => (x : ℂ)) *ᵥ fun i => (x i : ℂ)) =
        ((star x ⬝ᵥ (A *ᵥ x) : ℝ) : ℂ) := by
      simp [dotProduct, mulVec, map_apply, Complex.ofReal_sum, Complex.ofReal_mul, Pi.star_apply]
    rw [e] at hx
    exact_mod_cast hx

end NPT.CP3.Chk
