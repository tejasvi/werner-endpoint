import NPT.CP3.D3Core
import NPT.CP3.Radix
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Rat.Cast.Order

/-!
# NPT.CP3.D3Lift — flat double sums against `G` with per-factor pair functionals are lifts of `t0Arr`

`flat_lift`: for integer site matrices `M_l` (rows `t_l < m_l`) and an aux function `g`,
`Σ_{a,b < n} G[a·n + b] · Π_{l<4} M_l(t_l, a_l d_l + b_l) · g(a_4 d_4 + b_4)` (digits `a_l = digit dims a l`) equals
`Σ_{x4} g x4 · lift4(t0Arr v G)[(t, x4)]`.
-/

open BigOperators Finset
open NPT.CP3.Ctr NPT.CP3.Data
open NPT.CP3.D1 (digit flat5 boxN sq t0Arr sum_pairs digit_flat5 digit_lt t0Arr_spec)

namespace NPT.CP3.D3

/-- Pair of digit `l` of `(a, b)`: `a_l d_l + b_l`. -/
def pr (d : List ℕ) (l a b : ℕ) : ℕ := digit d a l * d.getD l 1 + digit d b l

lemma div_mod_lt {x c : ℕ} (hc : 0 < c) (hx : x < c * c) : x / c < c ∧ x % c < c :=
  ⟨by rw [Nat.div_lt_iff_lt_mul hc]; exact hx, Nat.mod_lt _ hc⟩

/-- The two flat indices with digits `x_l / d_l` and `x_l % d_l`. -/
def fa (d : List ℕ) (x0 x1 x2 x3 x4 : ℕ) : ℕ :=
  flat5 d (x0 / d.getD 0 1) (x1 / d.getD 1 1) (x2 / d.getD 2 1) (x3 / d.getD 3 1) (x4 / d.getD 4 1)
def fb (d : List ℕ) (x0 x1 x2 x3 x4 : ℕ) : ℕ :=
  flat5 d (x0 % d.getD 0 1) (x1 % d.getD 1 1) (x2 % d.getD 2 1) (x3 % d.getD 3 1) (x4 % d.getD 4 1)

lemma pr_flat5 (d : List ℕ) (hpos : ∀ i < 5, 0 < d.getD i 1) {x0 x1 x2 x3 x4 : ℕ}
    (h0 : x0 < sq d 0) (h1 : x1 < sq d 1) (h2 : x2 < sq d 2) (h3 : x3 < sq d 3) (h4 : x4 < sq d 4) :
    pr d 0 (fa d x0 x1 x2 x3 x4) (fb d x0 x1 x2 x3 x4) = x0 ∧
      pr d 1 (fa d x0 x1 x2 x3 x4) (fb d x0 x1 x2 x3 x4) = x1 ∧
      pr d 2 (fa d x0 x1 x2 x3 x4) (fb d x0 x1 x2 x3 x4) = x2 ∧
      pr d 3 (fa d x0 x1 x2 x3 x4) (fb d x0 x1 x2 x3 x4) = x3 ∧
      pr d 4 (fa d x0 x1 x2 x3 x4) (fb d x0 x1 x2 x3 x4) = x4 := by
  obtain ⟨a0, b0⟩ := div_mod_lt (hpos 0 (by decide)) (by simpa [NPT.CP3.D1.sq] using h0)
  obtain ⟨a1, b1⟩ := div_mod_lt (hpos 1 (by decide)) (by simpa [NPT.CP3.D1.sq] using h1)
  obtain ⟨a2, b2⟩ := div_mod_lt (hpos 2 (by decide)) (by simpa [NPT.CP3.D1.sq] using h2)
  obtain ⟨a3, b3⟩ := div_mod_lt (hpos 3 (by decide)) (by simpa [NPT.CP3.D1.sq] using h3)
  obtain ⟨a4, b4⟩ := div_mod_lt (hpos 4 (by decide)) (by simpa [NPT.CP3.D1.sq] using h4)
  obtain ⟨da0, da1, da2, da3, da4⟩ := digit_flat5 d a0 a1 a2 a3 a4
  obtain ⟨db0, db1, db2, db3, db4⟩ := digit_flat5 d b0 b1 b2 b3 b4
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [pr, fa, fb, da0, da1, da2, da3, da4, db0, db1, db2, db3, db4, Nat.div_add_mod']

lemma pr_lt4 (d : List ℕ) (hpos : ∀ i < 5, 0 < d.getD i 1) (a b : ℕ) : pr d 4 a b < sq d 4 := by
  have l4 := hpos 4 (by decide)
  have da : digit d a 4 < d.getD 4 1 := by simpa using digit_lt d (p := a) 4 (by simpa using l4)
  have db : digit d b 4 < d.getD 4 1 := by simpa using digit_lt d (p := b) 4 (by simpa using l4)
  simp only [pr, NPT.CP3.D1.sq]
  have hm := Nat.mul_le_mul_right (d.getD 4 1) (Nat.succ_le_of_lt da)
  rw [Nat.succ_mul] at hm
  omega

/-- **Flat double sums as lifts.** -/
theorem flat_lift (v : VarB) (G : Array Int) (hpos : ∀ i < 5, 0 < v.dims.getD i 1)
    (m0 m1 m2 m3 : ℕ) (M0 M1 M2 M3 : ℕ → ℕ → ℤ) {t0 t1 t2 t3 : ℕ} (h0 : t0 < m0) (h1 : t1 < m1) (h2 : t2 < m2)
    (h3 : t3 < m3) (g : ℕ → ℚ) :
    ∑ a ∈ range (boxN v.dims), ∑ b ∈ range (boxN v.dims), (G.getD (a * boxN v.dims + b) 0 : ℚ) *
      ((M0 t0 (pr v.dims 0 a b) : ℚ) * (M1 t1 (pr v.dims 1 a b) : ℚ) * (M2 t2 (pr v.dims 2 a b) : ℚ) *
        (M3 t3 (pr v.dims 3 a b) : ℚ) * g (pr v.dims 4 a b)) =
    ∑ x4 ∈ range (sq v.dims 4), g x4 *
      ((lift4 (sq v.dims 0) (sq v.dims 1) (sq v.dims 2) (sq v.dims 3) (sq v.dims 4) m0 m1 m2 m3 M0 M1 M2 M3
        (t0Arr v G)).getD ((((t0 * m1 + t1) * m2 + t2) * m3 + t3) * sq v.dims 4 + x4) 0 : ℚ) := by
  set F : ℕ → ℕ → ℚ := fun a b => (G.getD (a * boxN v.dims + b) 0 : ℚ) *
    ((M0 t0 (pr v.dims 0 a b) : ℚ) * (M1 t1 (pr v.dims 1 a b) : ℚ) * (M2 t2 (pr v.dims 2 a b) : ℚ) *
      (M3 t3 (pr v.dims 3 a b) : ℚ) * g (pr v.dims 4 a b)) with hF
  have split : ∑ x4 ∈ range (sq v.dims 4), ∑ a ∈ range (boxN v.dims), ∑ b ∈ range (boxN v.dims),
      (if digit v.dims a 4 * v.dims.getD 4 1 + digit v.dims b 4 = x4 then F a b else 0) =
      ∑ a ∈ range (boxN v.dims), ∑ b ∈ range (boxN v.dims), F a b := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_ite_eq]
    exact if_pos (Finset.mem_range.2 (pr_lt4 v.dims hpos a b))
  show ∑ a ∈ range (boxN v.dims), ∑ b ∈ range (boxN v.dims), F a b = _
  rw [← split]
  refine Finset.sum_congr rfl fun x4 hx4 => ?_
  have hx4' : x4 < sq v.dims 4 := Finset.mem_range.1 hx4
  rw [sum_pairs v.dims hpos (by simpa [NPT.CP3.D1.sq] using hx4') F,
    lift4_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2 h3 hx4']
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x3 hx3 => Finset.sum_congr rfl fun x2 hx2 =>
    Finset.sum_congr rfl fun x1 hx1 => Finset.sum_congr rfl fun x0 hx0 => ?_
  have e0 : x0 < sq v.dims 0 := by simpa [NPT.CP3.D1.sq] using Finset.mem_range.1 hx0
  have e1 : x1 < sq v.dims 1 := by simpa [NPT.CP3.D1.sq] using Finset.mem_range.1 hx1
  have e2 : x2 < sq v.dims 2 := by simpa [NPT.CP3.D1.sq] using Finset.mem_range.1 hx2
  have e3 : x3 < sq v.dims 3 := by simpa [NPT.CP3.D1.sq] using Finset.mem_range.1 hx3
  obtain ⟨p0, p1, p2, p3, p4⟩ := pr_flat5 v.dims hpos e0 e1 e2 e3 hx4'
  simp only [fa, fb] at p0 p1 p2 p3 p4
  simp only [hF, p0, p1, p2, p3, p4]
  rw [t0Arr_spec v G e0 e1 e2 e3 hx4']
  ring

end NPT.CP3.D3
