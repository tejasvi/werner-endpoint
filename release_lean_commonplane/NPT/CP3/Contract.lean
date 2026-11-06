/-
NPT.CP3.Contract — the entries of the flat-tensor contractions of `NPT.CP3.D1Core` (the computational core of the
native data checks). A tensor of shape `(B, n, A)` is a flat array with entry `(b, x, a)` at `(b·n + x)·A + a`;
`contract` replaces the middle axis by its image under an `n' × n` matrix. `contract_spec` gives the entries, and
`lift4_spec` composes four contractions on the first four axes of a five-axis tensor.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import NPT.CP3.D1Core

namespace NPT.CP3.Ctr

lemma sumGo_eq (f : ℕ → ℤ) (k : ℕ) (acc : ℤ) : sumGo f k acc = acc + ∑ x ∈ Finset.range k, f x := by
  induction k generalizing acc with
  | zero => simp [sumGo]
  | succ k ih => rw [sumGo, ih, Finset.sum_range_succ]; ring

lemma sumRange_eq (n : ℕ) (f : ℕ → ℤ) : sumRange n f = ∑ x ∈ Finset.range n, f x := by
  rw [sumRange, sumGo_eq, zero_add]

lemma idx_lt {B n A b y a : ℕ} (hb : b < B) (hy : y < n) (ha : a < A) : (b * n + y) * A + a < B * n * A := by
  have h1 : b * n + y + 1 ≤ B * n := by
    have : (b + 1) * n ≤ B * n := Nat.mul_le_mul_right n hb
    nlinarith
  have h2 : (b * n + y) * A + a < (b * n + y + 1) * A := by nlinarith
  calc (b * n + y) * A + a < (b * n + y + 1) * A := h2
    _ ≤ B * n * A := Nat.mul_le_mul_right A h1

lemma idx2_lt {B n b y : ℕ} (hb : b < B) (hy : y < n) : b * n + y < B * n := by
  have : (b + 1) * n ≤ B * n := Nat.mul_le_mul_right n hb
  nlinarith

lemma idx_mod {n A b y a : ℕ} (ha : a < A) : ((b * n + y) * A + a) % A = a := by
  rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]

lemma idx_div {n A b y a : ℕ} (ha : a < A) : ((b * n + y) * A + a) / A = b * n + y := by
  have hA : 0 < A := by omega
  rw [add_comm, Nat.add_mul_div_right _ _ hA, Nat.div_eq_of_lt ha, zero_add]

lemma idx_y {n A b y a : ℕ} (hy : y < n) (ha : a < A) : ((b * n + y) * A + a) / A % n = y := by
  rw [idx_div ha, add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]

lemma idx_b {n A b y a : ℕ} (hy : y < n) (ha : a < A) : ((b * n + y) * A + a) / (n * A) = b := by
  have hn : 0 < n := by omega
  rw [mul_comm n A, ← Nat.div_div_eq_div_mul, idx_div ha, add_comm, Nat.add_mul_div_right _ _ hn,
    Nat.div_eq_of_lt hy, zero_add]

/-- **Entries of a contraction.** -/
theorem contract_spec (B n A n' : ℕ) (M : ℕ → ℕ → ℤ) (T : Array ℤ) {b y a : ℕ} (hb : b < B) (hy : y < n')
    (ha : a < A) :
    (contract B n A n' M T).getD ((b * n' + y) * A + a) 0 =
      ∑ x ∈ Finset.range n, M y x * T.getD ((b * n + x) * A + a) 0 := by
  have hi := idx_lt (n := n') hb hy ha
  unfold contract
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by rw [Array.size_ofFn]; exact hi), Option.getD_some,
    Array.getElem_ofFn]
  dsimp only
  rw [sumRange_eq]
  simp only [idx_y hy ha, idx_b hy ha, idx_mod ha]

/-- **Entries of the four-axis lift.** -/
theorem lift4_spec (n0 n1 n2 n3 n4 m0 m1 m2 m3 : ℕ) (M0 M1 M2 M3 : ℕ → ℕ → ℤ) (T : Array ℤ)
    {t0 t1 t2 t3 x4 : ℕ} (h0 : t0 < m0) (h1 : t1 < m1) (h2 : t2 < m2) (h3 : t3 < m3) (h4 : x4 < n4) :
    (lift4 n0 n1 n2 n3 n4 m0 m1 m2 m3 M0 M1 M2 M3 T).getD ((((t0 * m1 + t1) * m2 + t2) * m3 + t3) * n4 + x4) 0 =
      ∑ x3 ∈ Finset.range n3, M3 t3 x3 * ∑ x2 ∈ Finset.range n2, M2 t2 x2 * ∑ x1 ∈ Finset.range n1, M1 t1 x1 *
        ∑ x0 ∈ Finset.range n0, M0 t0 x0 * T.getD ((((x0 * n1 + x1) * n2 + x2) * n3 + x3) * n4 + x4) 0 := by
  dsimp only [lift4]
  have hb2 : t0 * m1 + t1 < m0 * m1 := idx2_lt h0 h1
  have hb3 : (t0 * m1 + t1) * m2 + t2 < m0 * m1 * m2 := idx2_lt hb2 h2
  rw [contract_spec _ _ _ _ _ _ hb3 h3 h4]
  refine Finset.sum_congr rfl fun x3 hx3 => ?_
  have hx3' : x3 < n3 := Finset.mem_range.1 hx3
  have e3 : (((t0 * m1 + t1) * m2 + t2) * n3 + x3) * n4 + x4 = ((t0 * m1 + t1) * m2 + t2) * (n3 * n4) + (x3 * n4 + x4) := by
    ring
  have ha3 : x3 * n4 + x4 < n3 * n4 := by
    have := idx_lt (B := n3) (n := n4) (A := 1) hx3' h4 Nat.one_pos
    simpa using this
  rw [e3, contract_spec _ _ _ _ _ _ hb2 h2 ha3]
  congr 1
  refine Finset.sum_congr rfl fun x2 hx2 => ?_
  have hx2' : x2 < n2 := Finset.mem_range.1 hx2
  have e2 : ((t0 * m1 + t1) * n2 + x2) * (n3 * n4) + (x3 * n4 + x4) =
      (t0 * m1 + t1) * (n2 * n3 * n4) + (x2 * (n3 * n4) + (x3 * n4 + x4)) := by ring
  have ha2 : x2 * (n3 * n4) + (x3 * n4 + x4) < n2 * n3 * n4 := by
    have := idx_lt (B := n2) (n := n3 * n4) (A := 1) hx2' ha3 Nat.one_pos
    simpa [mul_assoc] using this
  rw [e2, contract_spec _ _ _ _ _ _ h0 h1 ha2]
  congr 1
  refine Finset.sum_congr rfl fun x1 hx1 => ?_
  have hx1' : x1 < n1 := Finset.mem_range.1 hx1
  have e1 : (t0 * n1 + x1) * (n2 * n3 * n4) + (x2 * (n3 * n4) + (x3 * n4 + x4)) =
      (0 * m0 + t0) * (n1 * n2 * n3 * n4) + (x1 * (n2 * n3 * n4) + (x2 * (n3 * n4) + (x3 * n4 + x4))) := by ring
  have ha1 : x1 * (n2 * n3 * n4) + (x2 * (n3 * n4) + (x3 * n4 + x4)) < n1 * n2 * n3 * n4 := by
    have := idx_lt (B := n1) (n := n2 * n3 * n4) (A := 1) hx1' ha2 Nat.one_pos
    simpa [mul_assoc] using this
  rw [e1, contract_spec _ _ _ _ _ _ Nat.one_pos h0 ha1]
  congr 1
  refine Finset.sum_congr rfl fun x0 _ => ?_
  congr 2
  ring

end NPT.CP3.Ctr
