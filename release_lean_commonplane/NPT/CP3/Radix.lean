/-
NPT.CP3.Radix — mixed-radix facts for the five-factor flat indices of `NPT.CP3.D1Core` (`flat5`, `digit`), and the
reindexing of a double sum over flat indices `(t, s)` as the nested sum over the per-factor pairs
`x_q = digit t q · d_q + digit s q` that the native lift uses.
-/
import NPT.CP3.D1Spec
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

open NPT.CP3.Ctr NPT.CP3.Data

namespace NPT.CP3.D1

variable (L : List ℕ)

/-- Mixed-radix decoding of `flat5`. -/
theorem digit_flat5 {a0 a1 a2 a3 a4 : ℕ} (h0 : a0 < L.getD 0 1) (h1 : a1 < L.getD 1 1) (h2 : a2 < L.getD 2 1)
    (h3 : a3 < L.getD 3 1) (h4 : a4 < L.getD 4 1) :
    digit L (flat5 L a0 a1 a2 a3 a4) 0 = a0 ∧ digit L (flat5 L a0 a1 a2 a3 a4) 1 = a1 ∧
      digit L (flat5 L a0 a1 a2 a3 a4) 2 = a2 ∧ digit L (flat5 L a0 a1 a2 a3 a4) 3 = a3 ∧
      digit L (flat5 L a0 a1 a2 a3 a4) 4 = a4 := by
  obtain ⟨e0, e1, e2, e3, e4⟩ := decode5 (x0 := a0) h1 h2 h3 h4
  simp only [digit, flat5]
  refine ⟨?_, ?_, ?_, ?_, e4⟩
  · rw [show L.getD 1 1 * L.getD 2 1 * L.getD 3 1 * L.getD 4 1 = L.getD 4 1 * L.getD 3 1 * L.getD 2 1 * L.getD 1 1 by
      ring, e0, Nat.mod_eq_of_lt h0]
  · rw [show L.getD 2 1 * L.getD 3 1 * L.getD 4 1 = L.getD 4 1 * L.getD 3 1 * L.getD 2 1 by ring, e1]
  · rw [show L.getD 3 1 * L.getD 4 1 = L.getD 4 1 * L.getD 3 1 by ring, e2]
  · exact e3

/-- Mixed-radix reconstruction. -/
theorem flat5_digit {t : ℕ} (ht : t < boxN L) :
    flat5 L (digit L t 0) (digit L t 1) (digit L t 2) (digit L t 3) (digit L t 4) = t := by
  simp only [flat5, digit, boxN] at ht ⊢
  set L0 := L.getD 0 1
  set L1 := L.getD 1 1
  set L2 := L.getD 2 1
  set L3 := L.getD 3 1
  set L4 := L.getD 4 1
  have hprod : L0 * L1 * L2 * L3 * L4 = L0 * (L1 * L2 * L3 * L4) := by ring
  have hpos : 0 < L1 * L2 * L3 * L4 := by
    rcases Nat.eq_zero_or_pos (L1 * L2 * L3 * L4) with h | h
    · rw [hprod, h, mul_zero] at ht
      exact absurd ht (Nat.not_lt_zero _)
    · exact h
  have hq : t / (L1 * L2 * L3 * L4) < L0 := by
    rw [Nat.div_lt_iff_lt_mul hpos]
    rw [hprod] at ht
    exact ht
  rw [Nat.mod_eq_of_lt hq]
  have d1 : t / (L1 * L2 * L3 * L4) = t / L4 / L3 / L2 / L1 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]; ring_nf
  have d2 : t / (L2 * L3 * L4) = t / L4 / L3 / L2 := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]; ring_nf
  have d3 : t / (L3 * L4) = t / L4 / L3 := by rw [Nat.div_div_eq_div_mul]; ring_nf
  rw [d1, d2, d3, Nat.div_add_mod', Nat.div_add_mod', Nat.div_add_mod', Nat.div_add_mod']

lemma digit_lt {p : ℕ} (l : ℕ) (hl : 0 < L.getD (min l 4) 1) :
    digit L p l < L.getD (min l 4) 1 := by
  match l with
  | 0 => simp only [digit]; exact Nat.mod_lt _ hl
  | 1 => simp only [digit]; exact Nat.mod_lt _ hl
  | 2 => simp only [digit]; exact Nat.mod_lt _ hl
  | 3 => simp only [digit]; exact Nat.mod_lt _ hl
  | l + 4 => simp only [digit] at hl ⊢; simpa using Nat.mod_lt p (by simpa using hl)

lemma flat5_lt {a0 a1 a2 a3 a4 : ℕ} (h0 : a0 < L.getD 0 1) (h1 : a1 < L.getD 1 1) (h2 : a2 < L.getD 2 1)
    (h3 : a3 < L.getD 3 1) (h4 : a4 < L.getD 4 1) : flat5 L a0 a1 a2 a3 a4 < boxN L := by
  simp only [flat5, boxN]
  exact lt5 h0 h1 h2 h3 h4

/-- **Reindexing a flat double sum by per-factor pairs** (the auxiliary pair fixed to `x4`). -/
theorem sum_pairs {M : Type*} [AddCommMonoid M] (hL : ∀ i < 5, 0 < L.getD i 1) {x4 : ℕ}
    (hx4 : x4 < L.getD 4 1 * L.getD 4 1) (F : ℕ → ℕ → M) :
    ∑ t ∈ Finset.range (boxN L), ∑ s ∈ Finset.range (boxN L),
      (if digit L t 4 * L.getD 4 1 + digit L s 4 = x4 then F t s else 0) =
    ∑ x3 ∈ Finset.range (L.getD 3 1 * L.getD 3 1), ∑ x2 ∈ Finset.range (L.getD 2 1 * L.getD 2 1),
      ∑ x1 ∈ Finset.range (L.getD 1 1 * L.getD 1 1), ∑ x0 ∈ Finset.range (L.getD 0 1 * L.getD 0 1),
        F (flat5 L (x0 / L.getD 0 1) (x1 / L.getD 1 1) (x2 / L.getD 2 1) (x3 / L.getD 3 1) (x4 / L.getD 4 1))
          (flat5 L (x0 % L.getD 0 1) (x1 % L.getD 1 1) (x2 % L.getD 2 1) (x3 % L.getD 3 1) (x4 % L.getD 4 1)) := by
  set L0 := L.getD 0 1 with hL0
  set L1 := L.getD 1 1 with hL1
  set L2 := L.getD 2 1 with hL2
  set L3 := L.getD 3 1 with hL3
  set L4 := L.getD 4 1 with hL4
  have p0 : 0 < L0 := hL 0 (by norm_num)
  have p1 : 0 < L1 := hL 1 (by norm_num)
  have p2 : 0 < L2 := hL 2 (by norm_num)
  have p3 : 0 < L3 := hL 3 (by norm_num)
  have p4 : 0 < L4 := hL 4 (by norm_num)
  have dg : ∀ p q, q < 5 → digit L p q < L.getD q 1 := by
    intro p q hq
    have := digit_lt L (p := p) q (by rw [min_eq_left (by omega)]; exact hL q hq)
    rwa [min_eq_left (by omega)] at this
  -- both sides as sums over finsets of tuples
  rw [← Finset.sum_product' (s := Finset.range (boxN L)) (t := Finset.range (boxN L))
      (f := fun t s => if digit L t 4 * L4 + digit L s 4 = x4 then F t s else 0), ← Finset.sum_filter]
  simp only [← Finset.sum_product']
  refine Finset.sum_nbij'
    (fun p => (digit L p.1 3 * L3 + digit L p.2 3, (digit L p.1 2 * L2 + digit L p.2 2,
      (digit L p.1 1 * L1 + digit L p.2 1, digit L p.1 0 * L0 + digit L p.2 0))))
    (fun x => (flat5 L (x.2.2.2 / L0) (x.2.2.1 / L1) (x.2.1 / L2) (x.1 / L3) (x4 / L4),
      flat5 L (x.2.2.2 % L0) (x.2.2.1 % L1) (x.2.1 % L2) (x.1 % L3) (x4 % L4))) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
    exact ⟨lt_of_rc (dg _ 3 (by norm_num)) (dg _ 3 (by norm_num)), lt_of_rc (dg _ 2 (by norm_num))
      (dg _ 2 (by norm_num)), lt_of_rc (dg _ 1 (by norm_num)) (dg _ 1 (by norm_num)),
      lt_of_rc (dg _ 0 (by norm_num)) (dg _ 0 (by norm_num))⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hx ⊢
    obtain ⟨h3, h2, h1, h0⟩ := hx
    have q0 : x.2.2.2 / L0 < L0 := Nat.div_lt_of_lt_mul h0
    have q1 : x.2.2.1 / L1 < L1 := Nat.div_lt_of_lt_mul h1
    have q2 : x.2.1 / L2 < L2 := Nat.div_lt_of_lt_mul h2
    have q3 : x.1 / L3 < L3 := Nat.div_lt_of_lt_mul h3
    have q4 : x4 / L4 < L4 := Nat.div_lt_of_lt_mul hx4
    have r0 : x.2.2.2 % L0 < L0 := Nat.mod_lt _ p0
    have r1 : x.2.2.1 % L1 < L1 := Nat.mod_lt _ p1
    have r2 : x.2.1 % L2 < L2 := Nat.mod_lt _ p2
    have r3 : x.1 % L3 < L3 := Nat.mod_lt _ p3
    have r4 : x4 % L4 < L4 := Nat.mod_lt _ p4
    refine ⟨⟨flat5_lt L q0 q1 q2 q3 q4, flat5_lt L r0 r1 r2 r3 r4⟩, ?_⟩
    rw [(digit_flat5 L q0 q1 q2 q3 q4).2.2.2.2, (digit_flat5 L r0 r1 r2 r3 r4).2.2.2.2, Nat.div_add_mod']
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨⟨ht, hs⟩, hP⟩ := hp
    have e : ∀ q, q < 5 → (digit L p.1 q * L.getD q 1 + digit L p.2 q) / L.getD q 1 = digit L p.1 q ∧
        (digit L p.1 q * L.getD q 1 + digit L p.2 q) % L.getD q 1 = digit L p.2 q :=
      fun q hq => ⟨rc_div (dg _ q hq), rc_mod (dg _ q hq)⟩
    have e4 : x4 / L4 = digit L p.1 4 ∧ x4 % L4 = digit L p.2 4 := by
      rw [← hP]; exact e 4 (by norm_num)
    simp only [Prod.ext_iff]
    rw [(e 0 (by norm_num)).1, (e 1 (by norm_num)).1, (e 2 (by norm_num)).1, (e 3 (by norm_num)).1, e4.1,
      (e 0 (by norm_num)).2, (e 1 (by norm_num)).2, (e 2 (by norm_num)).2, (e 3 (by norm_num)).2, e4.2]
    exact ⟨flat5_digit L ht, flat5_digit L hs⟩
  · intro x hx
    simp only [Finset.mem_product, Finset.mem_range] at hx
    obtain ⟨h3, h2, h1, h0⟩ := hx
    have q0 : x.2.2.2 / L0 < L0 := Nat.div_lt_of_lt_mul h0
    have q1 : x.2.2.1 / L1 < L1 := Nat.div_lt_of_lt_mul h1
    have q2 : x.2.1 / L2 < L2 := Nat.div_lt_of_lt_mul h2
    have q3 : x.1 / L3 < L3 := Nat.div_lt_of_lt_mul h3
    have q4 : x4 / L4 < L4 := Nat.div_lt_of_lt_mul hx4
    have r0 : x.2.2.2 % L0 < L0 := Nat.mod_lt _ p0
    have r1 : x.2.2.1 % L1 < L1 := Nat.mod_lt _ p1
    have r2 : x.2.1 % L2 < L2 := Nat.mod_lt _ p2
    have r3 : x.1 % L3 < L3 := Nat.mod_lt _ p3
    have r4 : x4 % L4 < L4 := Nat.mod_lt _ p4
    obtain ⟨a0, a1, a2, a3, -⟩ := digit_flat5 L q0 q1 q2 q3 q4
    obtain ⟨b0, b1, b2, b3, -⟩ := digit_flat5 L r0 r1 r2 r3 r4
    simp only [a0, a1, a2, a3, b0, b1, b2, b3, Nat.div_add_mod']
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
    obtain ⟨⟨ht, hs⟩, hP⟩ := hp
    have e : ∀ q, q < 5 → (digit L p.1 q * L.getD q 1 + digit L p.2 q) / L.getD q 1 = digit L p.1 q ∧
        (digit L p.1 q * L.getD q 1 + digit L p.2 q) % L.getD q 1 = digit L p.2 q :=
      fun q hq => ⟨rc_div (dg _ q hq), rc_mod (dg _ q hq)⟩
    have e4 : x4 / L4 = digit L p.1 4 ∧ x4 % L4 = digit L p.2 4 := by
      rw [← hP]; exact e 4 (by norm_num)
    simp only
    rw [(e 0 (by norm_num)).1, (e 1 (by norm_num)).1, (e 2 (by norm_num)).1, (e 3 (by norm_num)).1, e4.1,
      (e 0 (by norm_num)).2, (e 1 (by norm_num)).2, (e 2 (by norm_num)).2, (e 3 (by norm_num)).2, e4.2,
      flat5_digit L ht, flat5_digit L hs]

end NPT.CP3.D1
