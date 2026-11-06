/-
NPT.Cert.PsdSound — soundness of the kernel PSD checker `PBlock.check`:
`b.check Lden UB = true → (b.Zmat Lden).PosSemidef`.
-/
import NPT.Cert.PsdCheck
import Mathlib.Algebra.BigOperators.Field

open Matrix BigOperators Finset
open scoped ComplexOrder

namespace NPT.Cert

/-! ### Diagonal dominance (from an earlier formalization, `psd_of_dom`, verbatim proof) -/

/-- A Hermitian matrix whose diagonal dominates the off-diagonal row sums is positive semidefinite. -/
lemma psd_of_dom {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hH : M.IsHermitian)
    (hd : ∀ i, ∑ j, (if j = i then 0 else ‖M i j‖) ≤ (M i i).re) : M.PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg hH fun x => ?_
  have him : (star x ⬝ᵥ (M *ᵥ x)).im = 0 := by
    have h := hH.star_dotProduct_mulVec_comm x x
    have := congrArg Complex.im h
    rw [Complex.star_def, Complex.conj_im] at this
    linarith
  rw [Complex.nonneg_iff]
  refine ⟨?_, him.symm⟩
  have hdiag : ∀ i, (M i i).im = 0 := fun i => by
    have := congrArg Complex.im (hH.apply i i)
    rw [Complex.star_def, Complex.conj_im] at this
    linarith
  have hsym : ∀ i j, ‖M i j‖ = ‖M j i‖ := fun i j => by rw [← hH.apply j i, norm_star]
  set a : Fin n → ℝ := fun i => ‖x i‖
  have hterm : ∀ i j, (if j = i then (M i i).re * a i ^ 2 else -(‖M i j‖ * (a i ^ 2 + a j ^ 2) / 2)) ≤
      (star (x i) * (M i j * x j)).re := by
    intro i j
    split_ifs with hji
    · subst hji
      rw [show star (x j) * (M j j * x j) = M j j * (star (x j) * x j) by ring, Complex.star_def,
        Complex.conj_mul', ← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hdiag,
        zero_mul, sub_zero]
    · have h1 := Complex.abs_re_le_norm (star (x i) * (M i j * x j))
      have h2 : ‖star (x i) * (M i j * x j)‖ = ‖M i j‖ * (a i * a j) := by
        simp only [norm_mul, norm_star, a]; ring
      have h3 : a i * a j ≤ (a i ^ 2 + a j ^ 2) / 2 := by nlinarith [sq_nonneg (a i - a j)]
      have h4 := neg_abs_le (star (x i) * (M i j * x j)).re
      have h5 : ‖M i j‖ * (a i * a j) ≤ ‖M i j‖ * ((a i ^ 2 + a j ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
      linarith
  have hsum : (star x ⬝ᵥ (M *ᵥ x)).re = ∑ i, ∑ j, (star (x i) * (M i j * x j)).re := by
    simp only [dotProduct, mulVec, Pi.star_apply, Finset.mul_sum, Complex.re_sum]
  rw [hsum]
  refine le_trans ?_ (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j)
  set m : Fin n → Fin n → ℝ := fun i j => if j = i then 0 else ‖M i j‖ with hm
  set R : Fin n → ℝ := fun i => ∑ j, m i j with hR
  have hmsym : ∀ i j, m i j = m j i := fun i j => by
    simp only [hm]
    by_cases hij : j = i
    · subst hij; rfl
    · rw [if_neg hij, if_neg (Ne.symm hij), hsym]
  have e1 : ∀ i j, (if j = i then (M i i).re * a i ^ 2 else -(‖M i j‖ * (a i ^ 2 + a j ^ 2) / 2)) =
      (if j = i then (M i i).re * a i ^ 2 else 0) - m i j * a i ^ 2 / 2 - m i j * a j ^ 2 / 2 := by
    intro i j
    simp only [hm]
    split_ifs <;> ring
  simp only [e1, Finset.sum_sub_distrib]
  have s1 : ∀ i, ∑ j, (if j = i then (M i i).re * a i ^ 2 else 0) = (M i i).re * a i ^ 2 := fun i => by
    rw [Finset.sum_ite_eq']; simp
  have s2 : ∀ i, ∑ j, m i j * a i ^ 2 / 2 = R i * a i ^ 2 / 2 := fun i => by
    simp only [hR]; rw [Finset.sum_mul, Finset.sum_div]
  have s3 : ∑ i, ∑ j, m i j * a j ^ 2 / 2 = ∑ i, R i * a i ^ 2 / 2 := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hR]; rw [Finset.sum_mul, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [hmsym]
  simp only [s1, s2, s3]
  have : ∀ i, 0 ≤ ((M i i).re - R i) * a i ^ 2 := fun i => mul_nonneg (sub_nonneg.2 (hd i)) (sq_nonneg _)
  have h0 := Finset.sum_nonneg fun i (_ : i ∈ univ) => this i
  have e2 : ∑ i, ((M i i).re - R i) * a i ^ 2 = ∑ i, (M i i).re * a i ^ 2 - ∑ i, R i * a i ^ 2 / 2 -
      ∑ i, R i * a i ^ 2 / 2 := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

/-! ### List lemmas -/

lemma dot3_eq_sum : ∀ (a c b : List Int) (N : ℕ), a.length ≤ N →
    dot3 a c b = ∑ k ∈ range N, a.getD k 0 * c.getD k 0 * b.getD k 0
  | [], c, b, N, _ => by simp [dot3]
  | x :: as, [], b, N, _ => by simp [dot3]
  | x :: as, y :: cs, [], N, _ => by simp [dot3]
  | x :: as, y :: cs, z :: bs, N, h => by
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by simp at h; omega⟩
    rw [Finset.sum_range_succ', dot3, dot3_eq_sum as cs bs M (by simp at h; omega)]
    simp [add_comm]

lemma dot3_comm : ∀ (a c b : List Int), dot3 a c b = dot3 b c a
  | [], c, b => by cases c <;> cases b <;> simp [dot3]
  | x :: as, [], b => by cases b <;> simp [dot3]
  | x :: as, y :: cs, [] => by simp [dot3]
  | x :: as, y :: cs, z :: bs => by simp [dot3, dot3_comm as cs bs]; ring

lemma sum_map_range_eq (f : ℕ → Int) (n : ℕ) : ((List.range n).map f).sum = ∑ j ∈ range n, f j := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

namespace PBlock

variable (b : PBlock)

lemma lrow_length {i : ℕ} (h : (b.lrows.getD i []).length = i) : (b.lrow i).length = i + 1 := by
  rw [lrow, List.length_append, h]; rfl

lemma rval_comm (i j : ℕ) (h : b.zget i j = b.zget j i) : b.rval i j = b.rval j i := by
  simp only [rval, h, dot3_comm (b.lrow i)]

lemma ufind_comm (i j : ℕ) : b.ufind i j = b.ufind j i := by
  unfold ufind
  congr 1
  funext e
  cases (e.1 == i) <;> cases (e.2.1 == j) <;> cases (e.1 == j) <;> cases (e.2.1 == i) <;> rfl

lemma uval_comm (Lden : ℕ) (i j : ℕ) : b.uval Lden i j = b.uval Lden j i := by
  simp only [uval, ufind_comm b i j]

lemma uval_abs_le {Lden UB : ℕ} (hu : b.uOK Lden UB = true) (i j : ℕ) :
    |b.uval Lden i j| ≤ (1 : ℚ) / 2 ^ UB := by
  unfold uval
  cases hf : b.ufind i j with
  | none => simp
  | some e =>
    have hmem : e ∈ b.uent := List.mem_of_find?_eq_some hf
    have he := List.all_eq_true.1 hu e hmem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at he
    obtain ⟨-, hle⟩ := he
    simp only
    by_cases hL : Lden = 0
    · subst hL
      have : e.2.2.natAbs = 0 := by
        have hp : 0 < 2 ^ UB := by positivity
        nlinarith [Nat.zero_le e.2.2.natAbs]
      have hz : e.2.2 = 0 := Int.natAbs_eq_zero.1 this
      simp [hz]
    · have hLpos : (0 : ℚ) < Lden := by exact_mod_cast Nat.pos_of_ne_zero hL
      rw [abs_div, abs_of_pos hLpos, div_le_div_iff₀ hLpos (by positivity)]
      have h1 : ((e.2.2.natAbs : ℕ) : ℚ) * 2 ^ UB ≤ (Lden : ℚ) := by exact_mod_cast hle
      have h2 : |(e.2.2 : ℚ)| = ((e.2.2.natAbs : ℕ) : ℚ) := by
        rw [Nat.cast_natAbs, Int.cast_abs]
      rw [h2]; linarith

/-- `L` (scaled down) as a complex matrix. -/
def Lm : Matrix (Fin b.n) (Fin b.n) ℂ := fun i k => (((b.lget i k : ℚ) / 2 ^ b.F : ℚ) : ℂ)

/-- `D` (scaled down) as a complex diagonal matrix. -/
def Dm : Matrix (Fin b.n) (Fin b.n) ℂ := diagonal fun k => (((b.dlist.getD k 0 : ℚ) / 2 ^ b.E : ℚ) : ℂ)

/-- The remainder `R / 2^(2F+E) + U`. -/
def Rm (Lden : ℕ) : Matrix (Fin b.n) (Fin b.n) ℂ :=
  fun i j => (((b.rval i j : ℚ) / 2 ^ (2 * b.F + b.E) + b.uval Lden i j : ℚ) : ℂ)

lemma lenOK_spec (hl : b.lenOK = true) {i : ℕ} (hi : i < b.n) : (b.lrows.getD i []).length = i := by
  have := List.all_eq_true.1 hl i (List.mem_range.2 hi)
  simpa using this

lemma symOK_spec (hs : b.symOK = true) {i j : ℕ} (hi : i < b.n) (hj : j < b.n) : b.zget i j = b.zget j i := by
  have := List.all_eq_true.1 (List.all_eq_true.1 hs i (List.mem_range.2 hi)) j (List.mem_range.2 hj)
  simpa using this

lemma dot3_lrow (hl : b.lenOK = true) (i j : Fin b.n) :
    dot3 (b.lrow i) b.dlist (b.lrow j) = ∑ k : Fin b.n, b.lget i k * b.dlist.getD k 0 * b.lget j k := by
  have hlen : (b.lrow i).length ≤ b.n := by
    rw [b.lrow_length (b.lenOK_spec hl i.2)]; exact i.2
  rw [dot3_eq_sum _ _ _ b.n hlen, ← Fin.sum_univ_eq_sum_range]
  rfl

lemma LDL_entry (hl : b.lenOK = true) (i j : Fin b.n) :
    (b.Lm * b.Dm * b.Lmᴴ) i j = (((dot3 (b.lrow i) b.dlist (b.lrow j) : ℚ) / 2 ^ (2 * b.F + b.E) : ℚ) : ℂ) := by
  rw [b.dot3_lrow hl i j]
  simp only [Matrix.mul_apply, Lm, Dm, Matrix.diagonal_apply, Matrix.conjTranspose_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, star_ratCast]
  push_cast
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pow_add, pow_mul']
  field_simp

lemma Zmat_eq (Lden : ℕ) (hl : b.lenOK = true) :
    b.Zmat Lden = b.Lm * b.Dm * b.Lmᴴ + b.Rm Lden := by
  ext i j
  rw [Matrix.add_apply, b.LDL_entry hl i j]
  simp only [Zmat, Rm, rval, pow2I, Int.ofNat_eq_coe]
  push_cast
  rw [pow_add, pow_mul']
  field_simp
  ring

lemma Dm_psd : b.Dm.PosSemidef := by
  rw [Dm, posSemidef_diagonal_iff]
  intro k
  have h : (0 : ℚ) ≤ (b.dlist.getD k 0 : ℚ) / 2 ^ b.E := by
    apply div_nonneg _ (by positivity)
    have : 0 ≤ b.dlist.getD k 0 := by
      unfold dlist
      rw [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases b.dvals[k]? <;> simp
    exact_mod_cast this
  have h' : (0 : ℝ) ≤ (((b.dlist.getD k 0 : ℚ) / 2 ^ b.E : ℚ) : ℝ) := by exact_mod_cast h
  rw [← Complex.ofReal_ratCast]
  exact Complex.zero_le_real.2 h'

lemma Rm_herm (Lden : ℕ) (hs : b.symOK = true) : (b.Rm Lden).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Rm, star_ratCast]
  rw [b.rval_comm j i (b.symOK_spec hs j.2 i.2), b.uval_comm Lden j i]

lemma rowOK_spec {UB : ℕ} (hr : (List.range b.n).all (b.rowOK UB) = true) {i : ℕ} (hi : i < b.n) :
    (∑ j ∈ range b.n, (if j = i then (0 : ℤ) else ((b.rval i j).natAbs : ℤ))) +
      (b.n : ℤ) * pow2I (2 * b.F + b.E - UB) ≤ b.rval i i := by
  have h := List.all_eq_true.1 hr i (List.mem_range.2 hi)
  simp only [rowOK, decide_eq_true_eq] at h
  rw [← sum_map_range_eq]
  simpa using h

lemma Rm_dom {Lden UB : ℕ} (hU : UB ≤ 2 * b.F + b.E) (hu : b.uOK Lden UB = true)
    (hr : (List.range b.n).all (b.rowOK UB) = true) (i : Fin b.n) :
    ∑ j, (if j = i then 0 else ‖b.Rm Lden i j‖) ≤ (b.Rm Lden i i).re := by
  set s : ℝ := 2 ^ (2 * b.F + b.E) with hs
  set ε : ℝ := 1 / 2 ^ UB with hε
  have hspos : 0 < s := by positivity
  have hεs : (2 : ℝ) ^ (2 * b.F + b.E - UB) / s = ε := by
    rw [hs, hε, div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add, Nat.sub_add_cancel hU]
  have hu' : ∀ i' j', |(b.uval Lden i' j' : ℝ)| ≤ ε := fun i' j' => by
    have h1 := b.uval_abs_le hu i' j'
    have h2 : ((|b.uval Lden i' j'| : ℚ) : ℝ) ≤ (((1 : ℚ) / 2 ^ UB : ℚ) : ℝ) := by exact_mod_cast h1
    rw [Rat.cast_abs] at h2
    rw [hε]; push_cast at h2; exact h2
  have hnorm : ∀ j : Fin b.n, ‖b.Rm Lden i j‖ ≤ |(b.rval i j : ℝ)| / s + ε := fun j => by
    simp only [Rm, Complex.norm_ratCast]
    push_cast
    calc |(b.rval i j : ℝ) / 2 ^ (2 * b.F + b.E) + (b.uval Lden i j : ℝ)|
        ≤ |(b.rval i j : ℝ) / 2 ^ (2 * b.F + b.E)| + |(b.uval Lden i j : ℝ)| := abs_add_le _ _
      _ ≤ |(b.rval i j : ℝ)| / s + ε := by
        rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 ^ (2 * b.F + b.E))]
        exact add_le_add (le_of_eq rfl) (hu' i j)
  have hdiag : (b.rval i i : ℝ) / s - ε ≤ (b.Rm Lden i i).re := by
    simp only [Rm, Complex.ratCast_re]
    push_cast
    have := hu' i i
    rw [abs_le] at this
    rw [hs]; linarith [this.1]
  have hrow := b.rowOK_spec hr i.2
  have hrow' : (∑ j ∈ range b.n, (if j = (i : ℕ) then (0 : ℝ) else |(b.rval i j : ℝ)|)) +
      (b.n : ℝ) * 2 ^ (2 * b.F + b.E - UB) ≤ (b.rval i i : ℝ) := by
    have := (Int.cast_le (R := ℝ)).2 hrow
    push_cast [pow2I, Int.ofNat_eq_natCast] at this
    convert this using 2
  -- assemble
  have hsum : ∑ j, (if j = i then 0 else ‖b.Rm Lden i j‖) ≤
      ∑ j : Fin b.n, (if j = i then 0 else |(b.rval i j : ℝ)| / s + ε) :=
    Finset.sum_le_sum fun j _ => by split_ifs; rfl; exact hnorm j
  have hsplit : ∑ j : Fin b.n, (if j = i then (0 : ℝ) else |(b.rval i j : ℝ)| / s + ε) =
      (∑ j ∈ range b.n, (if j = (i : ℕ) then (0 : ℝ) else |(b.rval i j : ℝ)|)) / s + ((b.n : ℝ) - 1) * ε := by
    have e : ∀ j : Fin b.n, (if j = i then (0 : ℝ) else |(b.rval i j : ℝ)| / s + ε) =
        (fun j : ℕ => if j = (i : ℕ) then (0 : ℝ) else |(b.rval i j : ℝ)| / s + ε) j := fun j => by
      simp only [Fin.val_inj]
    rw [Finset.sum_congr rfl (fun j _ => e j),
      Fin.sum_univ_eq_sum_range (fun j : ℕ => if j = (i : ℕ) then (0 : ℝ) else |(b.rval i j : ℝ)| / s + ε) b.n,
      Finset.sum_div]
    have hcard : ∑ j ∈ range b.n, (if j = (i : ℕ) then (0 : ℝ) else ε) = ((b.n : ℝ) - 1) * ε := by
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul]
      congr 1
      rw [Finset.filter_ne' (range b.n) (i : ℕ), Finset.card_erase_of_mem (Finset.mem_range.2 i.2),
        Finset.card_range]
      have : 1 ≤ b.n := Nat.one_le_of_lt i.2
      push_cast [Nat.cast_sub this]; ring
    rw [← hcard, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have key : (∑ j ∈ range b.n, (if j = (i : ℕ) then (0 : ℝ) else |(b.rval i j : ℝ)|)) / s + (b.n : ℝ) * ε ≤
      (b.rval i i : ℝ) / s := by
    rw [← hεs, mul_div_assoc', ← add_div]
    exact div_le_div_of_nonneg_right hrow' hspos.le
  linarith

theorem check_sound {Lden UB : ℕ} (h : b.check Lden UB = true) : (b.Zmat Lden).PosSemidef := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hU, hs⟩, hl⟩, hu⟩, hr⟩ := h
  rw [b.Zmat_eq Lden hl]
  exact (b.Dm_psd.mul_mul_conjTranspose_same b.Lm).add (psd_of_dom (b.Rm_herm Lden hs) (b.Rm_dom hU hu hr))

end PBlock

end NPT.Cert
