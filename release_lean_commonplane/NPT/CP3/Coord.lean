/-
NPT.CP3.Coord — the coordinate representation of Gram forms, as abstract linear algebra.

* `gram_coord`: a symmetric `H` with `H = Pᵀ H P` and `Pᵀ = W K` equals `W S Wᵀ` with `S = W⁺ H W⁺ᵀ`, where `W⁺ W = 1`
  (the bosonic range of the Gram forms).
* `stab_coord`: a symmetric `S` with `B S Bᵀ = S` for every `B` of a finite list lies in the span of matrices `S_j`,
  with explicit coefficients, once the sums `Σ_B B (E_ab + E_ba) Bᵀ` lie in that span (site-stabilizer invariance).
-/
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Module.BigOperators

open Matrix BigOperators Finset

namespace NPT.CP3

section Gram

variable {R : Type*} [CommRing R] {m r : Type*} [Fintype m] [Fintype r] [DecidableEq r]

/-- **Bosonic range.** -/
theorem gram_coord (H P : Matrix m m R) (W : Matrix m r R) (Wp : Matrix r m R) (K : Matrix r m R)
    (hH : Hᵀ = H) (hP : H = Pᵀ * H * P) (hWp : Wp * W = 1) (hK : Pᵀ = W * K) :
    H = W * (Wp * H * Wpᵀ) * Wᵀ := by
  have hWWP : W * Wp * Pᵀ = Pᵀ := by
    rw [hK, Matrix.mul_assoc W Wp, ← Matrix.mul_assoc Wp, hWp, Matrix.one_mul]
  have h1 : W * Wp * H = H := by
    conv_lhs => rw [hP]
    rw [← Matrix.mul_assoc (W * Wp), ← Matrix.mul_assoc (W * Wp), hWWP, ← hP]
  have h2 : H * (W * Wp)ᵀ = H := by
    have h := congrArg Matrix.transpose h1
    rwa [Matrix.transpose_mul, hH] at h
  calc H = W * Wp * H * (W * Wp)ᵀ := by rw [h1, h2]
    _ = W * (Wp * H * Wpᵀ) * Wᵀ := by rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]

end Gram

section Stab

variable {K : Type*} [Field K] [CharZero K] {r ι : Type*} [Fintype r] [DecidableEq r] [Fintype ι]

/-- The symmetric units `E_ab + E_ba`. -/
def symU (a b : r) : Matrix r r K := single a b 1 + single b a 1

lemma sum_ite_and_eq (f : r → r → K) (i j : r) : (∑ a, ∑ b, if a = i ∧ b = j then f a b else 0) = f i j := by
  simp [ite_and, Finset.sum_ite_eq', Finset.sum_ite_eq]

lemma sym_expand (S : Matrix r r K) (hSt : Sᵀ = S) : S = ∑ a, ∑ b, (S a b / 2) • symU a b := by
  have hji : ∀ i j, S j i = S i j := fun i j => by
    have := congrFun (congrFun hSt i) j
    simpa [Matrix.transpose_apply] using this
  ext i j
  have e : ∀ a b, ((S a b / 2) • symU (K := K) a b) i j =
      (if a = i ∧ b = j then S a b / 2 else 0) + (if b = i ∧ a = j then S a b / 2 else 0) := by
    intro a b
    simp only [symU, Matrix.smul_apply, Matrix.add_apply, single_apply, smul_eq_mul, mul_add, mul_ite, mul_one,
      mul_zero]
  simp only [Matrix.sum_apply, e, Finset.sum_add_distrib, sum_ite_and_eq]
  have h2 : (∑ a, ∑ b, if b = i ∧ a = j then S a b / 2 else 0) = S j i / 2 := by
    rw [Finset.sum_comm]
    exact sum_ite_and_eq (fun b a => S a b / 2) i j
  rw [h2, hji]
  ring

/-- **Stabilizer span.** -/
theorem stab_coord {n : ℕ} (Bs : Fin n → Matrix r r K) (S : Matrix r r K) (hSt : Sᵀ = S)
    (hS : ∀ i, Bs i * S * (Bs i)ᵀ = S) (Sj : ι → Matrix r r K) (c : r → r → ι → K)
    (hc : ∀ a b, ∑ i, Bs i * symU a b * (Bs i)ᵀ = ∑ j, c a b j • Sj j) (hn : n ≠ 0) :
    S = ∑ j, ((∑ a, ∑ b, S a b * c a b j) / (2 * n)) • Sj j := by
  have hTS : ∑ i, Bs i * S * (Bs i)ᵀ = (n : K) • S := by
    simp only [hS, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    exact (Nat.cast_smul_eq_nsmul K n S).symm
  have hTS2 : ∑ i, Bs i * S * (Bs i)ᵀ = ∑ j, (∑ a, ∑ b, S a b / 2 * c a b j) • Sj j := by
    calc ∑ i, Bs i * S * (Bs i)ᵀ
        = ∑ i, ∑ a, ∑ b, (S a b / 2) • (Bs i * symU a b * (Bs i)ᵀ) := by
          conv_lhs => rw [sym_expand S hSt]
          simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
      _ = ∑ a, ∑ b, (S a b / 2) • ∑ i, Bs i * symU a b * (Bs i)ᵀ := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun b _ => (Finset.smul_sum ..).symm
      _ = ∑ a, ∑ b, ∑ j, (S a b / 2 * c a b j) • Sj j := by
          simp only [hc, Finset.smul_sum, smul_smul]
      _ = ∑ a, ∑ j, ∑ b, (S a b / 2 * c a b j) • Sj j := Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ j, ∑ a, ∑ b, (S a b / 2 * c a b j) • Sj j := Finset.sum_comm
      _ = ∑ j, (∑ a, ∑ b, S a b / 2 * c a b j) • Sj j := by simp only [Finset.sum_smul]
  have hn' : (n : K) ≠ 0 := by exact_mod_cast hn
  calc S = ((n : K))⁻¹ • ∑ i, Bs i * S * (Bs i)ᵀ := by rw [hTS, smul_smul, inv_mul_cancel₀ hn', one_smul]
    _ = ((n : K))⁻¹ • ∑ j, (∑ a, ∑ b, S a b / 2 * c a b j) • Sj j := by rw [hTS2]
    _ = ∑ j, ((∑ a, ∑ b, S a b * c a b j) / (2 * n)) • Sj j := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_smul]
        congr 1
        rw [Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [mul_inv]
        ring

end Stab

end NPT.CP3
