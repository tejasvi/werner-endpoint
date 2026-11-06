/-
NPT.Cert.NormalForm — normal form of a rank-two operator (helper task H2).

* `normal_form` : every `C = A0 B0ᴴ` on `k ≥ 1` copies of `ℂ^d`, `d ≥ 2`, is `0` or `C = A Bᴴ` with
  `Aᴴ A = c • 1` (`c > 0`) and `‖B‖_F = ‖A‖_F`.
  Proof: an orthonormal pair `Q` (Gram–Schmidt in `EuclideanSpace ℂ (Fin k → Fin d)`, which has
  `d^k ≥ 2` coordinates) spans the columns of `A0`, so `C = Q Mᴴ` with `M = B0 A0ᴴ Q`; if `M ≠ 0`
  take `A = s Q`, `B = M / s` with `s⁴ = ‖M‖²_F / 2`.
* `q_zero` : `q t 0 = 0`.
-/
import NPT.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

open Matrix BigOperators Finset

namespace NPT.Cert

/-- `q t 0 = 0`: every partial trace of `0` is `0`. -/
theorem q_zero {k d : ℕ} [NeZero d] (t : ℝ) : NPT.q t (0 : NPT.Op (Fin k) d) = 0 := by
  simp [NPT.q, NPT.ptrace, NPT.frobSq]

namespace NormalForm

/-- Entry formula for the inner product of `EuclideanSpace ℂ ι`. -/
lemma inner_eq_sum {ι : Type*} [Fintype ι] (u v : EuclideanSpace ℂ ι) :
    inner ℂ u v = ∑ x, star (u x) * v x := by
  simp only [PiLp.inner_apply, RCLike.inner_apply', starRingEnd_apply]

/-- With at least two rows, there is an orthonormal pair of columns `Q` whose span contains the
columns of `A0` (Gram–Schmidt on `col 0, col 1, col 1, …`). -/
lemma exists_orthonormal_pair {ι : Type*} [Fintype ι] [DecidableEq ι] (h2 : 2 ≤ Fintype.card ι)
    (A0 : Matrix ι (Fin 2) ℂ) :
    ∃ Q : Matrix ι (Fin 2) ℂ, Qᴴ * Q = 1 ∧ Q * (Qᴴ * A0) = A0 := by
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card ι = m + 2 := ⟨Fintype.card ι - 2, by omega⟩
  let col : Fin 2 → EuclideanSpace ℂ ι := fun γ => WithLp.toLp 2 (fun x => A0 x γ)
  let e : Fin 2 → Fin (m + 2) := Fin.castLE (by omega)
  have he : Function.Injective e := Fin.castLE_injective _
  let f : Fin (m + 2) → EuclideanSpace ℂ ι := fun j => if (j : ℕ) = 0 then col 0 else col 1
  have h : Module.finrank ℂ (EuclideanSpace ℂ ι) = Fintype.card (Fin (m + 2)) := by
    simp [hm]
  let b := InnerProductSpace.gramSchmidtOrthonormalBasis h f
  have hfe : ∀ γ, f (e γ) = col γ := by
    intro γ; fin_cases γ
    · exact ite_eq_left rfl
    · exact ite_eq_right (show ((e 1 : Fin (m + 2)) : ℕ) ≠ 0 from one_ne_zero)
  -- the basis vectors `b j`, `j ≥ 2`, are orthogonal to both columns
  have hzero : ∀ γ j, j ∉ Set.range e → inner ℂ (b j) (col γ) = 0 := by
    intro γ j hj
    have hj2 : 2 ≤ (j : ℕ) := by
      by_contra hj2'
      exact hj ⟨⟨j, by omega⟩, Fin.ext rfl⟩
    have hlt : e γ < j := by
      rw [Fin.lt_def]
      show (γ : ℕ) < j
      omega
    rw [← hfe γ]
    exact InnerProductSpace.gramSchmidtOrthonormalBasis_inv_triangular h f hlt
  let Q : Matrix ι (Fin 2) ℂ := Matrix.of fun x α => b (e α) x
  refine ⟨Q, ?_, ?_⟩
  · ext α β
    have := (orthonormal_iff_ite.mp b.orthonormal) (e α) (e β)
    rw [inner_eq_sum] at this
    simp only [Q, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.one_apply]
    rw [this]
    simp [he.eq_iff]
  · ext x γ
    have hx := congrArg (fun w : EuclideanSpace ℂ ι => w x) (b.sum_repr' (col γ))
    simp only [WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply, smul_eq_mul] at hx
    rw [← Fintype.sum_of_injective e he (fun α => inner ℂ (b (e α)) (col γ) * b (e α) x)
      (fun j => inner ℂ (b j) (col γ) * b j x)
      (fun j hj => by simp [hzero γ j hj]) (fun α => rfl)] at hx
    change _ = A0 x γ at hx
    simp only [Q, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
    rw [← hx]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [inner_eq_sum, mul_comm]

/-- A matrix with two orthonormal columns has squared Frobenius norm `2`. -/
lemma sum_normSq_eq_two {ι : Type*} [Fintype ι] (Q : Matrix ι (Fin 2) ℂ) (hQ : Qᴴ * Q = 1) :
    ∑ x, ∑ α, Complex.normSq (Q x α) = 2 := by
  have hcol : ∀ α, ∑ x, Complex.normSq (Q x α) = 1 := by
    intro α
    have h := congrFun (congrFun hQ α) α
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
    have : ((∑ x, Complex.normSq (Q x α) : ℝ) : ℂ) = 1 := by
      push_cast
      rw [← h]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Complex.normSq_eq_conj_mul_self]
      rfl
    exact_mod_cast this
  rw [Finset.sum_comm, Fin.sum_univ_two, hcol, hcol]
  norm_num

end NormalForm

/-- Normal form of a rank-≤2 operator: `C = 0`, or `C = A Bᴴ` where `A` has orthogonal columns of
equal positive norm (`Aᴴ A = c • 1`, `c > 0`) and `‖B‖_F = ‖A‖_F`. -/
theorem normal_form {k d : ℕ} [NeZero d] (hk : 1 ≤ k) (hd : 2 ≤ d)
    (C : NPT.Op (Fin k) d) (hC : NPT.RankLE2 C) :
    C = 0 ∨ ∃ A B : Matrix (Fin k → Fin d) (Fin 2) ℂ, C = A * Bᴴ ∧
      (∃ c : ℝ, 0 < c ∧ Aᴴ * A = (c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
      (∑ x, ∑ α, Complex.normSq (B x α)) = ∑ x, ∑ α, Complex.normSq (A x α) := by
  obtain ⟨A0, B0, rfl⟩ := hC
  have h2 : 2 ≤ Fintype.card (Fin k → Fin d) := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    calc 2 ≤ d := hd
      _ = d ^ 1 := (pow_one d).symm
      _ ≤ d ^ k := Nat.pow_le_pow_right (by omega) hk
  obtain ⟨Q, hQQ, hQA⟩ := NormalForm.exists_orthonormal_pair h2 A0
  -- `Q Qᴴ` fixes the columns of `A0`, so `C = Q Mᴴ`
  set M := B0 * A0ᴴ * Q with hM
  have hCM : A0 * B0ᴴ = Q * Mᴴ := by
    rw [hM, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    conv_lhs => rw [← hQA]
    simp only [Matrix.mul_assoc]
  by_cases hM0 : M = 0
  · left
    rw [hCM, hM0, Matrix.conjTranspose_zero, Matrix.mul_zero]
  right
  set N := ∑ x, ∑ α, Complex.normSq (M x α) with hN
  have hNpos : 0 < N := by
    obtain ⟨x0, α0, hx0⟩ : ∃ x α, M x α ≠ 0 := by
      by_contra hcon
      exact hM0 (Matrix.ext fun x α => by_contra fun h => hcon ⟨x, α, h⟩)
    exact Finset.sum_pos' (fun x _ => Finset.sum_nonneg fun α _ => Complex.normSq_nonneg _)
      ⟨x0, Finset.mem_univ _, Finset.sum_pos' (fun α _ => Complex.normSq_nonneg _)
        ⟨α0, Finset.mem_univ _, Complex.normSq_pos.mpr hx0⟩⟩
  -- rescale: `A = s Q`, `B = M / s` with `s⁴ = N / 2`
  set s := Real.sqrt (Real.sqrt (N / 2)) with hs
  have hspos : 0 < s := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (by positivity))
  have hs4 : s ^ 2 * s ^ 2 = N / 2 := by
    rw [hs, Real.sq_sqrt (Real.sqrt_nonneg _), Real.mul_self_sqrt (by positivity)]
  refine ⟨(s : ℂ) • Q, ((s⁻¹ : ℝ) : ℂ) • M, ?_, ⟨s ^ 2, by positivity, ?_⟩, ?_⟩
  · rw [hCM, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have : (s : ℂ) * star ((s⁻¹ : ℝ) : ℂ) = 1 := by
      rw [Complex.star_def, Complex.conj_ofReal, Complex.ofReal_inv]
      exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hspos.ne')
    rw [this, one_smul]
  · rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hQQ]
    congr 1
    rw [Complex.star_def, Complex.conj_ofReal]
    push_cast
    ring
  · have hQ2 := NormalForm.sum_normSq_eq_two Q hQQ
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal]
    simp only [← Finset.mul_sum]
    rw [← hN, hQ2, show N = 2 * (s ^ 2 * s ^ 2) by rw [hs4]; ring]
    field_simp

end NPT.Cert
