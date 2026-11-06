/-
NPT.CP3.SoundR — soundness of the coordinate certificate, for real data indexed by `ℕ` (the form of the checked data
in `NPT.CP3.Sem`): `ident` with the part `Z₁₂ + Z₂₁ᵀ`, symmetric `F_k[i]`, `Z_k = N_k Y_k N_kᵀ` with `Y_k ⪰ 0`.
-/
import NPT.CP3.Sound

open Matrix BigOperators Finset
open scoped ComplexOrder

namespace NPT.CP3

/-- Real matrices as complex matrices. -/
noncomputable def crm {ι κ : Type*} (M : Matrix ι κ ℝ) : Matrix ι κ ℂ := M.map fun r => (r : ℂ)

lemma crm_mul {ι κ μ : Type*} [Fintype κ] (A : Matrix ι κ ℝ) (B : Matrix κ μ ℝ) : crm (A * B) = crm A * crm B := by
  ext i j; simp [crm, Matrix.mul_apply]

lemma crm_conjTranspose {ι κ : Type*} (A : Matrix ι κ ℝ) : crm Aᴴ = (crm A)ᴴ := by
  ext i j; simp [crm, Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_ofReal]

/-- Real positive semidefinite matrices stay positive semidefinite over `ℂ`. -/
lemma psd_real_to_complex {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℝ} (hM : M.PosSemidef) :
    (crm M).PosSemidef := by
  set U : Matrix n n ℝ := (hM.1.eigenvectorUnitary : Matrix n n ℝ) with hU
  have hspec : M = U * diagonal (fun i => hM.1.eigenvalues i) * star U := by
    rw [hU]
    conv_lhs => rw [hM.1.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, Function.comp_def]
  set B : Matrix n n ℝ := diagonal (fun i => Real.sqrt (hM.1.eigenvalues i)) * star U with hB
  have hMB : M = Bᴴ * B := by
    rw [hspec, hB, conjTranspose_mul, diagonal_conjTranspose, Matrix.star_eq_conjTranspose,
      conjTranspose_conjTranspose]
    have hd : (star fun i => Real.sqrt (hM.1.eigenvalues i)) = fun i => Real.sqrt (hM.1.eigenvalues i) := by
      funext i; simp
    rw [hd]
    have hdd : diagonal (fun i => Real.sqrt (hM.1.eigenvalues i)) * diagonal (fun i => Real.sqrt (hM.1.eigenvalues i)) =
        diagonal (fun i => hM.1.eigenvalues i) := by
      rw [diagonal_mul_diagonal]
      congr 1
      funext i
      exact Real.mul_self_sqrt (hM.eigenvalues_nonneg i)
    rw [← hdd]
    simp only [Matrix.mul_assoc, Matrix.star_eq_conjTranspose]
  rw [hMB, crm_mul, crm_conjTranspose]
  exact posSemidef_conjTranspose_mul_self _

/-- `Z = N Y Nᵀ` with `Y ⪰ 0` (real) is symmetric and positive semidefinite over `ℂ`. -/
lemma nyn_facts {r m2 : ℕ} (N : Matrix (Fin m2) (Fin r) ℝ) (Y : Matrix (Fin r) (Fin r) ℝ) (hY : Y.PosSemidef) :
    (N * Y * Nᵀ)ᵀ = N * Y * Nᵀ ∧ (crm (N * Y * Nᵀ)).PosSemidef := by
  have hYt : Yᵀ = Y := by
    have h := hY.1
    unfold Matrix.IsHermitian at h
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  refine ⟨?_, ?_⟩
  · rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hYt, Matrix.mul_assoc]
  · have hNt : crm Nᵀ = (crm N)ᴴ := by
      rw [← crm_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    rw [crm_mul, crm_mul, hNt]
    exact (psd_real_to_complex hY).mul_mul_conjTranspose_same (crm N)

/-- The part of a `2m × 2m` matrix in the convention of the checked data: `Z₁₁`, `Z₂₂`, `Z₁₂ + Z₂₁ᵀ`. -/
def partH {m : ℕ} (c : ℕ) (Z : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun u v => if c = 0 then Z (lo u) (lo v) else if c = 1 then Z (hi u) (hi v) else Z (lo u) (hi v) + Z (hi v) (lo u)

/-- The block combination for the weights `(x, y)`, real data. -/
noncomputable def zcombR {m : ℕ} (Z : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) (x y : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  fun u v => (x : ℂ) ^ 2 * (Z (lo u) (lo v) : ℂ) + (y : ℂ) ^ 2 * (Z (hi u) (hi v) : ℂ) +
    (x : ℂ) * y * ((Z (lo u) (hi v) : ℂ) + (Z (lo v) (hi u) : ℂ))

lemma zcombR_psd {m : ℕ} (Z : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) (hZt : Zᵀ = Z) (hZ : (crm Z).PosSemidef)
    (x y : ℝ) : (zcombR Z x y).PosSemidef := by
  have hsym : ∀ r s, Z r s = Z s r := fun r s => by
    have := congrFun (congrFun hZt s) r; simpa [Matrix.transpose_apply] using this
  have e : zcombR Z x y = (selM m x y)ᴴ * crm Z * selM m x y := by
    ext u v
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [selM_col x y v]
    have h1 : ∀ s, ∑ r, star (selM m x y r u) * crm Z r s = (x : ℂ) * crm Z (lo u) s + (y : ℂ) * crm Z (hi u) s := by
      intro s
      rw [Finset.sum_eq_add (lo u) (hi u) (lo_ne_hi u u)]
      · simp [selM, lo_ne_hi u u, (lo_ne_hi u u).symm, Complex.star_def, Complex.conj_ofReal]
      · intro r _ hr
        simp only [selM]
        rw [if_neg hr.1, if_neg hr.2, star_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h1, h1]
    simp only [zcombR, crm, Matrix.map_apply]
    rw [hsym (hi u) (lo v)]
    ring
  rw [e]
  exact hZ.conjTranspose_mul_mul_same _

/-- **Soundness of the coordinate certificate, real data.** -/
theorem sound_real (nC nK nE : ℕ) (mOf : ℕ → ℕ) (Fmat : (k i : ℕ) → Matrix (Fin (mOf k)) (Fin (mOf k)) ℝ)
    (Erow lam cvec : ℕ → ℕ → ℝ) (Zmat : (k : ℕ) → Matrix (Fin (2 * mOf k)) (Fin (2 * mOf k)) ℝ)
    (hident : ∀ c < 3, ∀ i < nC, cvec c i = (∑ e ∈ range nE, Erow e i * lam c e) +
      ∑ k ∈ range nK, ∑ u : Fin (mOf k), ∑ v : Fin (mOf k), Fmat k i u v * partH c (Zmat k) u v)
    (hFsym : ∀ k i u v, Fmat k i u v = Fmat k i v u)
    (hZt : ∀ k < nK, (Zmat k)ᵀ = Zmat k) (hZ : ∀ k < nK, (crm (Zmat k)).PosSemidef)
    (y : ℕ → ℂ) (hF : ∀ k < nK, (∑ i ∈ range nC, y i • crm (Fmat k i)).PosSemidef)
    (hE : ∀ e < nE, ∑ i ∈ range nC, y i * (Erow e i : ℂ) = 0) (x₁ x₂ : ℝ) :
    0 ≤ ∑ i ∈ range nC, y i * ((x₁ : ℂ) ^ 2 * (cvec 0 i : ℂ) + (x₂ : ℂ) ^ 2 * (cvec 1 i : ℂ) +
      (x₁ : ℂ) * x₂ * (cvec 2 i : ℂ)) := by
  set Fy : (k : ℕ) → Matrix (Fin (mOf k)) (Fin (mOf k)) ℂ := fun k => ∑ i ∈ range nC, y i • crm (Fmat k i) with hFy
  have hFy_app : ∀ k u v, Fy k u v = ∑ i ∈ range nC, y i * (Fmat k i u v : ℂ) := by
    intro k u v
    simp only [hFy, Matrix.sum_apply, Matrix.smul_apply, crm, Matrix.map_apply, smul_eq_mul]
  have hc : ∀ c < 3, ∑ i ∈ range nC, y i * (cvec c i : ℂ) =
      ∑ k ∈ range nK, ∑ u : Fin (mOf k), ∑ v : Fin (mOf k), Fy k u v * (partH c (Zmat k) u v : ℂ) := by
    intro c hc3
    have hsplit : ∀ i ∈ range nC, y i * (cvec c i : ℂ) =
        (∑ e ∈ range nE, y i * (Erow e i : ℂ) * (lam c e : ℂ)) +
          ∑ k ∈ range nK, ∑ u : Fin (mOf k), ∑ v : Fin (mOf k),
            y i * (Fmat k i u v : ℂ) * (partH c (Zmat k) u v : ℂ) := by
      intro i hi
      rw [hident c hc3 i (Finset.mem_range.1 hi)]
      push_cast
      simp only [mul_add, Finset.mul_sum]
      congr 1
      · exact Finset.sum_congr rfl fun e _ => by ring
      · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    have hE0 : ∑ i ∈ range nC, ∑ e ∈ range nE, y i * (Erow e i : ℂ) * (lam c e : ℂ) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun e he => ?_
      rw [← Finset.sum_mul, hE e (Finset.mem_range.1 he), zero_mul]
    rw [hE0, zero_add, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hFy_app, Finset.sum_mul]
  have hpair : ∀ k (u v : Fin (mOf k)), Fy k u v = Fy k v u := by
    intro k u v; rw [hFy_app, hFy_app]
    exact Finset.sum_congr rfl fun i _ => by rw [hFsym]
  have hobj : ∑ i ∈ range nC, y i * ((x₁ : ℂ) ^ 2 * (cvec 0 i : ℂ) + (x₂ : ℂ) ^ 2 * (cvec 1 i : ℂ) +
        (x₁ : ℂ) * x₂ * (cvec 2 i : ℂ)) =
      ∑ k ∈ range nK, ∑ u : Fin (mOf k), ∑ v : Fin (mOf k), Fy k u v * zcombR (Zmat k) x₁ x₂ u v := by
    have e1 : ∑ i ∈ range nC, y i * ((x₁ : ℂ) ^ 2 * (cvec 0 i : ℂ) + (x₂ : ℂ) ^ 2 * (cvec 1 i : ℂ) +
          (x₁ : ℂ) * x₂ * (cvec 2 i : ℂ)) =
        (x₁ : ℂ) ^ 2 * ∑ i ∈ range nC, y i * (cvec 0 i : ℂ) + (x₂ : ℂ) ^ 2 * ∑ i ∈ range nC, y i * (cvec 1 i : ℂ) +
          (x₁ : ℂ) * x₂ * ∑ i ∈ range nC, y i * (cvec 2 i : ℂ) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, hc 0 (by norm_num), hc 1 (by norm_num), hc 2 (by norm_num)]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    -- the Z₂₁ᵀ term pairs like Z₁₂ᵀ because `Fy k` is symmetric
    have hswap : ∑ u : Fin (mOf k), ∑ v : Fin (mOf k), Fy k u v * (Zmat k (hi v) (lo u) : ℂ) =
        ∑ u : Fin (mOf k), ∑ v : Fin (mOf k), Fy k u v * (Zmat k (lo v) (hi u) : ℂ) := by
      have hsym : ∀ r s, Zmat k r s = Zmat k s r := fun r s => by
        have := congrFun (congrFun (hZt k (Finset.mem_range.1 hk)) s) r
        simpa [Matrix.transpose_apply] using this
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun u _ => ?_
      rw [hpair k u v, hsym (hi v) (lo u)]
    have expand : ∀ (f g h : Fin (mOf k) → Fin (mOf k) → ℂ),
        ∑ u : Fin (mOf k), ∑ v : Fin (mOf k), (f u v + g u v + h u v) =
          (∑ u, ∑ v, f u v) + (∑ u, ∑ v, g u v) + ∑ u, ∑ v, h u v := by
      intro f g h; simp only [Finset.sum_add_distrib]
    simp only [partH, show (1 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide,
      if_true, if_false, ite_true, ite_false, zcombR]
    push_cast
    have L : ∀ u v, (x₁ : ℂ) ^ 2 * (Fy k u v * (Zmat k (lo u) (lo v) : ℂ)) +
          (x₂ : ℂ) ^ 2 * (Fy k u v * (Zmat k (hi u) (hi v) : ℂ)) +
          (x₁ : ℂ) * x₂ * (Fy k u v * ((Zmat k (lo u) (hi v) : ℂ) + (Zmat k (hi v) (lo u) : ℂ))) =
        ((x₁ : ℂ) ^ 2 * (Fy k u v * (Zmat k (lo u) (lo v) : ℂ)) + (x₂ : ℂ) ^ 2 * (Fy k u v * (Zmat k (hi u) (hi v) : ℂ)) +
          (x₁ : ℂ) * x₂ * (Fy k u v * (Zmat k (lo u) (hi v) : ℂ))) + (x₁ : ℂ) * x₂ * (Fy k u v * (Zmat k (hi v) (lo u) : ℂ)) := by
      intro u v; ring
    have R : ∀ u v, Fy k u v * ((x₁ : ℂ) ^ 2 * (Zmat k (lo u) (lo v) : ℂ) + (x₂ : ℂ) ^ 2 * (Zmat k (hi u) (hi v) : ℂ) +
          (x₁ : ℂ) * x₂ * ((Zmat k (lo u) (hi v) : ℂ) + (Zmat k (lo v) (hi u) : ℂ))) =
        ((x₁ : ℂ) ^ 2 * (Fy k u v * (Zmat k (lo u) (lo v) : ℂ)) + (x₂ : ℂ) ^ 2 * (Fy k u v * (Zmat k (hi u) (hi v) : ℂ)) +
          (x₁ : ℂ) * x₂ * (Fy k u v * (Zmat k (lo u) (hi v) : ℂ))) + (x₁ : ℂ) * x₂ * (Fy k u v * (Zmat k (lo v) (hi u) : ℂ)) := by
      intro u v; ring
    simp only [L, R, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hswap]
  rw [hobj]
  refine Finset.sum_nonneg fun k hk => ?_
  have htr : ∑ u : Fin (mOf k), ∑ v : Fin (mOf k), Fy k u v * zcombR (Zmat k) x₁ x₂ u v =
      (Fy k * (zcombR (Zmat k) x₁ x₂)ᵀ).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  have hzt : (zcombR (Zmat k) x₁ x₂)ᵀ = zcombR (Zmat k) x₁ x₂ := by
    have hsym : ∀ r s, Zmat k r s = Zmat k s r := fun r s => by
      have := congrFun (congrFun (hZt k (Finset.mem_range.1 hk)) s) r; simpa [Matrix.transpose_apply] using this
    ext u v
    simp only [Matrix.transpose_apply, zcombR]
    rw [hsym (lo v) (lo u), hsym (hi v) (hi u)]
    ring
  rw [htr, hzt]
  exact trace_mul_psd_nonneg (hF k (Finset.mem_range.1 hk))
    (zcombR_psd (Zmat k) (hZt k (Finset.mem_range.1 hk)) (hZ k (Finset.mem_range.1 hk)) x₁ x₂)

end NPT.CP3
