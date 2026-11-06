/-
NPT.CP3.Sound — soundness of the coordinate certificate.

The certificate is an exact identity in `N` coordinates (`cvec c = Eᵀ λ_c + Σ_k F_k*(part_c Z_k)`, `c = 0, 1, 2` for
`ca`, `cb`, `2 cab`) with every `Z_k` positive semidefinite. If a vector `y` makes every `Σ_i y_i F_k[i]` positive
semidefinite and annihilates every equality row, then the objective `Σ_i y_i (x² ca_i + y² cb_i + 2xy cab_i)` is
nonnegative: it equals `Σ_k Tr((Σ_i y_i F_k[i]) (x² Z₁₁ + y² Z₂₂ + xy (Z₁₂ + Z₁₂ᵀ)))`.
-/
import NPT.CP3.Phys

open Matrix BigOperators Finset
open scoped ComplexOrder

namespace NPT.CP3

/-- Rational matrices as complex matrices. -/
noncomputable def cqm {ι κ : Type*} (M : Matrix ι κ ℚ) : Matrix ι κ ℂ := M.map fun q => (q : ℂ)

/-- `0 ≤ Tr(A B)` for positive semidefinite `A`, `B`. -/
lemma trace_mul_psd_nonneg {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  set U : Matrix n n ℂ := (hA.1.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hspec : A = U * diagonal (fun i => ((hA.1.eigenvalues i : ℝ) : ℂ)) * star U := by
    rw [hU]
    conv_lhs => rw [hA.1.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, Function.comp_def]
  have hM : (star U * B * U).PosSemidef := by
    have := hB.conjTranspose_mul_mul_same U
    rwa [← Matrix.star_eq_conjTranspose] at this
  have htr : (A * B).trace = (diagonal (fun i => ((hA.1.eigenvalues i : ℝ) : ℂ)) * (star U * B * U)).trace := by
    conv_lhs => rw [hspec]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [htr]
  simp only [Matrix.trace, Matrix.diag, diagonal_mul]
  refine Finset.sum_nonneg fun i _ => mul_nonneg ?_ (hM.diag_nonneg)
  exact_mod_cast hA.eigenvalues_nonneg i

/-- Lower and upper index of the two blocks of a `2m × 2m` matrix. -/
def lo {m : ℕ} (u : Fin m) : Fin (2 * m) := ⟨u.val, by omega⟩
def hi {m : ℕ} (u : Fin m) : Fin (2 * m) := ⟨m + u.val, by omega⟩

/-- The parts of a `2m × 2m` certificate matrix: `Z₁₁`, `Z₂₂`, `Z₁₂ + Z₁₂ᵀ`. -/
def part {m : ℕ} (c : Fin 3) (Z : Matrix (Fin (2 * m)) (Fin (2 * m)) ℚ) : Matrix (Fin m) (Fin m) ℚ :=
  fun u v => if c = 0 then Z (lo u) (lo v) else if c = 1 then Z (hi u) (hi v) else Z (lo u) (hi v) + Z (lo v) (hi u)

/-- The block combination for the weights `(x, y)`. -/
noncomputable def zcomb {m : ℕ} (Z : Matrix (Fin (2 * m)) (Fin (2 * m)) ℚ) (x y : ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  fun u v => (x : ℂ) ^ 2 * (part 0 Z u v : ℂ) + (y : ℂ) ^ 2 * (part 1 Z u v : ℂ) + (x : ℂ) * y * (part 2 Z u v : ℂ)

/-- The selection matrix `M = (x I; y I)`. -/
noncomputable def selM (m : ℕ) (x y : ℝ) : Matrix (Fin (2 * m)) (Fin m) ℂ :=
  fun r u => if r = lo u then (x : ℂ) else if r = hi u then (y : ℂ) else 0

lemma lo_ne_hi {m : ℕ} (u v : Fin m) : lo u ≠ hi v := by
  intro h; have := congrArg Fin.val h; simp [lo, hi] at this; omega

lemma lo_inj {m : ℕ} {u v : Fin m} (h : lo u = lo v) : u = v := by
  apply Fin.ext; have := congrArg Fin.val h; simpa [lo] using this

lemma hi_inj {m : ℕ} {u v : Fin m} (h : hi u = hi v) : u = v := by
  apply Fin.ext; have := congrArg Fin.val h; simp [hi] at this; omega

lemma selM_col {m : ℕ} (x y : ℝ) (u : Fin m) (f : Fin (2 * m) → ℂ) :
    ∑ r, f r * selM m x y r u = f (lo u) * x + f (hi u) * y := by
  rw [Finset.sum_eq_add (lo u) (hi u) (lo_ne_hi u u)]
  · simp [selM, lo_ne_hi u u, (lo_ne_hi u u).symm]
  · intro r _ hr
    simp only [selM]
    rw [if_neg hr.1, if_neg hr.2, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `zcomb Z x y = Mᵀ Z M` for symmetric `Z`; hence it is positive semidefinite when `Z` is. -/
lemma zcomb_psd {m : ℕ} (Z : Matrix (Fin (2 * m)) (Fin (2 * m)) ℚ) (hZt : Zᵀ = Z) (hZ : (cqm Z).PosSemidef)
    (x y : ℝ) : (zcomb Z x y).PosSemidef := by
  have hsym : ∀ r s, Z r s = Z s r := fun r s => by
    have := congrFun (congrFun hZt s) r; simpa [Matrix.transpose_apply] using this
  have e : zcomb Z x y = (selM m x y)ᴴ * cqm Z * selM m x y := by
    ext u v
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [selM_col x y v]
    have h1 : ∀ s, ∑ r, star (selM m x y r u) * cqm Z r s = (x : ℂ) * cqm Z (lo u) s + (y : ℂ) * cqm Z (hi u) s := by
      intro s
      rw [Finset.sum_eq_add (lo u) (hi u) (lo_ne_hi u u)]
      · simp [selM, lo_ne_hi u u, (lo_ne_hi u u).symm, Complex.star_def, Complex.conj_ofReal]
      · intro r _ hr
        simp only [selM]
        rw [if_neg hr.1, if_neg hr.2, star_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [h1, h1]
    simp only [zcomb, part, cqm, Matrix.map_apply]
    simp only [show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
      if_true, if_false, ite_true, ite_false]
    rw [hsym (hi u) (lo v)]
    push_cast
    ring
  rw [e]
  exact hZ.conjTranspose_mul_mul_same _

/-- **Soundness of the coordinate certificate.** -/
theorem sound_coords {nC nK nE : ℕ} (m : Fin nK → ℕ)
    (F : (k : Fin nK) → Fin nC → Matrix (Fin (m k)) (Fin (m k)) ℚ) (Erow : Fin nE → Fin nC → ℚ)
    (lam : Fin 3 → Fin nE → ℚ) (cvec : Fin 3 → Fin nC → ℚ)
    (Z : (k : Fin nK) → Matrix (Fin (2 * m k)) (Fin (2 * m k)) ℚ)
    (hident : ∀ c i, cvec c i = ∑ e, Erow e i * lam c e + ∑ k, ∑ u, ∑ v, F k i u v * part c (Z k) u v)
    (hZt : ∀ k, (Z k)ᵀ = Z k) (hZ : ∀ k, (cqm (Z k)).PosSemidef)
    (y : Fin nC → ℂ) (hF : ∀ k, (∑ i, y i • cqm (F k i)).PosSemidef) (hE : ∀ e, ∑ i, y i * (Erow e i : ℂ) = 0)
    (x₁ x₂ : ℝ) :
    0 ≤ ∑ i, y i * ((x₁ : ℂ) ^ 2 * (cvec 0 i : ℂ) + (x₂ : ℂ) ^ 2 * (cvec 1 i : ℂ) + (x₁ : ℂ) * x₂ * (cvec 2 i : ℂ)) := by
  -- the value of the objective as a sum of block traces
  have hc : ∀ c : Fin 3, ∑ i, y i * (cvec c i : ℂ) =
      ∑ k, ∑ u, ∑ v, (∑ i, y i • cqm (F k i)) u v * (part c (Z k) u v : ℂ) := by
    intro c
    have hE0 : ∑ i, y i * ((∑ e, Erow e i * lam c e : ℚ) : ℂ) = 0 := by
      push_cast
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun e _ => ?_
      have := hE e
      calc ∑ i, y i * ((Erow e i : ℂ) * (lam c e : ℂ)) = (∑ i, y i * (Erow e i : ℂ)) * (lam c e : ℂ) := by
            rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun i _ => by ring
        _ = 0 := by rw [this, zero_mul]
    have hsplit : ∀ i, y i * (cvec c i : ℂ) = y i * ((∑ e, Erow e i * lam c e : ℚ) : ℂ) +
        ∑ k, ∑ u, ∑ v, y i * ((F k i u v : ℂ) * (part c (Z k) u v : ℂ)) := by
      intro i
      rw [hident c i]
      push_cast
      simp only [mul_add, Finset.mul_sum]
    simp only [hsplit, Finset.sum_add_distrib, hE0, zero_add]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [Matrix.sum_apply, Matrix.smul_apply, cqm, Matrix.map_apply, smul_eq_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hobj : ∑ i, y i * ((x₁ : ℂ) ^ 2 * (cvec 0 i : ℂ) + (x₂ : ℂ) ^ 2 * (cvec 1 i : ℂ) + (x₁ : ℂ) * x₂ * (cvec 2 i : ℂ)) =
      ∑ k, ((∑ i, y i • cqm (F k i)) * (zcomb (Z k) x₁ x₂)ᵀ).trace := by
    have e1 : ∑ i, y i * ((x₁ : ℂ) ^ 2 * (cvec 0 i : ℂ) + (x₂ : ℂ) ^ 2 * (cvec 1 i : ℂ) + (x₁ : ℂ) * x₂ * (cvec 2 i : ℂ)) =
        (x₁ : ℂ) ^ 2 * ∑ i, y i * (cvec 0 i : ℂ) + (x₂ : ℂ) ^ 2 * ∑ i, y i * (cvec 1 i : ℂ) +
          (x₁ : ℂ) * x₂ * ∑ i, y i * (cvec 2 i : ℂ) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [e1, hc 0, hc 1, hc 2]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, zcomb]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by ring
  rw [hobj]
  refine Finset.sum_nonneg fun k _ => ?_
  have hzt : (zcomb (Z k) x₁ x₂)ᵀ = zcomb (Z k) x₁ x₂ := by
    have hsym : ∀ r s, Z k r s = Z k s r := fun r s => by
      have := congrFun (congrFun (hZt k) s) r; simpa [Matrix.transpose_apply] using this
    ext u v
    simp only [Matrix.transpose_apply, zcomb, part]
    simp only [show (1 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
      if_true, if_false, ite_true, ite_false]
    rw [hsym (lo v) (lo u), hsym (hi v) (hi u)]
    ring
  rw [hzt]
  exact trace_mul_psd_nonneg (hF k) (zcomb_psd (Z k) (hZt k) (hZ k) x₁ x₂)

end NPT.CP3
