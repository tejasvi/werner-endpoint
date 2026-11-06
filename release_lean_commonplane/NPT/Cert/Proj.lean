/-
NPT.Cert.Proj — Hilbert–Schmidt projections onto subspaces of matrices, and intertwining.

`IsProj K X Y` says that `Y ∈ K` reproduces the Hilbert–Schmidt inner products `Tr(Zᴴ X)` of `X`
against `K`. Such a `Y` exists for every subspace (orthogonal projection in `EuclideanSpace ℂ (m × m)`)
and is unique. A linear map `T` with `T K ⊆ K'` whose adjoint maps `K'` into `K` sends projections to
projections (`IsProj.map`); in particular `T X = 0 ⟹ T Y = 0`.
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Matrix.PosDef

open Matrix BigOperators Finset
open scoped ComplexOrder

namespace NPT.Cert

variable {m m' : Type*} [Fintype m] [Fintype m']

/-- `Y` is the Hilbert–Schmidt projection of `X` onto `K`. -/
def IsProj (K : Submodule ℂ (Matrix m m ℂ)) (X Y : Matrix m m ℂ) : Prop :=
  Y ∈ K ∧ ∀ Z ∈ K, (Zᴴ * Y).trace = (Zᴴ * X).trace

/-- Flattening a matrix into `EuclideanSpace ℂ (m × m)`. -/
noncomputable def vecL : Matrix m m ℂ →ₗ[ℂ] EuclideanSpace ℂ (m × m) where
  toFun A := WithLp.toLp 2 (fun ij => A ij.1 ij.2)
  map_add' A B := by ext ij; simp
  map_smul' c A := by ext ij; simp

lemma inner_vecL (A B : Matrix m m ℂ) :
    inner ℂ (vecL A) (vecL B) = (Aᴴ * B).trace := by
  simp only [vecL, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply, RCLike.inner_apply,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [mul_comm]

lemma trace_conjTranspose_mul_self_eq_zero' {A : Matrix m m ℂ} (h : (Aᴴ * A).trace = 0) : A = 0 :=
  Matrix.conjTranspose_mul_self_eq_zero.1
    ((Matrix.PosSemidef.trace_eq_zero_iff (Matrix.posSemidef_conjTranspose_mul_self _)).1 h)

/-- Existence of the Hilbert–Schmidt projection onto any subspace. -/
theorem exists_isProj (K : Submodule ℂ (Matrix m m ℂ)) (X : Matrix m m ℂ) : ∃ Y, IsProj K X Y := by
  let K' : Submodule ℂ (EuclideanSpace ℂ (m × m)) := K.map vecL
  have hv : K'.starProjection (vecL X) ∈ K' := K'.starProjection_apply_mem _
  obtain ⟨Y, hY, hYv⟩ := Submodule.mem_map.1 hv
  refine ⟨Y, hY, fun Z hZ => ?_⟩
  have h0 := K'.starProjection_inner_eq_zero (vecL X) (vecL Z) (Submodule.mem_map_of_mem hZ)
  rw [← hYv, ← map_sub, inner_vecL] at h0
  have h1 : (Zᴴ * (X - Y)).trace = 0 := by
    have e : (Zᴴ * (X - Y)).trace = star (((X - Y)ᴴ * Z).trace) := by
      rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [e, h0, star_zero]
  rw [Matrix.mul_sub, Matrix.trace_sub, sub_eq_zero] at h1
  exact h1.symm

/-- Uniqueness of the projection. -/
theorem IsProj.unique {K : Submodule ℂ (Matrix m m ℂ)} {X Y₁ Y₂ : Matrix m m ℂ}
    (h₁ : IsProj K X Y₁) (h₂ : IsProj K X Y₂) : Y₁ = Y₂ := by
  have hD : Y₁ - Y₂ ∈ K := K.sub_mem h₁.1 h₂.1
  have h : ((Y₁ - Y₂)ᴴ * (Y₁ - Y₂)).trace = 0 := by
    rw [Matrix.mul_sub, Matrix.trace_sub, h₁.2 _ hD, h₂.2 _ hD, sub_self]
  exact sub_eq_zero.1 (trace_conjTranspose_mul_self_eq_zero' h)

/-- Projections are linear in the projected matrix. -/
theorem IsProj.add {K : Submodule ℂ (Matrix m m ℂ)} {X₁ X₂ Y₁ Y₂ : Matrix m m ℂ}
    (h₁ : IsProj K X₁ Y₁) (h₂ : IsProj K X₂ Y₂) : IsProj K (X₁ + X₂) (Y₁ + Y₂) :=
  ⟨K.add_mem h₁.1 h₂.1, fun Z hZ => by
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.trace_add, Matrix.trace_add, h₁.2 Z hZ, h₂.2 Z hZ]⟩

theorem IsProj.smul {K : Submodule ℂ (Matrix m m ℂ)} {X Y : Matrix m m ℂ}
    (h : IsProj K X Y) (c : ℂ) : IsProj K (c • X) (c • Y) :=
  ⟨K.smul_mem c h.1, fun Z hZ => by
    rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, h.2 Z hZ]⟩

theorem IsProj.sum {K : Submodule ℂ (Matrix m m ℂ)} {ι : Type*} (s : Finset ι)
    {X Y : ι → Matrix m m ℂ} (h : ∀ i ∈ s, IsProj K (X i) (Y i)) :
    IsProj K (∑ i ∈ s, X i) (∑ i ∈ s, Y i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨K.zero_mem, fun Z _ => by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- **Intertwining.** If `T` maps `K` into `K'` and its Hilbert–Schmidt adjoint maps `K'` into `K`,
then `T` maps the projection of `X` onto `K` to the projection of `T X` onto `K'`. -/
theorem IsProj.map {K : Submodule ℂ (Matrix m m ℂ)} {K' : Submodule ℂ (Matrix m' m' ℂ)}
    (T : Matrix m m ℂ →ₗ[ℂ] Matrix m' m' ℂ) (hT : ∀ Y ∈ K, T Y ∈ K')
    (hadj : ∀ N ∈ K', ∃ M ∈ K, ∀ Z, (Nᴴ * T Z).trace = (Mᴴ * Z).trace)
    {X Y : Matrix m m ℂ} (h : IsProj K X Y) : IsProj K' (T X) (T Y) := by
  refine ⟨hT Y h.1, fun N hN => ?_⟩
  obtain ⟨M, hM, hMN⟩ := hadj N hN
  rw [hMN, hMN, h.2 M hM]

/-- A projection of a matrix annihilated by an intertwining map is annihilated. -/
theorem IsProj.map_eq_zero {K : Submodule ℂ (Matrix m m ℂ)} {K' : Submodule ℂ (Matrix m' m' ℂ)}
    (T : Matrix m m ℂ →ₗ[ℂ] Matrix m' m' ℂ) (hT : ∀ Y ∈ K, T Y ∈ K')
    (hadj : ∀ N ∈ K', ∃ M ∈ K, ∀ Z, (Nᴴ * T Z).trace = (Mᴴ * Z).trace)
    {X Y : Matrix m m ℂ} (h : IsProj K X Y) (hX : T X = 0) : T Y = 0 := by
  have h' := h.map T hT hadj
  rw [hX] at h'
  exact h'.unique ⟨K'.zero_mem, fun Z _ => by simp⟩

end NPT.Cert
