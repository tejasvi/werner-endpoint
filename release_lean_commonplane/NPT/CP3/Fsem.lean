/-
NPT.CP3.Fsem — the active blocks of the coordinate route as linear functions of the coordinates.

Abstract orbit data `D` (one entry per variable): a tuple `tup v`, coordinates `off v + j` (`j < m v`) carrying the
padded matrices `WSW v j = W_v S_j W_vᵀ`, and cosets `(new v c, perm v c)` with `new ∘ sigHat perm = tup`. If the `new`
tuples are pairwise distinct and the Gram forms of all other tuples vanish, then for a site-symmetric `Y ∈ A'_0` whose
variable Gram forms are `Σ_j y_(off+j) WSW j`:
* `fsem_sound3`: `Vᵀ J'_τ'ᵀ Y^{Γ₃} J'_τ' V = Σ_v Σ_j y_(off+j) Vᵀ (Σ_c (phiMap Φ (τ' ∘ sigHat perm) tup (WSW j)) read through
  permMI perm) V` (cut `(3,)`);
* `fsem_sound0`: `Vᵀ J_τᵀ Y J_τ V = Σ_v Σ_j y_(off+j) Vᵀ (Σ_{c : new = τ} (WSW j) read through permMI perm) V` (cut `()`);
* `sum_coord`: the double sums are `Σ_i y_i Fsem i` for the coordinate-indexed `Fsem i := coordSum`.
-/
import NPT.CP3.Orbit

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem NPT.Cert.SymAvg

namespace NPT.CP3

/-- Orbit data of the variables. -/
structure OrbitData where
  nv : ℕ
  tup : Fin nv → Fin 5 → Fin 5
  m : Fin nv → ℕ
  off : Fin nv → ℕ
  WSW : (v : Fin nv) → Fin (m v) → Matrix MI MI ℂ
  nc : Fin nv → ℕ
  new : (v : Fin nv) → Fin (nc v) → Fin 5 → Fin 5
  perm : (v : Fin nv) → Fin (nc v) → Equiv.Perm (Fin 4)

namespace OrbitData

variable (D : OrbitData)

/-- All cosets of all variables. -/
abbrev I := Σ v : Fin D.nv, Fin (D.nc v)

/-- The tuple of a coset. -/
def newOf (x : D.I) : Fin 5 → Fin 5 := D.new x.1 x.2

/-- Cosets are consistent: `new ∘ sigHat perm = tup`. -/
def CosOK : Prop := ∀ v c, (fun l => D.new v c (sigHat (D.perm v c) l)) = D.tup v

/-- Coordinate-indexed family: the entry of coordinate `i` (`0` if no variable owns it). -/
def coordSum {M : Type*} [AddCommMonoid M] (X : (v : Fin D.nv) → Fin (D.m v) → M) (i : ℕ) : M :=
  ∑ v, ∑ j : Fin (D.m v), if D.off v + j.val = i then X v j else 0

end OrbitData

lemma phiMap_finsum {P0 P3 : PadData} (Φ : PhiF P0.fam P3.fam) (τ' : Tup P3.fam) (τ : Tup P0.fam) {ι : Type*}
    (s : Finset ι) (G : ι → Matrix MI MI ℂ) : phiMap Φ τ' τ (∑ x ∈ s, G x) = ∑ x ∈ s, phiMap Φ τ' τ (G x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty]; exact phiMap_zero Φ τ' τ
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, phiMap_add, ih]

lemma reindexMI_finsum (σ : Equiv.Perm (Fin 4)) {ι : Type*} (s : Finset ι) (G : ι → Matrix MI MI ℂ) :
    reindexMI σ (∑ x ∈ s, G x) = ∑ x ∈ s, reindexMI σ (G x) := by
  ext μ ν
  simp only [reindexMI, Matrix.sum_apply]

/-- **Orbit decomposition of a Gram form.** -/
theorem gram_decomp (P : PadData) (D : OrbitData) (hcos : D.CosOK) (hinj : Function.Injective D.newOf)
    {Y : Matrix GC GC ℂ} (hsym : ∀ σ : Equiv.Perm (Fin 4), ∀ i j, Y (permIdx σ i) (permIdx σ j) = Y i j)
    (hout : ∀ τ : Tup P.fam, (∀ x, D.newOf x ≠ τ) → gram P.fam τ Y = 0) (τ : Tup P.fam) :
    gram P.fam τ Y = ∑ x : D.I, if D.newOf x = τ then reindexMI (D.perm x.1 x.2) (gram P.fam (D.tup x.1) Y) else 0 := by
  have key : ∀ x : D.I, (if D.newOf x = τ then reindexMI (D.perm x.1 x.2) (gram P.fam (D.tup x.1) Y) else 0) =
      if D.newOf x = τ then gram P.fam τ Y else 0 := by
    intro x
    split_ifs with h
    · rw [← h]
      exact (gram_new P (D.perm x.1 x.2) (D.newOf x) (D.tup x.1) (hcos x.1 x.2) (hsym _)).symm
    · rfl
  rw [Finset.sum_congr rfl fun x _ => key x]
  by_cases hτ : ∃ x, D.newOf x = τ
  · obtain ⟨x0, hx0⟩ := hτ
    rw [Finset.sum_eq_single x0]
    · rw [if_pos hx0]
    · intro x _ hx
      rw [if_neg]
      intro h
      exact hx (hinj (h.trans hx0.symm))
    · intro h
      exact absurd (Finset.mem_univ x0) h
  · push_neg at hτ
    rw [hout τ hτ]
    simp

/-- **The tuple sum of the lift over the orbits.** -/
theorem lift_orbit {P0 P3 : PadData} (Φ : PhiF P0.fam P3.fam) (hΦ : PhiUniform Φ) (D : OrbitData) (hcos : D.CosOK)
    (hinj : Function.Injective D.newOf) {Y : Matrix GC GC ℂ}
    (hsym : ∀ σ : Equiv.Perm (Fin 4), ∀ i j, Y (permIdx σ i) (permIdx σ j) = Y i j)
    (hout : ∀ τ : Tup P0.fam, (∀ x, D.newOf x ≠ τ) → gram P0.fam τ Y = 0) (τ' : Tup P3.fam) :
    ∑ τ : Tup P0.fam, phiMap Φ τ' τ (gram P0.fam τ Y) =
      ∑ x : D.I, reindexMI (D.perm x.1 x.2)
        (phiMap Φ (fun l => τ' (sigHat (D.perm x.1 x.2) l)) (D.tup x.1) (gram P0.fam (D.tup x.1) Y)) := by
  have e1 : ∀ τ : Tup P0.fam, phiMap Φ τ' τ (gram P0.fam τ Y) = ∑ x : D.I,
      if D.newOf x = τ then phiMap Φ τ' τ (reindexMI (D.perm x.1 x.2) (gram P0.fam (D.tup x.1) Y)) else 0 := by
    intro τ
    rw [gram_decomp P0 D hcos hinj hsym hout τ, phiMap_finsum]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs
    · rfl
    · exact phiMap_zero Φ τ' τ
  rw [Finset.sum_congr rfl fun τ _ => e1 τ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  exact phiMap_site Φ hΦ (D.perm x.1 x.2) τ' (D.newOf x) (D.tup x.1) (hcos x.1 x.2) _

/-- **Cut-`(3,)` blocks as functions of the coordinates.** -/
theorem fsem_sound3 {P0 P3 : PadData} (Φ : PhiF P0.fam P3.fam) (hΦ : PhiUniform Φ)
    (hfs : ∀ l : Fin 5, l.val < 4 → ∀ p : Fin 24, FourierAt Φ l (VG ℂ (nfC l) 0 p)) (hfa : ∀ X, FourierAt Φ 4 X)
    (D : OrbitData) (hcos : D.CosOK) (hinj : Function.Injective D.newOf) {Y : Matrix GC GC ℂ} (hY : Y ∈ spanA 0)
    (hsym : ∀ σ : Equiv.Perm (Fin 4), ∀ i j, Y (permIdx σ i) (permIdx σ j) = Y i j)
    (hout : ∀ τ : Tup P0.fam, (∀ x, D.newOf x ≠ τ) → gram P0.fam τ Y = 0) (y : ℕ → ℂ)
    (hcoord : ∀ v, gram P0.fam (D.tup v) Y = ∑ j : Fin (D.m v), y (D.off v + j.val) • D.WSW v j)
    (τ' : Tup P3.fam) {m' : ℕ} (V : Matrix MI (Fin m') ℂ) :
    Vᵀ * gram P3.fam τ' (gam3 Y) * V = ∑ v, ∑ j : Fin (D.m v), y (D.off v + j.val) •
      (Vᵀ * (∑ c : Fin (D.nc v), reindexMI (D.perm v c)
        (phiMap Φ (fun l => τ' (sigHat (D.perm v c) l)) (D.tup v) (D.WSW v j))) * V) := by
  rw [lift_b P0.fam P3.fam Φ hfs hfa hY τ', lift_orbit Φ hΦ D hcos hinj hsym hout τ', Fintype.sum_sigma]
  simp only [hcoord, phiMap_sum, reindexMI_sum, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.smul_sum]

/-- **Cut-`()` blocks as functions of the coordinates.** -/
theorem fsem_sound0 (P0 : PadData) (D : OrbitData) (hcos : D.CosOK) (hinj : Function.Injective D.newOf)
    {Y : Matrix GC GC ℂ} (hsym : ∀ σ : Equiv.Perm (Fin 4), ∀ i j, Y (permIdx σ i) (permIdx σ j) = Y i j)
    (hout : ∀ τ : Tup P0.fam, (∀ x, D.newOf x ≠ τ) → gram P0.fam τ Y = 0) (y : ℕ → ℂ)
    (hcoord : ∀ v, gram P0.fam (D.tup v) Y = ∑ j : Fin (D.m v), y (D.off v + j.val) • D.WSW v j)
    (τ : Tup P0.fam) {m' : ℕ} (V : Matrix MI (Fin m') ℂ) :
    Vᵀ * gram P0.fam τ Y * V = ∑ v, ∑ j : Fin (D.m v), y (D.off v + j.val) •
      (Vᵀ * (∑ c : Fin (D.nc v), if D.new v c = τ then reindexMI (D.perm v c) (D.WSW v j) else 0) * V) := by
  rw [gram_decomp P0 D hcos hinj hsym hout τ, Fintype.sum_sigma]
  have e : ∀ v (c : Fin (D.nc v)), (if D.newOf ⟨v, c⟩ = τ then reindexMI (D.perm v c) (gram P0.fam (D.tup v) Y) else 0) =
      ∑ j : Fin (D.m v), y (D.off v + j.val) • (if D.new v c = τ then reindexMI (D.perm v c) (D.WSW v j) else 0) := by
    intro v c
    rw [hcoord v]
    show (if D.new v c = τ then _ else 0) = _
    split_ifs with h
    · exact reindexMI_sum _ _ _ _
    · simp only [smul_zero, Finset.sum_const_zero]
  simp only [e, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.smul_sum]

/-- **Coordinate form.** If every coordinate of every variable is below `N`, the double sums are sums over the
coordinates `i < N` of `y_i · coordSum X i`. -/
theorem sum_coord (D : OrbitData) {M : Type*} [AddCommMonoid M] [Module ℂ M] (N : ℕ)
    (hN : ∀ v, D.off v + D.m v ≤ N) (y : ℕ → ℂ) (X : (v : Fin D.nv) → Fin (D.m v) → M) :
    ∑ i ∈ Finset.range N, y i • D.coordSum X i = ∑ v, ∑ j : Fin (D.m v), y (D.off v + j.val) • X v j := by
  simp only [OrbitData.coordSum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hmem : D.off v + j.val ∈ Finset.range N := by
    rw [Finset.mem_range]
    have := hN v
    omega
  rw [Finset.sum_eq_single (D.off v + j.val)]
  · rw [if_pos rfl]
  · intro i _ hi
    rw [if_neg (fun h => hi h.symm), smul_zero]
  · intro h
    exact absurd hmem h

end NPT.CP3
