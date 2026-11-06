/-
NPT.Cert.EqMaps — linear maps on four-replica operators given by product kernels (partial traces over
a replica, the Stiefel contrast), their Kronecker action, Hilbert–Schmidt adjoints, and the transfer of
`span`-membership from local to global operators.
-/
import NPT.Cert.Glob
import NPT.Cert.Proj

open Matrix BigOperators Finset NPT.Brauer

namespace NPT.Cert

/-- A local kernel from `4`-replica to `mo`-replica operators. -/
abbrev LKer (n mo : ℕ) := Dig n mo → Dig n mo → Dig n 4 → Dig n 4 → ℂ

/-- Local application of a kernel. -/
def applyK {n mo : ℕ} (κ : LKer n mo) (M : Matrix (Dig n 4) (Dig n 4) ℂ) : Matrix (Dig n mo) (Dig n mo) ℂ :=
  fun i' j' => ∑ i, ∑ j, κ i' j' i j * M i j

/-- Adjoint kernel (from `mo`-replica back to `4`-replica operators). -/
def adjK {n mo : ℕ} (κ : LKer n mo) : Dig n 4 → Dig n 4 → Dig n mo → Dig n mo → ℂ :=
  fun i j i' j' => star (κ i' j' i j)

/-- Local application of an adjoint kernel. -/
def applyA {n mo : ℕ} (κ : LKer n mo) (N : Matrix (Dig n mo) (Dig n mo) ℂ) : Matrix (Dig n 4) (Dig n 4) ℂ :=
  fun i j => ∑ i', ∑ j', adjK κ i j i' j' * N i' j'

section Global

variable {L : Type*} [Fintype L] [DecidableEq L] {nf : L → ℕ} {mo : L → ℕ}

/-- Output index of a product kernel. -/
abbrev GO (nf mo : L → ℕ) := (l : L) → Dig (nf l) (mo l)

/-- Global application of a product kernel. -/
def applyG (κ : (l : L) → LKer (nf l) (mo l)) (M : Matrix (GI nf) (GI nf) ℂ) :
    Matrix (GO nf mo) (GO nf mo) ℂ :=
  fun i' j' => ∑ i : GI nf, ∑ j : GI nf, (∏ l, κ l (i' l) (j' l) (i l) (j l)) * M i j

/-- Global application of the adjoint of a product kernel. -/
def applyGA (κ : (l : L) → LKer (nf l) (mo l)) (N : Matrix (GO nf mo) (GO nf mo) ℂ) :
    Matrix (GI nf) (GI nf) ℂ :=
  fun i j => ∑ i' : GO nf mo, ∑ j' : GO nf mo, (∏ l, adjK (κ l) (i l) (j l) (i' l) (j' l)) * N i' j'

/-- `applyG` as a linear map. -/
def applyGL (κ : (l : L) → LKer (nf l) (mo l)) : Matrix (GI nf) (GI nf) ℂ →ₗ[ℂ] Matrix (GO nf mo) (GO nf mo) ℂ where
  toFun := applyG κ
  map_add' A B := by
    ext i' j'; simp only [applyG, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c A := by
    ext i' j'; simp only [applyG, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

/-- Sum over pairs of dependent functions as a product of local pair sums. -/
lemma sum_pair_prod {α : L → Type*} [∀ l, Fintype (α l)] [∀ l, DecidableEq (α l)]
    (g : (l : L) → α l → α l → ℂ) :
    ∑ i : (l : L) → α l, ∑ j : (l : L) → α l, ∏ l, g l (i l) (j l) = ∏ l, ∑ x, ∑ y, g l x y := by
  have h1 : ∀ l, (∑ x, ∑ y, g l x y) = ∑ p : α l × α l, g l p.1 p.2 :=
    fun l => (Fintype.sum_prod_type' _).symm
  simp only [h1]
  rw [Finset.prod_univ_sum (fun _ => Finset.univ) (fun l (p : α l × α l) => g l p.1 p.2),
    Fintype.piFinset_univ]
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow L α α) _ _ (fun q => rfl)).symm

/-- Reversal of a four-fold finite sum. -/
lemma sum4_rev {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (F : α → β → γ → δ → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ d, ∑ c, ∑ b, ∑ a, F a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ a, ∑ b, ∑ d, ∑ c, F a b c d := by
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ a, ∑ d, ∑ b, ∑ c, F a b c d := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ b, ∑ c, F a b c d := Finset.sum_comm
    _ = ∑ d, ∑ a, ∑ c, ∑ b, F a b c d := by
        exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ d, ∑ c, ∑ a, ∑ b, F a b c d := Finset.sum_congr rfl fun d _ => Finset.sum_comm
    _ = ∑ d, ∑ c, ∑ b, ∑ a, F a b c d := by
        exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- A product kernel acts factorwise on Kronecker products. -/
lemma applyG_kron (κ : (l : L) → LKer (nf l) (mo l)) (A : (l : L) → Matrix (Dig (nf l) 4) (Dig (nf l) 4) ℂ) :
    applyG κ (kron A) = kron fun l => applyK (κ l) (A l) := by
  ext i' j'
  simp only [applyG, kron, applyK, ← Finset.prod_mul_distrib]
  exact sum_pair_prod (fun l x y => κ l (i' l) (j' l) x y * A l x y)

lemma applyGA_kron (κ : (l : L) → LKer (nf l) (mo l))
    (B : (l : L) → Matrix (Dig (nf l) (mo l)) (Dig (nf l) (mo l)) ℂ) :
    applyGA κ (kron B) = kron fun l => applyA (κ l) (B l) := by
  ext i j
  simp only [applyGA, kron, applyA, ← Finset.prod_mul_distrib]
  exact sum_pair_prod (fun l x y => adjK (κ l) (i l) (j l) x y * B l x y)

/-- Hilbert–Schmidt adjointness of a product kernel. -/
lemma trace_applyG (κ : (l : L) → LKer (nf l) (mo l)) (N : Matrix (GO nf mo) (GO nf mo) ℂ)
    (Z : Matrix (GI nf) (GI nf) ℂ) :
    (Nᴴ * applyG κ Z).trace = ((applyGA κ N)ᴴ * Z).trace := by
  have lhs : (Nᴴ * applyG κ Z).trace =
      ∑ a, ∑ b, ∑ i, ∑ j, star (N b a) * ((∏ l, κ l (b l) (a l) (i l) (j l)) * Z i j) := by
    simp only [Matrix.trace, Matrix.diag, mul_apply, conjTranspose_apply, applyG, Finset.mul_sum]
  have rhs : ((applyGA κ N)ᴴ * Z).trace =
      ∑ j, ∑ i, ∑ b, ∑ a, (∏ l, κ l (b l) (a l) (i l) (j l)) * star (N b a) * Z i j := by
    simp only [Matrix.trace, Matrix.diag, mul_apply, conjTranspose_apply, applyGA, adjK, star_sum,
      star_mul', star_prod, star_star, Finset.sum_mul]
  rw [lhs, rhs, sum4_rev]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

/-- Kronecker products of members of spans lie in the span of the Kronecker products. -/
lemma kron_mem_span {ι : L → Type*} [∀ l, Fintype (ι l)] [∀ l, DecidableEq (ι l)]
    {W : L → Type*} [∀ l, Fintype (W l)] [∀ l, DecidableEq (W l)]
    (V : (l : L) → W l → Matrix (ι l) (ι l) ℂ) {A : (l : L) → Matrix (ι l) (ι l) ℂ}
    (hA : ∀ l, A l ∈ Submodule.span ℂ (Set.range (V l))) :
    kron A ∈ Submodule.span ℂ (Set.range fun u : (l : L) → W l => kron fun l => V l (u l)) := by
  choose c hc using fun l => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hA l)
  have hA' : A = fun l => ∑ w, c l w • V l w := funext fun l => (hc l).symm
  have e : kron A = ∑ u : (l : L) → W l, (∏ l, c l (u l)) • kron fun l => V l (u l) := by
    rw [hA']
    ext i j
    simp only [kron, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.prod_univ_sum (fun _ => Finset.univ), Fintype.piFinset_univ]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.prod_mul_distrib]
  rw [e]
  exact Submodule.sum_mem _ fun u _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, rfl⟩)

end Global

end NPT.Cert
