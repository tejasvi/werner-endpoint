/-
NPT.CP3.Site — padded module families and site permutations of Gram forms.

Every module of the CP3 instance is padded by zero columns to dimension `dpad l` (3 on the sites, 6 on the auxiliary
factor), and every factor carries five modules (on the sites the fifth is zero). Then the Gram index `MI` and the tuple
type `Fin 5 → Fin 5` do not depend on the tuple. A site permutation `σ` acts on Gram forms of a site-symmetric operator
by the fixed permutation `permMI σ` of `MI` (`gram_site`); in particular the stabilizer of a tuple fixes its Gram form
(`gram_stab`).
-/
import NPT.CP3.Kron
import NPT.CP3.Phys

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem NPT.Cert.SymAvg

namespace NPT.CP3

/-- Padded module dimension: 3 on the sites, 6 on the auxiliary factor. -/
def dpad (l : Fin 5) : ℕ := if l.val < 4 then 3 else 6

/-- Padded module multi-index. -/
abbrev MI := (l : Fin 5) → Fin (dpad l)

lemma dpad_sigHat (σ : Equiv.Perm (Fin 4)) (l : Fin 5) : dpad (sigHat σ l) = dpad l := by
  unfold dpad
  by_cases h : l.val < 4
  · rw [if_pos ((sigHat_lt σ l).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((sigHat_lt σ l).1 h')), if_neg h]

/-- Site permutation of padded multi-indices (as `permIdx`). -/
def permMI (σ : Equiv.Perm (Fin 4)) (μ : MI) : MI := fun l => Fin.cast (dpad_sigHat σ l) (μ (sigHat σ l))

lemma nfC_site {l : Fin 5} (h : l.val < 4) : nfC l = 3 := by
  show (if l.val < 4 then 3 else 2) = 3
  rw [if_pos h]

lemma dpad_site {l : Fin 5} (h : l.val < 4) : dpad l = 3 := by unfold dpad; rw [if_pos h]

lemma dpad_aux {l : Fin 5} (h : ¬ l.val < 4) : dpad l = 6 := by unfold dpad; rw [if_neg h]

/-- Padded module data: five site modules (columns `Fin 3`) and five auxiliary modules (columns `Fin 6`). -/
structure PadData where
  Ms : Fin 5 → Matrix (Dig 3 4) (Fin 3) ℂ
  Ma : Fin 5 → Matrix (Dig 2 4) (Fin 6) ℂ

/-- Local module matrix of factor `l`. -/
def PadData.M (P : PadData) (l : Fin 5) (k : Fin 5) : Matrix (Dig (nfC l) 4) (Fin (dpad l)) ℂ :=
  fun x a => if h : l.val < 4 then P.Ms k (Fin.cast (nfC_site h) ∘ x) (Fin.cast (dpad_site h) a)
    else P.Ma k (Fin.cast (nfC_aux h) ∘ x) (Fin.cast (dpad_aux h) a)

/-- The module family of padded data (`NPT.CP3.ModFam` with tuple-independent dimensions). -/
abbrev PadData.fam (P : PadData) : ModFam nfC ℂ := ⟨fun _ => 5, fun l _ => dpad l, P.M⟩

lemma PadData.M_sigHat (P : PadData) (σ : Equiv.Perm (Fin 4)) (m k : Fin 5) (x : Dig (nfC m) 4) (a : Fin (dpad m)) :
    P.M (sigHat σ m) k (Fin.cast (nf_sigHat σ m).symm ∘ x) (Fin.cast (dpad_sigHat σ m).symm a) = P.M m k x a := by
  unfold PadData.M
  by_cases h : m.val < 4
  · have h' : (sigHat σ m).val < 4 := (sigHat_lt σ m).2 h
    rw [dif_pos h', dif_pos h]
    congr 1
    all_goals first
      | (funext r; apply Fin.ext; simp)
      | (apply Fin.ext; simp)
  · have h' : ¬ (sigHat σ m).val < 4 := fun h'' => h ((sigHat_lt σ m).1 h'')
    rw [dif_neg h', dif_neg h]
    congr 1
    all_goals first
      | (funext r; apply Fin.ext; simp)
      | (apply Fin.ext; simp)

lemma cast_index (i : GC) {m m' : Fin 5} (hm : m' = m) {n : ℕ} (h : nfC m' = n) (h' : nfC m = n) :
    Fin.cast h ∘ i m' = Fin.cast h' ∘ i m := by
  subst hm; rfl

/-- Naturality of the Kronecker module under site permutations. -/
lemma Jt_permIdx (P : PadData) (σ : Equiv.Perm (Fin 4)) (τ : Tup P.fam) (i : GC) (μ : MI) :
    Jt P.fam τ (permIdx σ.symm i) μ = Jt P.fam (fun l => τ (sigHat σ l)) i (permMI σ μ) := by
  simp only [Jt, kronR]
  symm
  refine Fintype.prod_equiv (sigHat σ) _ _ fun m => ?_
  show P.M m (τ (sigHat σ m)) (i m) (Fin.cast (dpad_sigHat σ m) (μ (sigHat σ m))) =
    P.M (sigHat σ m) (τ (sigHat σ m)) (fun r => Fin.cast (nf_sigHat σ.symm (sigHat σ m)) (i (sigHat σ.symm (sigHat σ m)) r))
      (μ (sigHat σ m))
  have hx : (fun r => Fin.cast (nf_sigHat σ.symm (sigHat σ m)) (i (sigHat σ.symm (sigHat σ m)) r)) =
      Fin.cast (nf_sigHat σ m).symm ∘ i m :=
    cast_index i (sigHat_symm_sigHat σ m) _ _
  have ha : μ (sigHat σ m) = Fin.cast (dpad_sigHat σ m).symm (Fin.cast (dpad_sigHat σ m) (μ (sigHat σ m))) := by
    apply Fin.ext; simp
  rw [hx]
  conv_rhs => rw [ha]
  exact (P.M_sigHat σ m (τ (sigHat σ m)) (i m) _).symm

lemma Jt_permIdx' (P : PadData) (σ : Equiv.Perm (Fin 4)) (τ : Tup P.fam) (i : GC) (μ : MI) :
    Jt P.fam τ i μ = Jt P.fam (fun l => τ (sigHat σ l)) (permIdx σ i) (permMI σ μ) := by
  rw [← Jt_permIdx, permIdx_symm]

/-- Reindexing a sum over all of `ι` by a permutation. The `Fintype` instance is an implicit argument, so it is unified
with the goal's instance instead of being synthesized (sums over the huge index `GC` must not require a kernel
comparison of two instance terms). -/
theorem sum_reindex {ι : Type*} {inst : Fintype ι} (e : ι ≃ ι) {f g : ι → ℂ} (h : ∀ x, f x = g (e x)) :
    @Finset.sum ι ℂ _ (@Finset.univ ι inst) f = @Finset.sum ι ℂ _ (@Finset.univ ι inst) g :=
  Fintype.sum_equiv e f g h

/-- `permIdx σ` as a permutation of the global index. -/
def permIdxE (σ : Equiv.Perm (Fin 4)) : GIx nfC ≃ GIx nfC := ⟨permIdx σ, permIdx σ.symm, permIdx_symm σ, permIdx_symm' σ⟩

/-- Site permutation of a global matrix, as EP3's `siteAct` but typed on `GC` (whose index is built on `Fin 5`, not
`Fin (4 + 1)`), so that products with `GC`-indexed modules carry one `Fintype` instance. -/
def siteActC (σ : Equiv.Perm (Fin 4)) (Y : Matrix GC GC ℂ) : Matrix GC GC ℂ := fun i j => Y (permIdx σ i) (permIdx σ j)

lemma gram_inner (P : PadData) (σ : Equiv.Perm (Fin 4)) (τ : Tup P.fam) (Y : Matrix GC GC ℂ) (μ : MI) (j : GC) :
    ((Jt P.fam τ)ᵀ * siteActC σ Y) μ j =
      ((Jt P.fam (fun l => τ (sigHat σ l)))ᵀ * Y) (permMI σ μ) (permIdx σ j) := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine sum_reindex (permIdxE σ) fun i => ?_
  rw [Matrix.transpose_apply, Matrix.transpose_apply, Jt_permIdx' P σ τ i μ]
  rfl

/-- **Site permutations of Gram forms.** -/
theorem gram_siteAct (P : PadData) (σ : Equiv.Perm (Fin 4)) (τ : Tup P.fam) (Y : Matrix GC GC ℂ) (μ ν : MI) :
    gram P.fam τ (siteActC σ Y) μ ν = gram P.fam (fun l => τ (sigHat σ l)) Y (permMI σ μ) (permMI σ ν) := by
  unfold gram
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine sum_reindex (permIdxE σ) fun j => ?_
  rw [gram_inner P σ τ Y μ j, Jt_permIdx' P σ τ j ν]
  rfl

/-- Site-symmetric operators: `gram (σ•τ)` is `gram τ` read through `permMI σ`. -/
theorem gram_site (P : PadData) (σ : Equiv.Perm (Fin 4)) (τ : Tup P.fam) {Y : Matrix GC GC ℂ}
    (hY : ∀ i j, Y (permIdx σ i) (permIdx σ j) = Y i j) (μ ν : MI) :
    gram P.fam τ Y μ ν = gram P.fam (fun l => τ (sigHat σ l)) Y (permMI σ μ) (permMI σ ν) := by
  have hs : siteActC σ Y = Y := funext fun i => funext fun j => hY i j
  conv_lhs => rw [← hs]
  exact gram_siteAct P σ τ Y μ ν

/-- The stabilizer of a tuple fixes its Gram form. -/
theorem gram_stab (P : PadData) (σ : Equiv.Perm (Fin 4)) (τ : Tup P.fam) (hτ : (fun l => τ (sigHat σ l)) = τ)
    {Y : Matrix GC GC ℂ} (hY : ∀ i j, Y (permIdx σ i) (permIdx σ j) = Y i j) (μ ν : MI) :
    gram P.fam τ Y μ ν = gram P.fam τ Y (permMI σ μ) (permMI σ ν) := by
  have h := gram_site P σ τ hY μ ν
  rw [hτ] at h
  exact h

/-- The physical projected moment is site-symmetric in the entrywise form used here. -/
lemma Yp_site_entry (σ : Equiv.Perm (Fin 4)) (A : MatA) (i j : GC) :
    Yp A (permIdx σ i) (permIdx σ j) = Yp A i j :=
  congrFun (congrFun (Yp_site σ A) i) j

end NPT.CP3
