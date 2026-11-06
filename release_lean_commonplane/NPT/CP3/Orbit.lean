/-
NPT.CP3.Orbit — site permutations of the Kronecker lift, for padded module families (`NPT.CP3.Site`).

* `permMIE σ`: `permMI σ` as a permutation of `MI`; `reindexMI σ G` reads a Gram form through it.
* `gram_new`: for a site-symmetric operator and a tuple `new` with `new ∘ sigHat σ = τ`, the Gram form of `new` is the
  Gram form of `τ` read through `permMI σ` (`gram_site` of `NPT.CP3.Site`).
* `phiMap_site`: for site-uniform Fourier data `Φ`, `phiMap Φ τ' new (reindexMI σ G) = reindexMI σ (phiMap Φ (τ' ∘ sigHat σ) τ G)`.
  So the lift of a variable's Gram form is computed once and only re-read for the other tuples of its orbit.
-/
import NPT.CP3.Site
import NPT.CP3.Lift

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem NPT.Cert.SymAvg

namespace NPT.CP3

lemma MI_val_congr (μ : MI) {l l' : Fin 5} (h : l = l') : (μ l).val = (μ l').val := by subst h; rfl

lemma sigHat_sigHat_symm (σ : Equiv.Perm (Fin 4)) (l : Fin 5) : sigHat σ (sigHat σ.symm l) = l := by
  have h := sigHat_symm_sigHat σ.symm l
  rwa [Equiv.symm_symm] at h

lemma permMI_symm_permMI (σ : Equiv.Perm (Fin 4)) (μ : MI) : permMI σ.symm (permMI σ μ) = μ := by
  funext l
  apply Fin.ext
  simp only [permMI, Fin.coe_cast]
  exact MI_val_congr μ (sigHat_sigHat_symm σ l)

lemma permMI_permMI_symm (σ : Equiv.Perm (Fin 4)) (μ : MI) : permMI σ (permMI σ.symm μ) = μ := by
  funext l
  apply Fin.ext
  simp only [permMI, Fin.coe_cast]
  exact MI_val_congr μ (sigHat_symm_sigHat σ l)

/-- `permMI σ` as a permutation of `MI`. -/
def permMIE (σ : Equiv.Perm (Fin 4)) : MI ≃ MI :=
  ⟨permMI σ, permMI σ.symm, permMI_symm_permMI σ, permMI_permMI_symm σ⟩

/-- A Gram form read through `permMI σ`. -/
def reindexMI (σ : Equiv.Perm (Fin 4)) (G : Matrix MI MI ℂ) : Matrix MI MI ℂ := fun μ ν => G (permMI σ μ) (permMI σ ν)

lemma reindexMI_add (σ : Equiv.Perm (Fin 4)) (A B : Matrix MI MI ℂ) :
    reindexMI σ (A + B) = reindexMI σ A + reindexMI σ B := rfl
lemma reindexMI_smul (σ : Equiv.Perm (Fin 4)) (c : ℂ) (A : Matrix MI MI ℂ) :
    reindexMI σ (c • A) = c • reindexMI σ A := rfl
lemma reindexMI_zero (σ : Equiv.Perm (Fin 4)) : reindexMI σ (0 : Matrix MI MI ℂ) = 0 := rfl

lemma reindexMI_sum (σ : Equiv.Perm (Fin 4)) {ι : Type*} (s : Finset ι) (c : ι → ℂ) (A : ι → Matrix MI MI ℂ) :
    reindexMI σ (∑ i ∈ s, c i • A i) = ∑ i ∈ s, c i • reindexMI σ (A i) := by
  ext μ ν
  simp only [reindexMI, Matrix.sum_apply, Matrix.smul_apply]

/-- **Orbit tuples.** For a site-symmetric `Y` and `new ∘ sigHat σ = τ`, `gram new Y` is `gram τ Y` read through
`permMI σ`. -/
theorem gram_new (P : PadData) (σ : Equiv.Perm (Fin 4)) (new τ : Tup P.fam) (hnew : (fun l => new (sigHat σ l)) = τ)
    {Y : Matrix GC GC ℂ} (hY : ∀ i j, Y (permIdx σ i) (permIdx σ j) = Y i j) :
    gram P.fam new Y = reindexMI σ (gram P.fam τ Y) := by
  ext μ ν
  rw [gram_site P σ new hY μ ν, hnew]
  rfl

/-- Site uniformity of padded Fourier data: the coefficients of a factor `sigHat σ m` are those of `m`. -/
def PhiUniform {P0 P3 : PadData} (Φ : PhiF P0.fam P3.fam) : Prop :=
  ∀ (σ : Equiv.Perm (Fin 4)) (m κ : Fin 5) (a' b' : Fin (dpad m)) (la : Fin 5) (a b : Fin (dpad m)),
    Φ (sigHat σ m) κ (Fin.cast (dpad_sigHat σ m).symm a') (Fin.cast (dpad_sigHat σ m).symm b') la
      (Fin.cast (dpad_sigHat σ m).symm a) (Fin.cast (dpad_sigHat σ m).symm b) = Φ m κ a' b' la a b

lemma cast_permMI (σ : Equiv.Perm (Fin 4)) (μ : MI) (m : Fin 5) :
    Fin.cast (dpad_sigHat σ m).symm (permMI σ μ m) = μ (sigHat σ m) := by
  apply Fin.ext
  simp only [permMI, Fin.coe_cast]

/-- **Site permutations commute with the lift.** -/
theorem phiMap_site {P0 P3 : PadData} (Φ : PhiF P0.fam P3.fam) (hΦ : PhiUniform Φ) (σ : Equiv.Perm (Fin 4))
    (τ' : Tup P3.fam) (new τ : Tup P0.fam) (hnew : (fun l => new (sigHat σ l)) = τ) (G : Matrix MI MI ℂ) :
    phiMap Φ τ' new (reindexMI σ G) = reindexMI σ (phiMap Φ (fun l => τ' (sigHat σ l)) τ G) := by
  ext a' b'
  simp only [phiMap, reindexMI]
  refine Fintype.sum_equiv (permMIE σ) _ _ fun a => ?_
  refine Fintype.sum_equiv (permMIE σ) _ _ fun b => ?_
  simp only [permMIE, Equiv.coe_fn_mk]
  congr 1
  rw [← Equiv.prod_comp (sigHat σ)]
  refine Finset.prod_congr rfl fun m _ => ?_
  have hn : new (sigHat σ m) = τ m := congrFun hnew m
  rw [hn, ← cast_permMI σ a' m, ← cast_permMI σ b' m, ← cast_permMI σ a m, ← cast_permMI σ b m]
  exact hΦ σ m (τ' (sigHat σ m)) (permMI σ a' m) (permMI σ b' m) (τ m) (permMI σ a m) (permMI σ b m)

end NPT.CP3
