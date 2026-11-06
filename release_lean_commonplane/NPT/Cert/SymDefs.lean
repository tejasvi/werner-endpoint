/-
NPT.Cert.SymDefs — the symmetry actions used to make the moment coefficients orbit-constant: site
permutations (on the factor-major global index, with the dimension casts), entrywise conjugation, and
left/right multiplication by constant words.
-/
import NPT.Cert.Phys

open Matrix BigOperators Finset NPT.Brauer NPT.Cert.Sem

namespace NPT.Cert

variable {k d : ℕ}

/-- A site permutation extended to the factors (the auxiliary factor `last k` is fixed). -/
def sigHat (σ : Equiv.Perm (Fin k)) : Equiv.Perm (Fin (k + 1)) where
  toFun l := if h : l.val < k then (σ ⟨l.val, h⟩).castSucc else l
  invFun l := if h : l.val < k then (σ.symm ⟨l.val, h⟩).castSucc else l
  left_inv l := by
    by_cases h : l.val < k
    · simp [h]
    · simp [h]
  right_inv l := by
    by_cases h : l.val < k
    · simp [h]
    · simp [h]

lemma sigHat_lt (σ : Equiv.Perm (Fin k)) (l : Fin (k + 1)) : (sigHat σ l).val < k ↔ l.val < k := by
  by_cases h : l.val < k
  · simp [sigHat, h]
  · simp [sigHat, h]

lemma nf_sigHat (σ : Equiv.Perm (Fin k)) (l : Fin (k + 1)) : nf k d (sigHat σ l) = nf k d l := by
  simp only [nf, sigHat_lt]

/-- Site permutation of a global index: factor `l` reads factor `sigHat σ l`. -/
def permIdx (σ : Equiv.Perm (Fin k)) (i : GI (nf k d)) : GI (nf k d) :=
  fun l r => Fin.cast (nf_sigHat σ l) (i (sigHat σ l) r)

/-- Site permutation of a global operator. -/
def siteAct (σ : Equiv.Perm (Fin k)) (M : Matrix (GI (nf k d)) (GI (nf k d)) ℂ) :
    Matrix (GI (nf k d)) (GI (nf k d)) ℂ :=
  fun i j => M (permIdx σ i) (permIdx σ j)

/-- Entrywise complex conjugation. -/
def conjM {ι : Type*} (M : Matrix ι ι ℂ) : Matrix ι ι ℂ := M.map star

/-- The constant word `g` on every factor. -/
def VWc (g : Fin 24) : Matrix (GI (nf k d)) (GI (nf k d)) ℂ := VW (nf k d) 0 (fun _ => g)

/-- Site permutation of a two-column matrix (rows `x ↦ x ∘ σ`). -/
def permRows (σ : Equiv.Perm (Fin k)) (A : Matrix (Fin k → Fin d) (Fin 2) ℂ) :
    Matrix (Fin k → Fin d) (Fin 2) ℂ :=
  fun x α => A (x ∘ σ) α

end NPT.Cert
