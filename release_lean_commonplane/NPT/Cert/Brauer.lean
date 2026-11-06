/-
NPT.Cert.Brauer — products of partially transposed permutation operators (walled Brauer
algebras), generic in the local dimension `n`.

A partially transposed permutation operator is a *selection operator*
`SelOp α β = Σ_x |x ∘ α⟩⟨x ∘ β|` (`x : Fin m → Fin n` ranges over all digit strings). Constrained sums
of matrix units — products of two selection operators, partial traces — are multiples `n^e` of a
selection operator; the reparametrisation is certified by finite combinatorial data (`GCert`), checkable
by `decide` independently of `n`.
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Module.NatInt
import Mathlib.LinearAlgebra.Matrix.ConjTranspose

open Matrix BigOperators Finset

namespace NPT.Brauer

variable {R : Type*} [CommSemiring R]
variable {n m e : ℕ}

/-- Digit strings: `m` slots, local dimension `n`. -/
abbrev Dig (n m : ℕ) := Fin m → Fin n

/-- Selection operator `Σ_x |x ∘ α⟩⟨x ∘ β|`. -/
def SelOp (R : Type*) [CommSemiring R] (n : ℕ) {m : ℕ} (α β : Fin m → Fin m) :
    Matrix (Dig n m) (Dig n m) R :=
  ∑ x : Dig n m, single (x ∘ α) (x ∘ β) (1 : R)

lemma single_mul_single_ite {ι : Type*} [Fintype ι] [DecidableEq ι] (i j k l : ι) :
    (single i j (1 : R) * single k l (1 : R) : Matrix ι ι R) =
      if j = k then single i l 1 else 0 := by
  by_cases h : j = k
  · subst h; simp
  · rw [ite_eq_right h, single_mul_single_of_ne (h := h)]

/-- Relabelling the digit variables by a permutation does not change a selection operator. -/
lemma SelOp_reindex (π : Equiv.Perm (Fin m)) (α β : Fin m → Fin m) :
    SelOp R n (π ∘ α) (π ∘ β) = SelOp R n α β := by
  unfold SelOp
  exact Fintype.sum_equiv (Equiv.arrowCongr π.symm (Equiv.refl _)) _ _ fun x => by
    congr 1

lemma SelOp_transpose (α β : Fin m → Fin m) : (SelOp R n α β)ᵀ = SelOp R n β α := by
  unfold SelOp
  rw [transpose_sum]
  exact Finset.sum_congr rfl fun x _ => transpose_single _ _ _

/-- General constrained sums. Variables `U`, constraints `E i = (u, u')` (meaning `v u = v u'`),
row digits `v ∘ ρ`, column digits `v ∘ κ`. -/
def CSum (R : Type*) [CommSemiring R] (n : ℕ) {U : Type*} [Fintype U] [DecidableEq U] {c m : ℕ}
    (E : Fin c → U × U) (ρ κ : Fin m → U) : Matrix (Dig n m) (Dig n m) R :=
  ∑ v : U → Fin n, if (∀ i, v (E i).1 = v (E i).2) then single (v ∘ ρ) (v ∘ κ) (1 : R) else 0

/-- Certificate that `CSum E ρ κ = n ^ e • SelOp α β` for every `n`: `σ` assigns every variable to
a result digit (`Sum.inl`) or a free loop (`Sum.inr`); `τ` picks representatives; `par`/`dep` is a
spanning forest of the constraint graph rooted at the representatives. -/
structure GCert {U : Type*} {c m : ℕ} (E : Fin c → U × U) (ρ κ : Fin m → U)
    (α β : Fin m → Fin m) (e : ℕ) where
  σ : U → Fin m ⊕ Fin e
  τ : Fin m ⊕ Fin e → U
  par : U → U
  dep : U → ℕ
  hA : ∀ i, σ (E i).1 = σ (E i).2
  hB : ∀ c, σ (τ c) = c
  hC1 : ∀ s, σ (ρ s) = Sum.inl (α s)
  hC2 : ∀ s, σ (κ s) = Sum.inl (β s)
  hD : ∀ v, v = τ (σ v) ∨ (dep (par v) < dep v ∧ σ (par v) = σ v ∧
      ∃ i, (v = (E i).1 ∧ par v = (E i).2) ∨ (v = (E i).2 ∧ par v = (E i).1))

section GCert

variable {U : Type*} {c : ℕ} {E : Fin c → U × U} {ρ κ : Fin m → U}
  {α β : Fin m → Fin m}

/-- Every solution of the constraints is constant along the certificate's forest. -/
lemma GCert.prop (C : GCert E ρ κ α β e) (v : U → Fin n) (hv : ∀ i, v (E i).1 = v (E i).2) :
    ∀ t, v t = v (C.τ (C.σ t)) := by
  suffices H : ∀ k, ∀ t, C.dep t = k → v t = v (C.τ (C.σ t)) from fun t => H _ t rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro t ht
    rcases C.hD t with h1 | ⟨hlt, hσ, i, hs⟩
    · conv_lhs => rw [h1]
    · have hedge : v t = v (C.par t) := by
        rcases hs with ⟨h2, h3⟩ | ⟨h2, h3⟩
        · rw [h3, h2]; exact hv i
        · rw [h3, h2]; exact (hv i).symm
      rw [hedge, ih _ (ht ▸ hlt) (C.par t) rfl, hσ]

/-- **Reparametrisation.** A certificate gives `CSum E ρ κ = n ^ e • SelOp α β`. -/
theorem GCert.csum_eq [Fintype U] [DecidableEq U] (C : GCert E ρ κ α β e) :
    CSum R n E ρ κ = ((n : R) ^ e) • SelOp R n α β := by
  unfold CSum
  rw [← Finset.sum_filter]
  have h1 : (∑ w : Fin m ⊕ Fin e → Fin n, single (w ∘ Sum.inl ∘ α) (w ∘ Sum.inl ∘ β) (1 : R)) =
      ∑ v ∈ Finset.univ.filter (fun v : U → Fin n => ∀ i, v (E i).1 = v (E i).2),
        single (v ∘ ρ) (v ∘ κ) (1 : R) := by
    refine Finset.sum_nbij' (fun w => w ∘ C.σ) (fun v => v ∘ C.τ) ?_ ?_ ?_ ?_ ?_
    · intro w _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply, C.hA,
        implies_true]
    · intro v _; exact Finset.mem_univ _
    · intro w _; funext c; simp only [Function.comp_apply, C.hB c]
    · intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
      funext t; exact (C.prop v hv t).symm
    · intro w _
      have ha : (w ∘ C.σ) ∘ ρ = w ∘ Sum.inl ∘ α := by
        funext s; simp only [Function.comp_apply, C.hC1 s]
      have hb : (w ∘ C.σ) ∘ κ = w ∘ Sum.inl ∘ β := by
        funext s; simp only [Function.comp_apply, C.hC2 s]
      rw [ha, hb]
  rw [← h1]
  rw [Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow _ _ _)
      (fun w : Fin m ⊕ Fin e → Fin n => single (w ∘ Sum.inl ∘ α) (w ∘ Sum.inl ∘ β) (1 : R))
      (fun p : (Fin m → Fin n) × (Fin e → Fin n) => single (p.1 ∘ α) (p.1 ∘ β) (1 : R))
      (fun w => rfl)]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
  rw [SelOp, Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

end GCert

/-- The product of two selection operators as a constrained sum over `Fin (m + m)` (first `m`
variables: left factor, last `m`: right factor). -/
lemma SelOp_mul_eq_csum (α1 β1 α2 β2 : Fin m → Fin m) :
    SelOp R n α1 β1 * SelOp R n α2 β2 =
      CSum R n (fun s => (Fin.castAdd m (β1 s), Fin.natAdd m (α2 s)))
        (Fin.castAdd m ∘ α1) (Fin.natAdd m ∘ β2) := by
  unfold SelOp CSum
  rw [Finset.sum_mul_sum]
  simp only [single_mul_single_ite]
  rw [← Fintype.sum_prod_type']
  -- `(x, y) ↦ Fin.append x y`
  refine Fintype.sum_equiv
    ((Equiv.sumArrowEquivProdArrow (Fin m) (Fin m) (Fin n)).symm.trans
      (Equiv.arrowCongr finSumFinEquiv (Equiv.refl _))) _ _ fun p => ?_
  obtain ⟨x, y⟩ := p
  have hx : ∀ s, (Equiv.arrowCongr finSumFinEquiv (Equiv.refl (Fin n))
      ((Equiv.sumArrowEquivProdArrow (Fin m) (Fin m) (Fin n)).symm (x, y))) (Fin.castAdd m s) = x s := by
    intro s
    simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply,
      finSumFinEquiv_symm_apply_castAdd, Equiv.sumArrowEquivProdArrow_symm_apply_inl]
  have hy : ∀ s, (Equiv.arrowCongr finSumFinEquiv (Equiv.refl (Fin n))
      ((Equiv.sumArrowEquivProdArrow (Fin m) (Fin m) (Fin n)).symm (x, y))) (Fin.natAdd m s) = y s := by
    intro s
    simp only [Equiv.arrowCongr_apply, Equiv.refl_apply, Function.comp_apply,
      finSumFinEquiv_symm_apply_natAdd, Equiv.sumArrowEquivProdArrow_symm_apply_inr]
  simp only [Equiv.trans_apply, Function.comp_def, hx, hy]
  by_cases hc : ∀ s, x (β1 s) = y (α2 s)
  · have hc' : (fun s => x (β1 s)) = fun s => y (α2 s) := funext hc
    rw [ite_eq_left hc, ite_eq_left hc']
  · have hc' : ¬((fun s => x (β1 s)) = fun s => y (α2 s)) := fun h => hc fun s => congrFun h s
    rw [ite_eq_right hc, ite_eq_right hc']

/-- **Product rule.** -/
theorem SelOp_mul_of_gcert {α1 β1 α2 β2 α3 β3 : Fin m → Fin m}
    (C : GCert (fun s => (Fin.castAdd m (β1 s), Fin.natAdd m (α2 s)))
      (Fin.castAdd m ∘ α1) (Fin.natAdd m ∘ β2) α3 β3 e) :
    SelOp R n α1 β1 * SelOp R n α2 β2 = ((n : R) ^ e) • SelOp R n α3 β3 := by
  rw [SelOp_mul_eq_csum, C.csum_eq]

end NPT.Brauer

#print axioms NPT.Brauer.SelOp_mul_of_gcert
