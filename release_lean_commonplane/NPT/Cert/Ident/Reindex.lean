/-
NPT.Cert.Ident.Reindex — flat indices of digit strings: `Sem.flat` (digit 0 most significant) is a
bijection `(Fin m → Fin n) ≃ range (n^m)`, with inverse `unflat` given by the digits `k / n^(m-1-s) % n`;
sums over digit strings become sums over `range (n^m)`.
-/
import NPT.Cert.Sem
import Mathlib.Algebra.BigOperators.Fin

open BigOperators Finset NPT.Cert.Sem

namespace NPT.Cert.Ident

/-- Digit `s` of `k` (base `n`, `m` digits, digit 0 most significant). -/
def dgt (n m k s : ℕ) : ℕ := k / n ^ (m - 1 - s) % n

/-- The digit string of `k`. -/
def unflat (n m : ℕ) [NeZero n] (k : ℕ) : Fin m → Fin n := fun s => ⟨dgt n m k s, Nat.mod_lt _ (NeZero.pos n)⟩

lemma flat_eq_ffe {n m : ℕ} (x : Fin m → Fin n) : flat x = (finFunctionFinEquiv (x ∘ Fin.rev) : ℕ) := by
  rw [finFunctionFinEquiv_apply, flat]
  exact (Fintype.sum_equiv Fin.revPerm _ _ fun s => by
    simp only [Fin.revPerm_apply, Function.comp_apply, Fin.rev_rev, Fin.val_rev]
    congr 2; omega)

lemma flat_lt {n m : ℕ} (x : Fin m → Fin n) : flat x < n ^ m := by
  rw [flat_eq_ffe]; exact (finFunctionFinEquiv _).isLt

lemma unflat_flat {n m : ℕ} [NeZero n] (x : Fin m → Fin n) : unflat n m (flat x) = x := by
  funext s
  apply Fin.ext
  have h := finFunctionFinEquiv_symm_apply_val (m := n) (n := m) (finFunctionFinEquiv (x ∘ Fin.rev)) (Fin.rev s)
  rw [Equiv.symm_apply_apply] at h
  simp only [Function.comp_apply, Fin.rev_rev, Fin.val_rev] at h
  simp only [unflat, dgt, flat_eq_ffe]
  rw [show m - 1 - s.val = m - (s.val + 1) by omega, ← h]

lemma flat_unflat {n m : ℕ} [NeZero n] (k : ℕ) (hk : k < n ^ m) : flat (unflat n m k) = k := by
  have key : unflat n m k = (finFunctionFinEquiv.symm (⟨k, hk⟩ : Fin (n ^ m))) ∘ Fin.rev := by
    funext s
    apply Fin.ext
    simp only [unflat, dgt, Function.comp_apply, finFunctionFinEquiv_symm_apply_val, Fin.val_rev]
    rw [show m - (s.val + 1) = m - 1 - s.val by omega]
  rw [key, flat_eq_ffe]
  have : ((finFunctionFinEquiv.symm (⟨k, hk⟩ : Fin (n ^ m))) ∘ Fin.rev) ∘ Fin.rev =
      finFunctionFinEquiv.symm (⟨k, hk⟩ : Fin (n ^ m)) := by
    funext s; simp [Fin.rev_rev]
  rw [this, Equiv.apply_symm_apply]

/-- Digit strings ≃ `Fin (n^m)` through `flat`. -/
def flatEquiv (n m : ℕ) [NeZero n] : (Fin m → Fin n) ≃ Fin (n ^ m) where
  toFun x := ⟨flat x, flat_lt x⟩
  invFun k := unflat n m k
  left_inv x := unflat_flat x
  right_inv k := Fin.ext (flat_unflat k k.isLt)

/-- Sums over digit strings as sums over flat indices. -/
lemma sum_fun_range {n m : ℕ} [NeZero n] {R : Type*} [AddCommMonoid R] (f : (Fin m → Fin n) → R) :
    ∑ x, f x = ∑ k ∈ range (n ^ m), f (unflat n m k) := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => f (unflat n m k))]
  exact Fintype.sum_equiv (flatEquiv n m) _ _ fun x => by simp [flatEquiv, unflat_flat]

end NPT.Cert.Ident
