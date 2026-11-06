/-
NPT.CP3.Fourier — the per-factor Fourier facts of the coordinate route (G2), in the form decided by the kernel:
compressions of the letters on modules as sums over the 81 (sites) or 16 (aux) digit strings, and the bridge from
entrywise identities of those sums to `FourierAt` (NPT.CP3.Kron).
-/
import NPT.CP3.Kron
import NPT.Cert.Ident.Reindex

open Matrix BigOperators Finset NPT.Cert NPT.Cert.Sem NPT.Cert.Ident NPT.Brauer

namespace NPT.CP3

section Compress

variable {R : Type*} [CommRing R]

/-- **Compression of a selection operator:** `(Aᵀ · SelOp σ τ · B)[a, b] = Σ_z A[z ∘ σ, a] B[z ∘ τ, b]`. -/
lemma compress_SelOp {n : ℕ} {α β : Type*} (A : Matrix (Dig n 4) α R) (B : Matrix (Dig n 4) β R)
    (σ τ : Fin 4 → Fin 4) (a : α) (b : β) :
    (Aᵀ * SelOp R n σ τ * B) a b = ∑ z : Dig n 4, A (z ∘ σ) a * B (z ∘ τ) b := by
  unfold SelOp
  rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun z _ => ?_
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single (z ∘ τ)]
  · rw [Finset.sum_eq_single (z ∘ σ)]
    · simp
    · intro x _ hx; simp [Ne.symm hx]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro y _ hy
    rw [Finset.sum_eq_zero]
    · simp
    · intro x _
      simp [Ne.symm hy]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Compression of a matrix unit:** `(Aᵀ · E_xy · B)[a, b] = A[x, a] B[y, b]`. -/
lemma compress_single {ι α β : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι α R) (B : Matrix ι β R)
    (x y : ι) (a : α) (b : β) : (Aᵀ * Matrix.single x y (1 : R) * B) a b = A x a * B y b := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single y]
  · rw [Finset.sum_eq_single x]
    · simp
    · intro u _ hu; simp [Ne.symm hu]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro v _ hv
    rw [Finset.sum_eq_zero]
    · simp
    · intro u _; simp [Ne.symm hv]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Sum over digit strings as a sum over flat indices (for kernel evaluation). -/
lemma sum_dig_range {n : ℕ} [NeZero n] {M : Type*} [AddCommMonoid M] (f : Dig n 4 → M) :
    ∑ z : Dig n 4, f z = ∑ k ∈ Finset.range (n ^ 4), f (unflat n 4 k) :=
  sum_fun_range f

end Compress

end NPT.CP3
