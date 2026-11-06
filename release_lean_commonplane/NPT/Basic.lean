/-
NPT.Basic — definitions for the Werner k-copy endpoint problem.

Copies are indexed by an arbitrary finite type `ι` (for the main theorems `ι = Fin k`);
each copy is `ℂ^d`, with basis indexed by `Fin d`. An operator on the copies is a matrix
indexed by `ι → Fin d`.

* `ptrace J C` : the partial trace of `C` over the copies in `J`, returned as an operator on
  all copies that is supported on the "corner" where the indices in `J` are `0`
  (so `frobSq (ptrace J C) = ‖Tr_J C‖_F²` for the usual reduced operator `Tr_J C`).
* `q t C = ∑_{J ⊆ ι} (-t)^{|J|} ‖Tr_J C‖_F²` (Costa Rico's form).
* `RankLE2 C` : `C = A Bᴴ` with `A B` having two columns.
* `EP ι d t` : `q t C ≥ 0` for every rank-≤2 operator `C` on the copies `ι` of `ℂ^d`.
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open Matrix BigOperators Finset

namespace NPT

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {d : ℕ}

/-- Multi-indices of the copies `ι` of `ℂ^d`. -/
abbrev Idx (ι : Type*) (d : ℕ) := ι → Fin d

/-- Operators on the copies `ι` of `ℂ^d`. -/
abbrev Op (ι : Type*) (d : ℕ) := Matrix (Idx ι d) (Idx ι d) ℂ

/-- Overwrite the coordinates of `x` in `J` by those of `z`. -/
def upd (J : Finset ι) (x : Idx ι d) (z : J → Fin d) : Idx ι d :=
  fun i => if h : i ∈ J then z ⟨i, h⟩ else x i

/-- `x` vanishes on the copies in `J`. -/
def ZeroOn [NeZero d] (J : Finset ι) (x : Idx ι d) : Prop := ∀ i ∈ J, x i = 0

instance [NeZero d] (J : Finset ι) (x : Idx ι d) : Decidable (ZeroOn J x) := by
  unfold ZeroOn; infer_instance

/-- Partial trace over the copies in `J`, padded by `|0⟩⟨0|` on `J`. -/
def ptrace [NeZero d] (J : Finset ι) (C : Op ι d) : Op ι d := fun x y =>
  if ZeroOn J x ∧ ZeroOn J y then ∑ z : J → Fin d, C (upd J x z) (upd J y z) else 0

/-- Squared Frobenius norm. -/
def frobSq (A : Op ι d) : ℝ := ∑ x, ∑ y, Complex.normSq (A x y)

/-- Costa Rico's form `q_k(t, C) = ∑_J (-t)^{|J|} ‖Tr_J C‖²`. -/
def q [NeZero d] (t : ℝ) (C : Op ι d) : ℝ :=
  ∑ J : Finset ι, (-t) ^ J.card * frobSq (ptrace J C)

/-- Rank at most two, as a factorization `C = A Bᴴ` with two columns. -/
def RankLE2 (C : Op ι d) : Prop :=
  ∃ A B : Matrix (Idx ι d) (Fin 2) ℂ, C = A * Bᴴ

/-- The endpoint property: `q t C ≥ 0` for all rank-≤2 operators on the copies `ι` of `ℂ^d`. -/
def EP (ι : Type*) [Fintype ι] [DecidableEq ι] (d : ℕ) [NeZero d] (t : ℝ) : Prop :=
  ∀ C : Op ι d, RankLE2 C → 0 ≤ q t C

lemma ptrace_apply_pos [NeZero d] {J : Finset ι} {C : Op ι d} {x y : Idx ι d}
    (h : ZeroOn J x ∧ ZeroOn J y) : ptrace J C x y = ∑ z : J → Fin d, C (upd J x z) (upd J y z) := by
  show (if ZeroOn J x ∧ ZeroOn J y then _ else _) = _
  rw [if_pos h]

lemma ptrace_apply_neg [NeZero d] {J : Finset ι} {C : Op ι d} {x y : Idx ι d}
    (h : ¬ (ZeroOn J x ∧ ZeroOn J y)) : ptrace J C x y = 0 := by
  show (if ZeroOn J x ∧ ZeroOn J y then _ else _) = _
  rw [if_neg h]

lemma frobSq_nonneg (A : Op ι d) : 0 ≤ frobSq A := by
  unfold frobSq
  exact Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => Complex.normSq_nonneg _

/-- The `J = ∅` term: no copy is traced. -/
lemma ptrace_empty [NeZero d] (C : Op ι d) : ptrace (∅ : Finset ι) C = C := by
  funext x y
  have hx : ZeroOn (∅ : Finset ι) x := by intro i hi; simp at hi
  have hy : ZeroOn (∅ : Finset ι) y := by intro i hi; simp at hi
  simp only [ptrace, hx, hy, and_self, ite_true]
  have hupd : ∀ (w : Idx ι d) (z : (∅ : Finset ι) → Fin d), upd ∅ w z = w := by
    intro w z; funext i; simp [upd]
  simp [hupd]

/-- For `t ≤ 0` every term of `q` is nonnegative. -/
lemma q_nonneg_of_nonpos [NeZero d] {t : ℝ} (ht : t ≤ 0) (C : Op ι d) : 0 ≤ q t C := by
  unfold q
  refine Finset.sum_nonneg fun J _ => mul_nonneg ?_ (frobSq_nonneg _)
  exact pow_nonneg (by linarith) _

end NPT
