/-
NPT.K4.Traces — traces of the family moment operators: `tr X_f(a, b) = Π_r ‖χ_r‖²` over the four
replicas, so every family has trace `s⁴` when `‖a‖² = ‖b‖² = s` (the normal form gives `‖a‖ = ‖b‖`).
-/
import NPT.Cert.PhysObj

open Matrix BigOperators Finset NPT.Brauer NPT.Cert NPT.Cert.Sem NPT.Cert.Phys NPT.Cert.Phys.Obj

namespace NPT.K4

variable {k d : ℕ}

lemma nsq_chi (c : Fin 4) (a b : V1 k d → ℂ) (s : ℝ) (ha : nsq k d a = s) (hb : nsq k d b = s) :
    ∑ u, ((Complex.normSq (chi c a b u) : ℝ) : ℂ) = (s : ℂ) := by
  rw [← Complex.ofReal_sum]
  congr 1
  fin_cases c
  · simpa [chi, nsq] using ha
  · simpa [chi, nsq, Complex.star_def, Complex.normSq_conj] using ha
  · simpa [chi, nsq] using hb
  · simpa [chi, nsq, Complex.star_def, Complex.normSq_conj] using hb

/-- **Trace of a family moment operator**: `s⁴` when `‖a‖² = ‖b‖² = s`, for every family. -/
lemma trace_Xf (f : ℕ) (a b : V1 k d → ℂ) (s : ℝ) (ha : nsq k d a = s) (hb : nsq k d b = s) :
    (Xf f a b).trace = ((s ^ 4 : ℝ) : ℂ) := by
  have h1 : (Xf f a b).trace = ∑ i, ∏ r, ((Complex.normSq (chi (famPat f r) a b (repl i r)) : ℝ) : ℂ) := by
    simp only [Matrix.trace, Matrix.diag, Xf, vecMulVec_apply, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : patVec (famPat f) a b i * star (patVec (famPat f) a b i) =
        ((Complex.normSq (patVec (famPat f) a b i) : ℝ) : ℂ) := Complex.mul_conj _
    rw [e, patVec, map_prod, Complex.ofReal_prod]
  rw [h1, sum_GI]
  simp only [Fin.prod_univ_four, repl_symm]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  rw [nsq_chi _ a b s ha hb, nsq_chi _ a b s ha hb, nsq_chi _ a b s ha hb, nsq_chi _ a b s ha hb]
  push_cast
  ring

end NPT.K4

#print axioms NPT.K4.trace_Xf
