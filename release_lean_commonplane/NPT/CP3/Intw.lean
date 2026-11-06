/-
NPT.CP3.Intw — rows of `VG 0 p · M`: left multiplication by the permutation operator `V_p` permutes the rows,
`(V_p M)[x] = M[x ∘ p]`. Used to reduce the intertwining of the modules to finite row checks.
-/
import NPT.CP3.Phys

open Matrix BigOperators Finset NPT.Brauer NPT.Cert

namespace NPT.CP3

lemma VG_mul_apply_row {n : ℕ} {κ : Type*} (p : Fin 24) (M : Matrix (Dig n 4) κ ℂ) (x : Dig n 4) (a : κ) :
    (VG ℂ n 0 p * M) x a = M (x ∘ pf p) a := by
  rw [Matrix.mul_apply]
  simp only [Phys.SymAux.VG0_apply]
  rw [Finset.sum_eq_single (x ∘ pf p)]
  · have h : x = (x ∘ pf p) ∘ pinvf p := by
      funext s; simp [Function.comp, pf_pinvf]
    rw [if_pos h, one_mul]
  · intro y _ hy
    rw [if_neg, zero_mul]
    intro h
    apply hy
    funext s
    rw [h]
    simp [Function.comp, pinvf_pf]
  · intro h; exact absurd (Finset.mem_univ _) h

end NPT.CP3
