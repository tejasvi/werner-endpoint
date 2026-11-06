/-
NPT.CP3.Cert — the checked certificate facts (`NPT.CP3.Checks`: `ident_ok`, `psd_ok`, all kernel) in the form consumed
by `sound_real`.
-/
import NPT.CP3.Checks
import NPT.CP3.SoundR

open Matrix BigOperators Finset
open scoped ComplexOrder

namespace NPT.CP3

lemma part_eq_partH {m : ℕ} (c : ℕ) (Z : Matrix (Fin (2 * m)) (Fin (2 * m)) ℝ) : Sem.part c Z = partH c Z := by
  funext u v
  rfl

/-- The certificate identity (`ident_ok`) with the part of `SoundR`. -/
theorem cert_ident : ∀ c < 3, ∀ i < 1331, Sem.cvec c i = (∑ e ∈ range 146, Sem.Erow e i * Sem.lam c e) +
    ∑ k ∈ range 302, ∑ u : Fin (Sem.mOf k), ∑ v : Fin (Sem.mOf k), Sem.Fmat k i u v * partH c (Sem.Zmat k) u v := by
  intro c hc i hi
  have h := ident_ok c hc i hi
  simp only [part_eq_partH] at h
  exact h

/-- The multipliers `Z_k = N_k Y_k N_kᵀ` are symmetric. -/
theorem cert_zsym : ∀ k < 302, (Sem.Zmat k)ᵀ = Sem.Zmat k := fun k hk =>
  (nyn_facts (Sem.Nmat k) (Sem.Ymat k) (psd_ok k hk)).1

/-- The multipliers `Z_k` are positive semidefinite (over `ℂ`). -/
theorem cert_zpsd : ∀ k < 302, (crm (Sem.Zmat k)).PosSemidef := fun k hk =>
  (nyn_facts (Sem.Nmat k) (Sem.Ymat k) (psd_ok k hk)).2

end NPT.CP3
