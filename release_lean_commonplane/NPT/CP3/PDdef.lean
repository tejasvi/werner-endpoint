/-
NPT.CP3.PDdef — the padded module families of the certificate data and the intertwining of the cut-() modules.

`PD c` pads the site modules `siteJ[c][k]` (81 rows in `Sem.flat` order) to 3 columns and the auxiliary block
selections `auxBlocks[c][li]` to 6 columns. `πp` pads the cut-() intertwiners (`piSite`, `auxM[0]`). The intertwining
`Intertw (PD 0) πp` follows from the kernel row checks `interSite_sum`, `interAux_sum` and the decided relation
between `flatPerm` and composition with `pf g`.
-/
import NPT.CP3.SemD2
import NPT.CP3.Intw
import NPT.CP3.Bos

open Matrix BigOperators Finset NPT.Brauer NPT.Cert

namespace NPT.CP3.Inst

open NPT.CP3 NPT.CP3.Data NPT.CP3.Chk

/-- True dimension of site label `k` of cut `c`. -/
def sdim (c k : ℕ) : ℕ := (siteDims.getD c []).getD k 0

/-- Auxiliary block `li` of cut `c` (strings `z`). -/
def ablk (c li : ℕ) : List ℕ := (auxBlocks.getD c []).getD li []

/-- Padded site module (columns beyond the true dimension are `0`). -/
noncomputable def MsC (c : ℕ) (k : Fin 5) : Matrix (Dig 3 4) (Fin 3) ℂ :=
  fun x a => if a.val < sdim c k then ((mget ((siteJ.getD c []).getD k []) (Sem.flat x) a : ℤ) : ℂ) else 0

/-- Padded auxiliary block selection. -/
noncomputable def MaC (c : ℕ) (li : Fin 5) : Matrix (Dig 2 4) (Fin 6) ℂ :=
  fun z j => if j.val < (ablk c li).length then (if (ablk c li).getD j 0 = Sem.flat z then 1 else 0) else 0

/-- The padded module data of cut `c`. -/
noncomputable def PD (c : ℕ) : PadData := ⟨MsC c, MaC c⟩

/-- Padded site intertwiner. -/
noncomputable def πsite (k : Fin 5) (g : Fin 24) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun a b => if a.val < sdim 0 k ∧ b.val < sdim 0 k then ((mget ((piSite.getD k []).getD g []) a b : ℤ) : ℂ) else 0

/-- Padded auxiliary intertwiner. -/
noncomputable def πaux (li : Fin 5) (g : Fin 24) : Matrix (Fin 6) (Fin 6) ℂ :=
  fun a b => if a.val < (ablk 0 li).length ∧ b.val < (ablk 0 li).length then
    ((mget (((auxM.getD 0 []).getD li []).getD g []) a b : ℤ) : ℂ) else 0

/-- The padded cut-() intertwiners of every factor. -/
noncomputable def πp : (l : Fin 5) → Fin 5 → Fin 24 → Matrix (Fin (dpad l)) (Fin (dpad l)) ℂ :=
  fun l k g a b => if h : l.val < 4 then πsite k g (Fin.cast (dpad_site h) a) (Fin.cast (dpad_site h) b)
    else πaux k g (Fin.cast (dpad_aux h) a) (Fin.cast (dpad_aux h) b)

/-! ### Finite facts (decided) -/

lemma flat3_lt : ∀ x : Dig 3 4, Sem.flat x < 81 := by decide +kernel
lemma flat2_lt : ∀ z : Dig 2 4, Sem.flat z < 16 := by decide +kernel
lemma flatPerm3 : ∀ g : Fin 24, ∀ x : Dig 3 4, flatPerm 3 g (Sem.flat x) = Sem.flat (x ∘ pf g) := by decide +kernel
lemma flatPerm2 : ∀ g : Fin 24, ∀ z : Dig 2 4, flatPerm 2 g (Sem.flat z) = Sem.flat (z ∘ pf g) := by decide +kernel
lemma sdim_le : ∀ k : Fin 5, sdim 0 k ≤ 3 := by decide +kernel
lemma sdim4 : sdim 0 4 = 0 := by decide +kernel
lemma ablk_le : ∀ li : Fin 5, (ablk 0 li).length ≤ 6 := by decide +kernel

/-- Sum over the padded columns `Fin d` of terms vanishing beyond `e ≤ d`, as a sum over `range e`. -/
lemma sum_fin_range {d e : ℕ} (he : e ≤ d) (f : ℕ → ℂ) :
    ∑ b : Fin d, (if b.val < e then f b.val else 0) = ∑ b ∈ Finset.range e, f b := by
  rw [Fin.sum_univ_eq_sum_range (fun b => if b < e then f b else 0) d, ← Finset.sum_filter]
  congr 1
  ext b; simp [Finset.mem_filter, Finset.mem_range]; omega

end NPT.CP3.Inst
