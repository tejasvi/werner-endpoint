/-
NPT.CP3.FinalD3 — the common-plane theorem from the active-block link `hF` alone (the D3 identities are discharged by
`NPT.CP3.ChecksD3`).
-/
import NPT.CP3.FinalPre
import NPT.CP3.ChecksD3

open Matrix BigOperators Finset
open scoped ComplexOrder

namespace NPT.CP3.Inst

open NPT.CP3 NPT.CP3.Data NPT.CP3.Chk NPT.CP3.Sem

/-- **The common-plane theorem from the block link.** -/
theorem q4_commonPlane_of_hF
    (hF : ∀ A : MatA, ∀ k < 302, (∑ i ∈ Finset.range 1331, yvec T A i • crm (Sem.Fmat k i)).PosSemidef)
    (U : Matrix (NPT.Idx (Fin 4) 3) (Fin 2) ℂ) (hU : Uᴴ * U = 1) (c : Matrix (Fin 2) (Fin 2) ℂ) :
    0 ≤ NPT.q (1 / 2) (U * c * Uᴴ) :=
  q4_commonPlane_of_D1D3 hF d3_obj d3_E U hU c

end NPT.CP3.Inst
