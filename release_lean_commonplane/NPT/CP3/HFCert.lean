/-
NPT.CP3.HFCert — `hF` of `q4_commonPlane_of_linksR` for the certificate, with the native D1 check `nat_all`.
-/
import NPT.CP3.HF
import NPT.CP3.D1All

open Matrix BigOperators Finset
open scoped ComplexOrder

namespace NPT.CP3.Inst

open NPT.CP3

/-- **`hF` for the certificate.** -/
theorem hF_cert : ∀ A : MatA, ∀ k < 302, (∑ i ∈ range 1331, yvec T A i • crm (Sem.Fmat k i)).PosSemidef :=
  hF_of D1.nat_all

end NPT.CP3.Inst
