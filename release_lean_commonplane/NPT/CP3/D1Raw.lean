/-
NPT.CP3.D1Raw — the certificate data as the input `raw` of the native D1 check (Mathlib-free).
-/
import NPT.CP3.D1Core
import NPT.CP3.Data.Vars
import NPT.CP3.Data.Outs
import NPT.CP3.Data.F
import NPT.CP3.Data.Site
import NPT.CP3.Data.AuxMaps

namespace NPT.CP3.D1

open NPT.CP3.Data

/-- The certificate data as the input of the native check. -/
def raw : Raw := ⟨vars, outs, Fc, fScale, phiNum, siteOff, auxOff, auxDest⟩

end NPT.CP3.D1
