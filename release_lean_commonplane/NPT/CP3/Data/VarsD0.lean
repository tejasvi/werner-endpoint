import NPT.CP3.Data.VarsD000

/-!
# NPT.CP3.Data.VarsD0 — D0 hints (left inverses, stabilizers, span coefficients) of the 175 tuples, same order as `vars`.

Generated from the common-plane (d = 3) release certificate. Untrusted data: every property used downstream
is checked in `NPT.CP3.Chk*`. Conventions: `NPT.CP3.Data.Types`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option compiler.extract_closed false

namespace NPT.CP3.Data

/-- D0 hints (left inverses, stabilizers, span coefficients) of the 175 tuples, same order as `vars`. -/
def d0 : List VarD0 := varsD000

end NPT.CP3.Data
