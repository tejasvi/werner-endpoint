import NPT.CP3.Data.F00
import NPT.CP3.Data.F01
import NPT.CP3.Data.F02
import NPT.CP3.Data.F03
import NPT.CP3.Data.F04
import NPT.CP3.Data.F05
import NPT.CP3.Data.F06
import NPT.CP3.Data.F07
import NPT.CP3.Data.F08

/-!
# NPT.CP3.Data.F — block coefficients F, all coordinates

Generated from the common-plane (d = 3) release certificate. Untrusted data: every property used downstream
is checked in `NPT.CP3.Chk*`. Conventions: `NPT.CP3.Data.Types`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option compiler.extract_closed false

namespace NPT.CP3.Data

/-- Entry scale per cut (gcd of all entries of the cut). -/
def fScale : List Nat := nlist% "576 764411904"
/-- `Fc[i]`: one row `[k, f_0, …]` per active block `k` with `F_k[i] ≠ 0` (increasing `k`). -/
def Fc : List (List (List Int)) := Fc00 ++ Fc01 ++ Fc02 ++ Fc03 ++ Fc04 ++ Fc05 ++ Fc06 ++ Fc07 ++ Fc08

end NPT.CP3.Data
