import NPT.CP3.Lit

/-!
# NPT.CP3.Data.Inter — cut-() site intertwiners

Generated from the common-plane (d = 3) release certificate. Untrusted data: every property used downstream
is checked in `NPT.CP3.Chk*`. Conventions: `NPT.CP3.Data.Types`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option compiler.extract_closed false

namespace NPT.CP3.Data

/-- `piSite[l][g]`: the cut-`()` intertwiner of site label `l`, `VG ℚ 3 0 g * J_l = J_l * piSite[l][g]` (integer). -/
def piSite : List (List (List (List Int))) := [[irows% "1", irows% "1", irows% "1", irows% "1", irows% "1", irows% "1", irows% "1", irows% "1", irows% "1", irows% "1", irows% "1", irows% "1", irows% "1", irows% "1", irows% "1", irows% "1", irows% "1", irows% "1", irows% "1", irows% "1", irows% "1", irows% "1", irows% "1", irows% "1"], [irows% "1 0 0 | 0 1 0 | 0 0 1", irows% "-1 -1 -1 | 0 1 0 | 0 0 1", irows% "0 1 0 | 1 0 0 | 0 0 1", irows% "0 1 0 | -1 -1 -1 | 0 0 1", irows% "-1 -1 -1 | 1 0 0 | 0 0 1", irows% "1 0 0 | -1 -1 -1 | 0 0 1", irows% "1 0 0 | 0 0 1 | 0 1 0", irows% "-1 -1 -1 | 0 0 1 | 0 1 0", irows% "0 1 0 | 0 0 1 | 1 0 0", irows% "0 1 0 | 0 0 1 | -1 -1 -1", irows% "-1 -1 -1 | 0 0 1 | 1 0 0", irows% "1 0 0 | 0 0 1 | -1 -1 -1", irows% "0 0 1 | 1 0 0 | 0 1 0", irows% "0 0 1 | -1 -1 -1 | 0 1 0", irows% "0 0 1 | 0 1 0 | 1 0 0", irows% "0 0 1 | 0 1 0 | -1 -1 -1", irows% "0 0 1 | -1 -1 -1 | 1 0 0", irows% "0 0 1 | 1 0 0 | -1 -1 -1", irows% "-1 -1 -1 | 1 0 0 | 0 1 0", irows% "1 0 0 | -1 -1 -1 | 0 1 0", irows% "-1 -1 -1 | 0 1 0 | 1 0 0", irows% "1 0 0 | 0 1 0 | -1 -1 -1", irows% "0 1 0 | -1 -1 -1 | 1 0 0", irows% "0 1 0 | 1 0 0 | -1 -1 -1"], [irows% "1 0 | 0 1", irows% "-1 -1 | 0 1", irows% "0 1 | 1 0", irows% "0 1 | -1 -1", irows% "-1 -1 | 1 0", irows% "1 0 | -1 -1", irows% "-1 -1 | 0 1", irows% "1 0 | 0 1", irows% "-1 -1 | 1 0", irows% "1 0 | -1 -1", irows% "0 1 | 1 0", irows% "0 1 | -1 -1", irows% "0 1 | -1 -1", irows% "0 1 | 1 0", irows% "1 0 | -1 -1", irows% "-1 -1 | 1 0", irows% "1 0 | 0 1", irows% "-1 -1 | 0 1", irows% "1 0 | -1 -1", irows% "-1 -1 | 1 0", irows% "0 1 | -1 -1", irows% "0 1 | 1 0", irows% "-1 -1 | 0 1", irows% "1 0 | 0 1"], [irows% "1 0 0 | 0 1 0 | 0 0 1", irows% "-1 0 1 | 0 -1 -1 | 0 0 1", irows% "-1 0 0 | 0 0 1 | 0 1 0", irows% "1 0 -1 | 0 0 1 | 0 -1 -1", irows% "1 1 0 | 0 -1 -1 | 0 1 0", irows% "-1 -1 0 | 0 1 0 | 0 -1 -1", irows% "0 1 0 | 1 0 0 | 0 0 -1", irows% "0 -1 -1 | -1 0 1 | 0 0 -1", irows% "0 0 1 | -1 0 0 | 0 -1 0", irows% "0 0 1 | 1 0 -1 | 0 1 1", irows% "0 -1 -1 | 1 1 0 | 0 -1 0", irows% "0 1 0 | -1 -1 0 | 0 1 1", irows% "0 -1 0 | 0 0 -1 | 1 0 0", irows% "0 1 1 | 0 0 -1 | -1 0 1", irows% "0 0 -1 | 0 -1 0 | -1 0 0", irows% "0 0 -1 | 0 1 1 | 1 0 -1", irows% "0 1 1 | 0 -1 0 | 1 1 0", irows% "0 -1 0 | 0 1 1 | -1 -1 0", irows% "1 1 0 | -1 0 1 | 1 0 0", irows% "-1 -1 0 | 1 0 0 | -1 0 1", irows% "-1 0 1 | 1 1 0 | -1 0 0", irows% "1 0 0 | -1 -1 0 | 1 0 -1", irows% "1 0 -1 | -1 0 0 | 1 1 0", irows% "-1 0 0 | 1 0 -1 | -1 -1 0"]]

end NPT.CP3.Data
