import NPT.CP3.Data.ZW00
import NPT.CP3.Data.ZW01
import NPT.CP3.Data.ZW02
import NPT.CP3.Data.ZW03
import NPT.CP3.Data.ZW04
import NPT.CP3.Data.ZW05
import NPT.CP3.Data.ZW06

/-!
# NPT.CP3.Data.ZW — Per active block: the weighted upper triangles of the three parts of `N Yi Nᵀ` and of `N dYn Nᵀ`.

Generated from the common-plane (d = 3) release certificate. Untrusted data: every property used downstream
is checked in `NPT.CP3.Chk*`. Conventions: `NPT.CP3.Data.Types`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option compiler.extract_closed false

namespace NPT.CP3.Data

/-- Per active block: the weighted upper triangles of the three parts of `N Yi Nᵀ` and of `N dYn Nᵀ`. -/
def zw : List (List (List Int) × List (List Int)) := zW00 ++ zW01 ++ zW02 ++ zW03 ++ zW04 ++ zW05 ++ zW06

end NPT.CP3.Data
