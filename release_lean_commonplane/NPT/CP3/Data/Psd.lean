import NPT.CP3.Data.Psd00
import NPT.CP3.Data.Psd01

/-!
# NPT.CP3.Data.Psd — PBlock hints `(F, lrows, dvals)` for the integer matrices `D·Y` of the 302 blocks (`E = 0`, `UB = 2F`, no corrections).

Generated from the common-plane (d = 3) release certificate. Untrusted data: every property used downstream
is checked in `NPT.CP3.Chk*`. Conventions: `NPT.CP3.Data.Types`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option compiler.extract_closed false

namespace NPT.CP3.Data

/-- PBlock hints `(F, lrows, dvals)` for the integer matrices `D·Y` of the 302 blocks (`E = 0`, `UB = 2F`, no corrections). -/
def psdHint : List (Nat × List (List Int) × List Nat) := psd00 ++ psd01

end NPT.CP3.Data
