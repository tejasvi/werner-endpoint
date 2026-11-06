import NPT.CP3.Data.Vars00

/-!
# NPT.CP3.Data.Vars — All 175 sorted cut-() tuples: the 150 variable blocks (producer order), then the 25 tuples the producer skips (`W` without columns).

Generated from the common-plane (d = 3) release certificate. Untrusted data: every property used downstream
is checked in `NPT.CP3.Chk*`. Conventions: `NPT.CP3.Data.Types`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option compiler.extract_closed false

namespace NPT.CP3.Data

/-- All 175 sorted cut-() tuples: the 150 variable blocks (producer order), then the 25 tuples the producer skips (`W` without columns). -/
def vars : List VarB := vars00

end NPT.CP3.Data
