import NPT.CP3.Data.Outs00

/-!
# NPT.CP3.Data.Outs — The 302 active output blocks, increasing producer index.

Generated from the common-plane (d = 3) release certificate. Untrusted data: every property used downstream
is checked in `NPT.CP3.Chk*`. Conventions: `NPT.CP3.Data.Types`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option compiler.extract_closed false

namespace NPT.CP3.Data

/-- The 302 active output blocks, increasing producer index. -/
def outs : List OutB := outs00

end NPT.CP3.Data
