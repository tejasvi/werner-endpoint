import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D068 — light part of variable 146

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0l146_ok : d0LightOK 146 = true := by decide +kernel

end NPT.CP3.Chk
