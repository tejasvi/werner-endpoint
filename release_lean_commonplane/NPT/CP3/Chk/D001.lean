import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D001 — light part of variable 80

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0l080_ok : d0LightOK 80 = true := by decide +kernel

end NPT.CP3.Chk
