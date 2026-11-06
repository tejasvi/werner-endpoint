import NPT.CP3.Chk.D2Defs

/-!
# NPT.CP3.Chk.Inter — the cut-() intertwiners

Kernel check (`decide +kernel`) of `interOK`; see `NPT.CP3.Chk.D2Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem inter_ok : interOK = true := by decide +kernel

theorem interShape_ok : interShapeOK = true := by decide +kernel

end NPT.CP3.Chk
