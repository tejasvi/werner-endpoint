import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D062 — span positions 96..143 of variable 124

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0s124_02_ok : (List.range' 96 48).all (spanOK1 124) = true := by decide +kernel

end NPT.CP3.Chk
