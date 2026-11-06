import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D030 — span positions 48..95 of variable 91

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0s091_01_ok : (List.range' 48 48).all (spanOK1 91) = true := by decide +kernel

end NPT.CP3.Chk
