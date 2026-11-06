import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D032 — span positions 144..191 of variable 91

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0s091_03_ok : (List.range' 144 48).all (spanOK1 91) = true := by decide +kernel

end NPT.CP3.Chk
