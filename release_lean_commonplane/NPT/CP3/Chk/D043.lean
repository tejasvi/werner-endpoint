import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D043 — span positions 26..51 of variable 106

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0s106_01_ok : (List.range' 26 26).all (spanOK1 106) = true := by decide +kernel

end NPT.CP3.Chk
