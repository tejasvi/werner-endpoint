import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D017 — span positions 165..197 of variable 81

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0s081_05_ok : (List.range' 165 33).all (spanOK1 81) = true := by decide +kernel

end NPT.CP3.Chk
