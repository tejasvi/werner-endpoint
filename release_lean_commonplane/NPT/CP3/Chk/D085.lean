import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D085 — span positions 198..230 of variable 147

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0s147_06_ok : (List.range' 198 33).all (spanOK1 147) = true := by decide +kernel

end NPT.CP3.Chk
