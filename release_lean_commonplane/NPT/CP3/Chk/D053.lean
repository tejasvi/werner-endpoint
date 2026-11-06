import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D053 — span positions 0..104 of variable 107

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0s107_00_ok : (List.range' 0 105).all (spanOK1 107) = true := by decide +kernel

end NPT.CP3.Chk
