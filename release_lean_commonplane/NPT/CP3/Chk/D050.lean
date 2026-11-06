import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D050 — span positions 208..230 of variable 106

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0s106_08_ok : (List.range' 208 23).all (spanOK1 106) = true := by decide +kernel

end NPT.CP3.Chk
