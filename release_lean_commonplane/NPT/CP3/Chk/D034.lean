import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D034 — variables 92..95

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0r34_ok : (List.range' 92 4).all d0OK = true := by decide +kernel

end NPT.CP3.Chk
