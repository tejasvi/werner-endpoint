import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D025 — variables 87..90

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0r25_ok : (List.range' 87 4).all d0OK = true := by decide +kernel

end NPT.CP3.Chk
