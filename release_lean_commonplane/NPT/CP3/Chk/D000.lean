import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D000 — variables 0..79

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0r00_ok : (List.range' 0 80).all d0OK = true := by decide +kernel

end NPT.CP3.Chk
