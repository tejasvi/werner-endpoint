import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D055 — variables 119..122

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0r55_ok : (List.range' 119 4).all d0OK = true := by decide +kernel

end NPT.CP3.Chk
