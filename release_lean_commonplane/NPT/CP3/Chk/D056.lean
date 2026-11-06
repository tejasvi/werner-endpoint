import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D056 — variables 123..123

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0r56_ok : (List.range' 123 1).all d0OK = true := by decide +kernel

end NPT.CP3.Chk
