import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D035 — variables 96..100

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0r35_ok : (List.range' 96 5).all d0OK = true := by decide +kernel

end NPT.CP3.Chk
