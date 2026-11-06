import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D028 — B_σ relations 5..5 of variable 91

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0b091_01_ok : (List.range' 5 1).all (bsigOK1 91) = true := by decide +kernel

end NPT.CP3.Chk
