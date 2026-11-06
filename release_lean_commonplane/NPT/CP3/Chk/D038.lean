import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D038 — B_σ relations 0..3 of variable 105

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0b105_00_ok : (List.range' 0 4).all (bsigOK1 105) = true := by decide +kernel

end NPT.CP3.Chk
