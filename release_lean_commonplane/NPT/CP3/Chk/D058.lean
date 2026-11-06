import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D058 — B_σ relations 0..4 of variable 124

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0b124_00_ok : (List.range' 0 5).all (bsigOK1 124) = true := by decide +kernel

end NPT.CP3.Chk
