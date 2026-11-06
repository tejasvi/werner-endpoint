import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D076 — B_σ relations 10..14 of variable 147

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0b147_02_ok : (List.range' 10 5).all (bsigOK1 147) = true := by decide +kernel

end NPT.CP3.Chk
