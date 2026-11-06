import NPT.CP3.Chk.D0Defs

/-!
# NPT.CP3.Chk.D069 — B_σ relations 0..16 of variable 146

Kernel check (`decide +kernel`) of the variable-block data; see `NPT.CP3.Chk.D0Defs`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

namespace NPT.CP3.Chk

theorem d0b146_00_ok : (List.range' 0 17).all (bsigOK1 146) = true := by decide +kernel

end NPT.CP3.Chk
